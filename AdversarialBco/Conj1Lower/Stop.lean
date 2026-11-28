/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Conj1Lower.Main
public import AdversarialBco.Conj1Lower.StopNoise
public import AdversarialBco.Conj1Lower.BalanceK

@[expose] public section

/-!
# Proposition STOP: the stopped game

The paper's stopped balance, on the Gaussian game of Top.lean at the strategy `ruleS d P` with `P` good
for a body inside `B(0, R0)`. The analysis stops at the first round where the posterior is dead or the observed
cumulative `C_u = Σ_{i < u} (o_i - b)` exceeds the threshold `x`; the game itself runs its `n` rounds.

This file holds the two facts of the analysis that hold for any measurable rule, weighted by a decreasing family of
measurable sets of histories that the later rounds do not change:

* (F2) `stopped_ledger`: the payments of the announced cells sum to at most the ledger's budget.
* (F3) `stopped_count`: the information of the rounds, on which the posterior is live, is at least `N*` times the
  probability of leaving the family through a dead posterior.
-/

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal NNReal

namespace AdversarialBco.Lower.Stop

open RealRAM Bayes _root_.AdversarialBco.Lower.Top

/-! ## The stopped live events -/

section Events

variable {d : ℕ} {R0 : ℝ} {Ω : Type} [MeasurableSpace Ω]

/-- The dent of round `t` at the tip: `D_t = s_t(x_t; x°) - b`. -/
noncomputable def dentT (P : SParams) (pol : Learner Ω d) (t : ℕ) (s : Sample d Ω) : ℝ :=
  (ruleS d P).sig (postT P pol t s) (playT P pol t s) s.1 - P.b

omit [MeasurableSpace Ω] in
theorem regG_eq (P : SParams) (pol : Learner Ω d) (n : ℕ) (s : Sample d Ω) :
    regG (prior d (1 / 2)) P pol n s = ∑ t ∈ range n, dentT P pol t s := rfl

end Events

/-! ## The stopped ledger for any rule (on variables, instantiated below) -/

section Generic

variable {d : ℕ} {Ω : Type} [MeasurableSpace Ω]

/-- The ledger potential after `t` rounds, weighted by a set of histories. -/
noncomputable def lamW (π0 : Measure (E d)) (R : Rule d (Option Cell)) (sc w : ℝ) (S : Set (Hist d (Option Cell)))
    (t : ℕ) (h : Hist d (Option Cell)) : ℝ≥0∞ :=
  S.indicator (fun h' => ENNReal.ofReal (lam w (post π0 R sc t h') - d * Real.log (w ^ 2) / 2)) h

/-- The payment of the cell announced at round `t` against the play `g`, weighted by a set of histories. -/
noncomputable def payW (π0 : Measure (E d)) (R : Rule d (Option Cell)) (sc w : ℝ) (S : Set (Hist d (Option Cell)))
    (t : ℕ) (g : Hist d (Option Cell) → E d) (h : Hist d (Option Cell)) : ℝ :=
  S.indicator (fun h' => payAnn w (post π0 R sc t h') (R.ans (post π0 R sc t h') (g h'))) h

theorem payW_nonneg (π0 : Measure (E d)) [IsProbabilityMeasure π0] (R : Rule d (Option Cell)) (hR : R.Meas π0)
    (sc : ℝ) {w : ℝ} (hw : w ≠ 0) {r : ℝ} (hball : ∀ᵐ θ ∂π0, θ ∈ Metric.closedBall (0 : E d) r)
    (S : Set (Hist d (Option Cell))) (t : ℕ) (g : Hist d (Option Cell) → E d) (h : Hist d (Option Cell)) :
    0 ≤ payW π0 R sc w S t g h := by
  unfold payW
  by_cases hs : h ∈ S
  · rw [Set.indicator_of_mem hs]
    have := isProbabilityMeasure_post π0 R hR sc t h
    have h2 := integrable_sq_norm_of_ae_mem _ (post_ae_mem _ R sc t h hball)
    exact Finset.sum_nonneg fun c _ => cellPay_nonneg _ h2 hw _
  · rw [Set.indicator_of_notMem hs]

theorem measurable_lamW (π0 : Measure (E d)) [IsProbabilityMeasure π0] (R : Rule d (Option Cell))
    (hR : R.Meas π0) (sc w : ℝ) {S : Set (Hist d (Option Cell))} (hS : MeasurableSet S) (t : ℕ) :
    Measurable (lamW π0 R sc w S t) := by
  have hdp := dens_props π0 R hR sc t
  exact (ENNReal.measurable_ofReal.comp ((measurable_lam_dens π0 hdp.1 hdp.2.1 w).sub_const _)).indicator hS

/-- The weighted payment is measurable in the history and the seed. -/
theorem measurable_payW (π0 : Measure (E d)) [IsProbabilityMeasure π0] (R : Rule d (Option Cell))
    (hR : R.Meas π0) (sc w : ℝ) {S : Set (Hist d (Option Cell))} (hS : MeasurableSet S) {pol : Learner Ω d} {t : ℕ}
    (hpol : Measurable fun p : Ω × (Fin t → E d) × (Fin t → ℝ) => pol t p.1 p.2.1 p.2.2) :
    Measurable (fun p : Hist d (Option Cell) × Ω => payW π0 R sc w S t (play pol t p.2) p.1) := by
  have hpl := measurable_play (α := Option Cell) hpol
  have h2 : Measurable (fun p : Hist d (Option Cell) × Ω => (p.1, play pol t p.2 p.1)) :=
    measurable_fst.prodMk (hpl.comp measurable_swap)
  have h3 := (measurable_payAnn π0 R hR sc t w).comp h2
  have h4 := h3.indicator (hS.preimage measurable_fst)
  have e : (fun p : Hist d (Option Cell) × Ω => payW π0 R sc w S t (play pol t p.2) p.1) =
      (Prod.fst ⁻¹' S).indicator
        ((fun p : Hist d (Option Cell) × E d => payAnn w (post π0 R sc t p.1) (R.ans (post π0 R sc t p.1) p.2)) ∘
          fun p : Hist d (Option Cell) × Ω => (p.1, play pol t p.2 p.1)) := by
    funext p
    unfold payW
    by_cases hp : p.1 ∈ S
    · rw [Set.indicator_of_mem hp, Set.indicator_of_mem (show p ∈ Prod.fst ⁻¹' S from hp)]
      rfl
    · rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem (show p ∉ Prod.fst ⁻¹' S from hp)]
  rw [e]
  exact h4

/-- One round of the ledger at a history, weighted by a set of histories that the round does not change (Lemma LEAK
(L2) and the Bayes update of the round), for any measurable rule. -/
theorem ledger_point_gen (π0 : Measure (E d)) [IsProbabilityMeasure π0] (R : Rule d (Option Cell)) (hR : R.Meas π0)
    {sc : ℝ} (hsc : sc ≠ 0) {w : ℝ} (hw : w ≠ 0) {r : ℝ}
    (hball : ∀ᵐ θ ∂π0, θ ∈ Metric.closedBall (0 : E d) r) (t : ℕ) (S : Set (Hist d (Option Cell)))
    (hS : ∀ (h : Hist d (Option Cell)) (y : E d) (o : ℝ) (a : Option Cell), Hist.push h t y o a ∈ S ↔ h ∈ S)
    (g : Hist d (Option Cell) → E d) (h : Hist d (Option Cell)) :
    ∫⁻ θ, ∫⁻ z, lamW π0 R sc w S (t + 1)
        (Hist.push h t (g h) (R.sig (post π0 R sc t h) (g h) θ + sc * z) (R.ans (post π0 R sc t h) (g h) θ))
        ∂gaussianReal 0 1 ∂post π0 R sc t h + ENNReal.ofReal (payW π0 R sc w S t g h) ≤
    lamW π0 R sc w S t h := by
  unfold lamW payW
  by_cases hs : h ∈ S
  · have hin : ∀ (y' : E d) (o : ℝ) (a : Option Cell),
        S.indicator (fun h' => ENNReal.ofReal (lam w (post π0 R sc (t + 1) h') - d * Real.log (w ^ 2) / 2))
          (Hist.push h t y' o a) =
          ENNReal.ofReal (lam w (bayesUpd (post π0 R sc t h)
            (lik (R.ans (post π0 R sc t h) y') (R.sig (post π0 R sc t h) y') (noiseVar sc) a o)) -
            d * Real.log (w ^ 2) / 2) := fun y' o a => by
      rw [Set.indicator_of_mem ((hS h y' o a).2 hs), post_succ_push _ _ hR]
    simp only [hin, Set.indicator_of_mem hs]
    have := isProbabilityMeasure_post π0 R hR sc t h
    have hrp := measurable_rule_post π0 R hR sc t
    have hm : Measurable (fun θ : E d => (h, g h, θ)) := by fun_prop
    have hc0 := hrp.1.comp hm
    have hs0 := hrp.2.comp hm
    have hc : Measurable (R.ans (post π0 R sc t h) (g h)) := hc0
    have hs1 : Measurable (R.sig (post π0 R sc t h) (g h)) := hs0
    exact ledger_round_ann (post π0 R sc t h) (post_ae_mem _ R sc t h hball) hc hs1 hsc hw
  · have hin : ∀ (y' : E d) (o : ℝ) (a : Option Cell),
        S.indicator (fun h' => ENNReal.ofReal (lam w (post π0 R sc (t + 1) h') - d * Real.log (w ^ 2) / 2))
          (Hist.push h t y' o a) = 0 :=
      fun y' o a => Set.indicator_of_notMem (mt (hS h y' o a).1 hs) _
    simp only [hin, Set.indicator_of_notMem hs, lintegral_zero, zero_add, ENNReal.ofReal_zero, le_refl]

/-- One round of the stopped ledger in expectation over the game. -/
theorem ledger_step_gen (π0 : Measure (E d)) [IsProbabilityMeasure π0] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (R : Rule d (Option Cell)) (hR : R.Meas π0) {sc : ℝ} (hsc : sc ≠ 0) {pol : Learner Ω d} {n : ℕ}
    (hpol : ∀ t < n, Measurable fun p : Ω × (Fin t → E d) × (Fin t → ℝ) => pol t p.1 p.2.1 p.2.2) {w : ℝ}
    (hw : w ≠ 0) {r : ℝ} (hball : ∀ᵐ θ ∂π0, θ ∈ Metric.closedBall (0 : E d) r) {t : ℕ} (ht : t < n)
    {S S' : Set (Hist d (Option Cell))} (hSm : MeasurableSet S)
    (hSpush : ∀ (h : Hist d (Option Cell)) (y : E d) (o : ℝ) (a : Option Cell), Hist.push h t y o a ∈ S ↔ h ∈ S)
    (hSanti : ∀ s : Sample d Ω, hist π0 R sc pol (t + 1) s ∈ S' → hist π0 R sc pol (t + 1) s ∈ S) :
    ∫⁻ s, lamW π0 R sc w S' (t + 1) (hist π0 R sc pol (t + 1) s) ∂gameLaw π0 μ +
      ∫⁻ s, ENNReal.ofReal (payW π0 R sc w S t (play pol t s.2.2) (hist π0 R sc pol t s)) ∂gameLaw π0 μ ≤
    ∫⁻ s, lamW π0 R sc w S t (hist π0 R sc pol t s) ∂gameLaw π0 μ := by
  have hΨ : Measurable (fun q : E d × Hist d (Option Cell) × Ω => lamW π0 R sc w S (t + 1) q.2.1) :=
    (measurable_lamW π0 R hR sc w hSm (t + 1)).comp (measurable_fst.comp measurable_snd)
  have hexp := hist_succ_expand π0 μ R hR hsc hpol ht hΨ
  have h1 : ∫⁻ s, lamW π0 R sc w S' (t + 1) (hist π0 R sc pol (t + 1) s) ∂gameLaw π0 μ ≤
      ∫⁻ s, lamW π0 R sc w S (t + 1) (hist π0 R sc pol (t + 1) s) ∂gameLaw π0 μ :=
    lintegral_mono fun s => by
      unfold lamW
      by_cases hs : hist π0 R sc pol (t + 1) s ∈ S'
      · rw [Set.indicator_of_mem hs, Set.indicator_of_mem (hSanti s hs)]
      · rw [Set.indicator_of_notMem hs]
        exact zero_le
  have hpm : Measurable (fun s : Sample d Ω =>
      ENNReal.ofReal (payW π0 R sc w S t (play pol t s.2.2) (hist π0 R sc pol t s))) := by
    have hq : Measurable (fun s : Sample d Ω => (hist π0 R sc pol t s, s.2.2)) :=
      (measurable_hist π0 R hR sc hpol ht.le).prodMk (measurable_snd.comp measurable_snd)
    have h2 := (measurable_payW π0 R hR sc w hSm (hpol t ht)).comp hq
    exact h2.ennreal_ofReal
  refine (add_le_add_left h1 _).trans ?_
  rw [hexp, ← lintegral_add_right _ hpm]
  exact lintegral_mono fun s => ledger_point_gen π0 R hR hsc hw hball t S hSpush (play pol t s.2.2)
    (hist π0 R sc pol t s)

/-- The weighted ledger at the prior is at most the ledger's budget. -/
theorem lamW_zero_le (hd : 0 < d) {r₀ : ℝ} (hr : 0 < r₀) (R : Rule d (Option Cell)) (sc : ℝ) {w : ℝ} (hw : w ≠ 0)
    (S : Set (Hist d (Option Cell))) (h : Hist d (Option Cell)) :
    lamW (prior d r₀) R sc w S 0 h ≤ ENNReal.ofReal (ledgerBudget d r₀ w) := by
  have hpost0 : post (prior d r₀) R sc 0 h = prior d r₀ := by simp [Bayes.post, Bayes.dens]
  unfold lamW
  refine (Set.indicator_le_self _ _ _).trans ?_
  simp only [hpost0]
  refine ENNReal.ofReal_le_ofReal ?_
  have hl := lam_prior_le hd hr hw
  have hw2 : 0 < w ^ 2 := by positivity
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hlog : Real.log (r₀ ^ 2 / d + w ^ 2) - Real.log (w ^ 2) = Real.log (1 + r₀ ^ 2 / (d * w ^ 2)) := by
    rw [← Real.log_div (by positivity) hw2.ne']
    congr 1
    field_simp
    ring
  unfold ledgerBudget
  nlinarith [hlog]

theorem ledgerBudget_nonneg (d : ℕ) (r₀ w : ℝ) : 0 ≤ ledgerBudget d r₀ w := by
  unfold ledgerBudget
  have : 1 ≤ 1 + r₀ ^ 2 / (d * w ^ 2) := le_add_of_nonneg_right (by positivity)
  exact mul_nonneg (by positivity) (Real.log_nonneg this)

/-- (F2) for any measurable rule: the payments of the announced cells, weighted by a decreasing family of measurable
sets of histories that the later rounds do not change, sum to at most the ledger's budget. -/
theorem stopped_ledger (hd : 0 < d) {r₀ : ℝ} (hr : 0 < r₀) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (R : Rule d (Option Cell)) (hR : R.Meas (prior d r₀)) {sc : ℝ} (hsc : sc ≠ 0) {pol : Learner Ω d} {n : ℕ}
    (hpol : ∀ t < n, Measurable fun p : Ω × (Fin t → E d) × (Fin t → ℝ) => pol t p.1 p.2.1 p.2.2) {w : ℝ}
    (hw : w ≠ 0) (S : ℕ → Set (Hist d (Option Cell))) (hSm : ∀ t, MeasurableSet (S t))
    (hSpush : ∀ t (h : Hist d (Option Cell)) (y : E d) (o : ℝ) (a : Option Cell), Hist.push h t y o a ∈ S t ↔ h ∈ S t)
    (hSanti : ∀ t (s : Sample d Ω), hist (prior d r₀) R sc pol (t + 1) s ∈ S (t + 1) →
      hist (prior d r₀) R sc pol (t + 1) s ∈ S t) :
    ∑ t ∈ range n, ∫ s, payW (prior d r₀) R sc w (S t) t (play pol t s.2.2) (hist (prior d r₀) R sc pol t s)
        ∂gameLaw (prior d r₀) μ ≤ ledgerBudget d r₀ w := by
  have hπ := isProbabilityMeasure_prior d hr
  have hG := isProbabilityMeasure_gameLaw (prior d r₀) μ
  have hball := prior_ae_mem d r₀
  have hpm : ∀ t < n, Measurable (fun s : Sample d Ω =>
      payW (prior d r₀) R sc w (S t) t (play pol t s.2.2) (hist (prior d r₀) R sc pol t s)) := fun t ht => by
    have hq : Measurable (fun s : Sample d Ω => (hist (prior d r₀) R sc pol t s, s.2.2)) :=
      (measurable_hist (prior d r₀) R hR sc hpol ht.le).prodMk (measurable_snd.comp measurable_snd)
    have h2 := (measurable_payW (prior d r₀) R hR sc w (hSm t) (hpol t ht)).comp hq
    exact h2
  have htel := telescope_lintegral (gameLaw (prior d r₀) μ)
    (fun t s => lamW (prior d r₀) R sc w (S t) t (hist (prior d r₀) R sc pol t s))
    (fun t s => ENNReal.ofReal (payW (prior d r₀) R sc w (S t) t (play pol t s.2.2) (hist (prior d r₀) R sc pol t s)))
    n (fun t ht => ledger_step_gen (prior d r₀) μ R hR hsc hpol hw hball ht (hSm t) (hSpush t) (hSanti t))
  have hF0 : ∫⁻ s, lamW (prior d r₀) R sc w (S 0) 0 (hist (prior d r₀) R sc pol 0 s) ∂gameLaw (prior d r₀) μ ≤
      ENNReal.ofReal (ledgerBudget d r₀ w) := by
    refine (lintegral_mono fun s => lamW_zero_le hd hr R sc hw (S 0) _).trans ?_
    simp only [lintegral_const, measure_univ, mul_one, le_refl]
  have hsum_le : ∑ t ∈ range n, ∫⁻ s, ENNReal.ofReal (payW (prior d r₀) R sc w (S t) t (play pol t s.2.2)
      (hist (prior d r₀) R sc pol t s)) ∂gameLaw (prior d r₀) μ ≤ ENNReal.ofReal (ledgerBudget d r₀ w) :=
    le_trans (le_trans le_self_add htel) hF0
  have hfin : ∀ t ∈ range n, ∫⁻ s, ENNReal.ofReal (payW (prior d r₀) R sc w (S t) t (play pol t s.2.2)
      (hist (prior d r₀) R sc pol t s)) ∂gameLaw (prior d r₀) μ ≠ ∞ := fun t ht =>
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (le_trans (Finset.single_le_sum (f := fun t => ∫⁻ s, ENNReal.ofReal (payW (prior d r₀) R sc w (S t) t
        (play pol t s.2.2) (hist (prior d r₀) R sc pol t s)) ∂gameLaw (prior d r₀) μ) (fun _ _ => zero_le) ht) hsum_le)
  have he : ∀ t ∈ range n, ∫ s, payW (prior d r₀) R sc w (S t) t (play pol t s.2.2) (hist (prior d r₀) R sc pol t s)
      ∂gameLaw (prior d r₀) μ = (∫⁻ s, ENNReal.ofReal (payW (prior d r₀) R sc w (S t) t (play pol t s.2.2)
        (hist (prior d r₀) R sc pol t s)) ∂gameLaw (prior d r₀) μ).toReal := fun t ht =>
    integral_eq_lintegral_of_nonneg_ae
      (ae_of_all _ fun s => payW_nonneg (prior d r₀) R hR sc hw hball (S t) t _ _)
      (hpm t (mem_range.1 ht)).aestronglyMeasurable
  rw [Finset.sum_congr rfl he, ← ENNReal.toReal_sum hfin]
  calc _ ≤ (ENNReal.ofReal (ledgerBudget d r₀ w)).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hsum_le
    _ = ledgerBudget d r₀ w := ENNReal.toReal_ofReal (ledgerBudget_nonneg d r₀ w)

/-- Summation of `b (t + 1) + c t ≤ b t + j t` over the rounds, in `ℝ≥0∞`. -/
theorem telescope_up (b c j : ℕ → ℝ≥0∞) (n : ℕ) (h : ∀ t < n, b (t + 1) + c t ≤ b t + j t) :
    ∑ t ∈ range n, c t + b n ≤ b 0 + ∑ t ∈ range n, j t := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, sum_range_succ]
    have h1 := ih fun t ht => h t (by omega)
    have h2 := h n (by omega)
    calc ∑ t ∈ range n, c t + c n + b (n + 1) = ∑ t ∈ range n, c t + (b (n + 1) + c n) := by ring
      _ ≤ ∑ t ∈ range n, c t + (b n + j n) := add_le_add le_rfl h2
      _ = (∑ t ∈ range n, c t + b n) + j n := by ring
      _ ≤ (b 0 + ∑ t ∈ range n, j t) + j n := add_le_add h1 le_rfl
      _ = b 0 + (∑ t ∈ range n, j t + j n) := by ring

/-- The divergence from the prior after `t` rounds, weighted by a set of histories. -/
noncomputable def klW (π0 : Measure (E d)) (R : Rule d (Option Cell)) (sc : ℝ) (S : Set (Hist d (Option Cell)))
    (t : ℕ) (h : Hist d (Option Cell)) : ℝ≥0∞ :=
  S.indicator (fun h' => ENNReal.ofReal (klDens π0 (dens π0 R sc t h'))) h

/-- The information of round `t` against the play `g`, weighted by a set of histories. -/
noncomputable def infoW (π0 : Measure (E d)) (R : Rule d (Option Cell)) (sc : ℝ) (S : Set (Hist d (Option Cell)))
    (t : ℕ) (g : Hist d (Option Cell) → E d) (h : Hist d (Option Cell)) : ℝ :=
  S.indicator (fun h' => infoJ (post π0 R sc t h') (R.ans (post π0 R sc t h') (g h'))
    (R.sig (post π0 R sc t h') (g h')) sc) h

theorem measurable_klW (π0 : Measure (E d)) [IsProbabilityMeasure π0] (R : Rule d (Option Cell))
    (hR : R.Meas π0) (sc : ℝ) {S : Set (Hist d (Option Cell))} (hS : MeasurableSet S) (t : ℕ) :
    Measurable (klW π0 R sc S t) := by
  have h1 := (measurable_klDens_dens π0 (measurable_dens π0 R hR sc t)).ennreal_ofReal
  exact h1.indicator hS

theorem klW_zero (π0 : Measure (E d)) (R : Rule d (Option Cell)) (sc : ℝ) (S : Set (Hist d (Option Cell)))
    (h : Hist d (Option Cell)) : klW π0 R sc S 0 h = 0 := by
  have h0 : ∀ h' : Hist d (Option Cell), klDens π0 (dens π0 R sc 0 h') = 0 := fun _ => klDens_one π0
  unfold klW
  by_cases hs : h ∈ S <;> simp [hs, h0]

omit [MeasurableSpace Ω] in
/-- The weighted information along the game is the information of the round on the preimage event. -/
theorem infoW_hist (π0 : Measure (E d)) (R : Rule d (Option Cell)) (sc : ℝ) (S : Set (Hist d (Option Cell)))
    (pol : Learner Ω d) (t : ℕ) (s : Sample d Ω) :
    infoW π0 R sc S t (play pol t s.2.2) (hist π0 R sc pol t s) =
      (hist π0 R sc pol t ⁻¹' S).indicator (infoRound π0 R sc pol t) s := by
  unfold infoW
  by_cases hs : hist π0 R sc pol t s ∈ S
  · rw [Set.indicator_of_mem hs, Set.indicator_of_mem (show s ∈ hist π0 R sc pol t ⁻¹' S from hs)]
    rfl
  · rw [Set.indicator_of_notMem hs, Set.indicator_of_notMem (show s ∉ hist π0 R sc pol t ⁻¹' S from hs)]

/-- (S2) at one history: the mean divergence after the round is the divergence before it plus the information. -/
theorem kl_point_gen (π0 : Measure (E d)) [IsProbabilityMeasure π0] (R : Rule d (Option Cell)) (hR : R.Meas π0)
    {sc : ℝ} (hsc : sc ≠ 0) (t : ℕ) (g : Hist d (Option Cell) → E d) (h : Hist d (Option Cell)) {S₀ : ℝ}
    (hb : ∀ θ, |R.sig (post π0 R sc t h) (g h) θ| ≤ S₀) :
    ∫⁻ θ, ∫⁻ z, ENNReal.ofReal (klDens π0 (dens π0 R sc (t + 1)
        (Hist.push h t (g h) (R.sig (post π0 R sc t h) (g h) θ + sc * z) (R.ans (post π0 R sc t h) (g h) θ))))
        ∂gaussianReal 0 1 ∂post π0 R sc t h =
      ENNReal.ofReal (klDens π0 (dens π0 R sc t h)) +
        ENNReal.ofReal (infoJ (post π0 R sc t h) (R.ans (post π0 R sc t h) (g h)) (R.sig (post π0 R sc t h) (g h)) sc) := by
  simp only [dens_succ_push]
  have hP : IsProbabilityMeasure (post π0 R sc t h) := isProbabilityMeasure_post π0 R hR sc t h
  obtain ⟨C, hC, hρC⟩ := dens_le_bound π0 R sc t h
  have hρ : Measurable (dens π0 R sc t h) := by
    have h' := (measurable_dens π0 R hR sc t).comp (measurable_prodMk_left (x := h))
    exact h'
  have h1 := (dens_props π0 R hR sc t).2.2 h
  have hmr := measurable_rule_post π0 R hR sc t
  have hg : Measurable (fun θ : E d => (h, g h, θ)) :=
    measurable_const.prodMk (measurable_const.prodMk measurable_id)
  have hc : Measurable (R.ans (post π0 R sc t h) (g h)) := by
    have h' := hmr.1.comp hg
    exact h'
  have hs : Measurable (R.sig (post π0 R sc t h) (g h)) := by
    have h' := hmr.2.comp hg
    exact h'
  have hJ0 := infoJ_nonneg (post π0 R sc t h) hc hs hb hsc
  obtain ⟨hI, hE⟩ := kl_round π0 hρ hC hρC h1 hc hs hb hsc
  have hlik := measurable_lik hc hs (noiseVar sc)
  have hK0 : ∀ p : E d × ℝ, 0 ≤ klDens π0 (updDens π0 (dens π0 R sc t h)
      (lik (R.ans (post π0 R sc t h) (g h)) (R.sig (post π0 R sc t h) (g h))
        (noiseVar sc) (R.ans (post π0 R sc t h) (g h) p.1)
        (R.sig (post π0 R sc t h) (g h) p.1 + sc * p.2))) := by
    intro p
    have hL : Measurable (lik (R.ans (post π0 R sc t h) (g h))
        (R.sig (post π0 R sc t h) (g h)) (noiseVar sc) (R.ans (post π0 R sc t h) (g h) p.1)
        (R.sig (post π0 R sc t h) (g h) p.1 + sc * p.2)) := by
      have h' := hlik.comp (measurable_prodMk_left (x := (R.ans (post π0 R sc t h) (g h) p.1,
        R.sig (post π0 R sc t h) (g h) p.1 + sc * p.2)))
      exact h'
    exact klDens_nonneg π0 (measurable_updDens π0 hρ hL) (lintegral_updDens π0 hρ hL h1)
  have hKρ : 0 ≤ klDens π0 (dens π0 R sc t h) := klDens_nonneg π0 hρ h1
  refine (lintegral_ofReal_prod (μ := post π0 R sc t h) (ν := gaussianReal 0 1) hI hK0).trans ?_
  rw [← ENNReal.ofReal_add hKρ hJ0]
  exact congrArg ENNReal.ofReal hE

/-- (S2) at one history, weighted by a set of histories that the round does not change. -/
theorem klW_point_gen (π0 : Measure (E d)) [IsProbabilityMeasure π0] (R : Rule d (Option Cell)) (hR : R.Meas π0)
    {sc : ℝ} (hsc : sc ≠ 0) (t : ℕ) (S : Set (Hist d (Option Cell)))
    (hS : ∀ (h : Hist d (Option Cell)) (y : E d) (o : ℝ) (a : Option Cell), Hist.push h t y o a ∈ S ↔ h ∈ S)
    (g : Hist d (Option Cell) → E d) (h : Hist d (Option Cell)) {S₀ : ℝ}
    (hb : ∀ θ, |R.sig (post π0 R sc t h) (g h) θ| ≤ S₀) :
    ∫⁻ θ, ∫⁻ z, klW π0 R sc S (t + 1)
        (Hist.push h t (g h) (R.sig (post π0 R sc t h) (g h) θ + sc * z) (R.ans (post π0 R sc t h) (g h) θ))
        ∂gaussianReal 0 1 ∂post π0 R sc t h =
      klW π0 R sc S t h + ENNReal.ofReal (infoW π0 R sc S t g h) := by
  unfold klW infoW
  by_cases hs : h ∈ S
  · have hin : ∀ (y' : E d) (o : ℝ) (a : Option Cell),
        S.indicator (fun h' => ENNReal.ofReal (klDens π0 (dens π0 R sc (t + 1) h'))) (Hist.push h t y' o a) =
          ENNReal.ofReal (klDens π0 (dens π0 R sc (t + 1) (Hist.push h t y' o a))) := fun y' o a =>
      Set.indicator_of_mem ((hS h y' o a).2 hs) _
    simp only [hin, Set.indicator_of_mem hs]
    exact kl_point_gen π0 R hR hsc t g h hb
  · have hin : ∀ (y' : E d) (o : ℝ) (a : Option Cell),
        S.indicator (fun h' => ENNReal.ofReal (klDens π0 (dens π0 R sc (t + 1) h'))) (Hist.push h t y' o a) = 0 :=
      fun y' o a => Set.indicator_of_notMem (mt (hS h y' o a).1 hs) _
    simp only [hin, Set.indicator_of_notMem hs, lintegral_zero, zero_add, ENNReal.ofReal_zero]

/-- (S2) over one round of the game, weighted by a set of histories that the round does not change. -/
theorem klW_step_gen (π0 : Measure (E d)) [IsProbabilityMeasure π0] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (R : Rule d (Option Cell)) (hR : R.Meas π0) {sc : ℝ} (hsc : sc ≠ 0) {pol : Learner Ω d} {n : ℕ}
    (hpol : ∀ t < n, Measurable fun p : Ω × (Fin t → E d) × (Fin t → ℝ) => pol t p.1 p.2.1 p.2.2) {S₀ : ℝ}
    (hsb : ∀ t < n, ∀ h θ ω, |R.sig (post π0 R sc t h) (play pol t ω h) θ| ≤ S₀) {t : ℕ} (ht : t < n)
    {S : Set (Hist d (Option Cell))} (hSm : MeasurableSet S)
    (hSpush : ∀ (h : Hist d (Option Cell)) (y : E d) (o : ℝ) (a : Option Cell), Hist.push h t y o a ∈ S ↔ h ∈ S) :
    ∫⁻ s, klW π0 R sc S (t + 1) (hist π0 R sc pol (t + 1) s) ∂gameLaw π0 μ =
      ∫⁻ s, klW π0 R sc S t (hist π0 R sc pol t s) ∂gameLaw π0 μ +
        ∫⁻ s, ENNReal.ofReal (infoW π0 R sc S t (play pol t s.2.2) (hist π0 R sc pol t s)) ∂gameLaw π0 μ := by
  have hΨ : Measurable (fun q : E d × Hist d (Option Cell) × Ω => klW π0 R sc S (t + 1) q.2.1) :=
    (measurable_klW π0 R hR sc hSm (t + 1)).comp (measurable_fst.comp measurable_snd)
  have hexp := hist_succ_expand π0 μ R hR hsc hpol ht hΨ
  have hKt : Measurable (fun s : Sample d Ω => klW π0 R sc S t (hist π0 R sc pol t s)) := by
    have h' := (measurable_klW π0 R hR sc hSm t).comp (measurable_hist π0 R hR sc hpol ht.le)
    exact h'
  rw [hexp, ← lintegral_add_left hKt]
  exact lintegral_congr fun s => klW_point_gen π0 R hR hsc t S hSpush (play pol t s.2.2) (hist π0 R sc pol t s)
    (fun θ => hsb t ht _ θ s.2.2)

/-- (F3) for any measurable rule: the information of the rounds on a decreasing family of sets of histories that
the later rounds do not change, and on which the posterior is live, is at least `N*` times the probability of
leaving the family through a dead posterior (Lemma CHAIN with the weight, a summation by parts, Lemma COUNT (b)). -/
theorem stopped_count {d : ℕ} (hd : 1 ≤ d) (μ : Measure Ω) [IsProbabilityMeasure μ] (R : Rule d (Option Cell))
    (hR : R.Meas (prior d (1 / 2))) {sc : ℝ} (hsc : sc ≠ 0) {pol : Learner Ω d} {n : ℕ}
    (hpol : ∀ t < n, Measurable fun p : Ω × (Fin t → E d) × (Fin t → ℝ) => pol t p.1 p.2.1 p.2.2) {S₀ : ℝ}
    (hsb : ∀ t < n, ∀ h θ ω, |R.sig (post (prior d (1 / 2)) R sc t h) (play pol t ω h) θ| ≤ S₀) {w : ℝ}
    (hw : 0 < w) (hX : Real.exp 1 / 2 ≤ xCount d w) (S : ℕ → Set (Hist d (Option Cell)))
    (hSm : ∀ t, MeasurableSet (S t))
    (hSpush : ∀ t (h : Hist d (Option Cell)) (y : E d) (o : ℝ) (a : Option Cell), Hist.push h t y o a ∈ S t ↔ h ∈ S t)
    (hSanti : ∀ t (s : Sample d Ω), hist (prior d (1 / 2)) R sc pol (t + 1) s ∈ S (t + 1) →
      hist (prior d (1 / 2)) R sc pol (t + 1) s ∈ S t)
    (hSlive : ∀ t (s : Sample d Ω), hist (prior d (1 / 2)) R sc pol (t + 1) s ∈ S (t + 1) →
      (d : ℝ) / 2 ≤ dLive w (covM (post (prior d (1 / 2)) R sc (t + 1) (hist (prior d (1 / 2)) R sc pol (t + 1) s)))) :
    nStar d w * ∑ t ∈ range n, (gameLaw (prior d (1 / 2)) μ).real
        {s | hist (prior d (1 / 2)) R sc pol (t + 1) s ∈ S t ∧
          dLive w (covM (post (prior d (1 / 2)) R sc (t + 1) (hist (prior d (1 / 2)) R sc pol (t + 1) s))) < d / 2} ≤
      ∑ t ∈ range n, ∫ s, infoW (prior d (1 / 2)) R sc (S t) t (play pol t s.2.2)
        (hist (prior d (1 / 2)) R sc pol t s) ∂gameLaw (prior d (1 / 2)) μ := by
  have hr : (0 : ℝ) < 1 / 2 := by norm_num
  have : IsProbabilityMeasure (prior d (1 / 2)) := isProbabilityMeasure_prior d hr
  have hG : IsProbabilityMeasure (gameLaw (prior d (1 / 2)) μ) := isProbabilityMeasure_gameLaw _ μ
  set π0 := prior d (1 / 2) with hπ0
  set G := gameLaw π0 μ with hGdef
  let E : ℕ → Set (Sample d Ω) := fun t => {s | hist π0 R sc pol (t + 1) s ∈ S t ∧
    dLive w (covM (post π0 R sc (t + 1) (hist π0 R sc pol (t + 1) s))) < d / 2}
  have hEm : ∀ t < n, MeasurableSet (E t) := fun t ht => by
    have hh := measurable_hist π0 R hR sc hpol (Nat.succ_le_of_lt ht)
    have hD := dens_props π0 R hR sc (t + 1)
    have hL : MeasurableSet {h : Hist d (Option Cell) | dLive w (covM (post π0 R sc (t + 1) h)) < d / 2} := by
      have h' := (measurable_dLive (d := d) w).comp (measurable_covM_dens π0 hD.1 hD.2.1)
      have h2 := measurableSet_lt h' (measurable_const (a := (d : ℝ) / 2))
      exact h2
    exact hh ((hSm t).inter hL)
  -- the information is integrable and nonnegative
  have hJi : ∀ t < n, Integrable (fun s => infoW π0 R sc (S t) t (play pol t s.2.2) (hist π0 R sc pol t s)) G :=
    fun t ht => by
      have he : (fun s => infoW π0 R sc (S t) t (play pol t s.2.2) (hist π0 R sc pol t s)) =
          (hist π0 R sc pol t ⁻¹' S t).indicator (infoRound π0 R sc pol t) :=
        funext fun s => infoW_hist π0 R sc (S t) pol t s
      rw [he]
      exact (integrable_infoRound π0 μ R hR hsc hpol hsb ht).indicator
        (measurable_hist π0 R hR sc hpol ht.le (hSm t))
  have hJ0 : ∀ t < n, ∀ s, 0 ≤ infoW π0 R sc (S t) t (play pol t s.2.2) (hist π0 R sc pol t s) := fun t ht s => by
    rw [infoW_hist]
    by_cases hs : s ∈ hist π0 R sc pol t ⁻¹' S t
    · rw [Set.indicator_of_mem hs]
      exact (infoRound_bounds π0 R hR hsc hsb ht s).1
    · rw [Set.indicator_of_notMem hs]
  -- the step of the summation by parts
  have hstep : ∀ t < n, ∫⁻ s, klW π0 R sc (S (t + 1)) (t + 1) (hist π0 R sc pol (t + 1) s) ∂G +
      ENNReal.ofReal (nStar d w) * G (E t) ≤ ∫⁻ s, klW π0 R sc (S t) t (hist π0 R sc pol t s) ∂G +
        ∫⁻ s, ENNReal.ofReal (infoW π0 R sc (S t) t (play pol t s.2.2) (hist π0 R sc pol t s)) ∂G := by
    intro t ht
    rw [← klW_step_gen π0 μ R hR hsc hpol hsb ht (hSm t) (hSpush t), ← lintegral_indicator_const (hEm t ht),
      ← lintegral_add_right _ ((measurable_const (a := ENNReal.ofReal (nStar d w))).indicator (hEm t ht))]
    refine lintegral_mono fun s => ?_
    unfold klW
    by_cases h1 : hist π0 R sc pol (t + 1) s ∈ S (t + 1)
    · have hnE : s ∉ E t := fun hE => by
        have := hSlive t s h1
        exact absurd hE.2 (not_lt.2 this)
      rw [Set.indicator_of_mem h1, Set.indicator_of_mem (hSanti t s h1), Set.indicator_of_notMem hnE, add_zero]
    · rw [Set.indicator_of_notMem h1, zero_add]
      by_cases hE : s ∈ E t
      · rw [Set.indicator_of_mem hE, Set.indicator_of_mem hE.1]
        obtain ⟨C, hC, hρC⟩ := dens_le_bound π0 R sc (t + 1) (hist π0 R sc pol (t + 1) s)
        have hρ : Measurable (dens π0 R sc (t + 1) (hist π0 R sc pol (t + 1) s)) := by
          have h' := (measurable_dens π0 R hR sc (t + 1)).comp
            (measurable_prodMk_left (x := hist π0 R sc pol (t + 1) s))
          exact h'
        exact ENNReal.ofReal_le_ofReal (count_b hd hw hX hρ hC hρC ((dens_props _ R hR sc (t + 1)).2.2 _) hE.2)
      · rw [Set.indicator_of_notMem hE]
        exact zero_le
  have htel := telescope_up (fun t => ∫⁻ s, klW π0 R sc (S t) t (hist π0 R sc pol t s) ∂G)
    (fun t => ENNReal.ofReal (nStar d w) * G (E t))
    (fun t => ∫⁻ s, ENNReal.ofReal (infoW π0 R sc (S t) t (play pol t s.2.2) (hist π0 R sc pol t s)) ∂G) n hstep
  simp only [klW_zero, lintegral_zero, zero_add] at htel
  have hsum := le_trans le_self_add htel
  have hj : ∀ t ∈ range n, ∫⁻ s, ENNReal.ofReal (infoW π0 R sc (S t) t (play pol t s.2.2)
      (hist π0 R sc pol t s)) ∂G = ENNReal.ofReal (∫ s, infoW π0 R sc (S t) t (play pol t s.2.2)
        (hist π0 R sc pol t s) ∂G) := fun t ht =>
    (ofReal_integral_eq_lintegral_ofReal (hJi t (mem_range.1 ht))
      (ae_of_all _ (hJ0 t (mem_range.1 ht)))).symm
  have hI0 : ∀ t ∈ range n, 0 ≤ ∫ s, infoW π0 R sc (S t) t (play pol t s.2.2) (hist π0 R sc pol t s) ∂G :=
    fun t ht => integral_nonneg (hJ0 t (mem_range.1 ht))
  rw [sum_congr rfl hj, ← ENNReal.ofReal_sum_of_nonneg hI0] at hsum
  by_cases hN : nStar d w ≤ 0
  · exact le_trans (mul_nonpos_of_nonpos_of_nonneg hN (sum_nonneg fun t _ => measureReal_nonneg))
      (sum_nonneg hI0)
  push Not at hN
  have hc : ∀ t ∈ range n, ENNReal.ofReal (nStar d w) * G (E t) = ENNReal.ofReal (nStar d w * G.real (E t)) :=
    fun t _ => by
      rw [ENNReal.ofReal_mul hN.le, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  rw [sum_congr rfl hc, ← ENNReal.ofReal_sum_of_nonneg fun t _ => mul_nonneg hN.le measureReal_nonneg,
    ENNReal.ofReal_le_ofReal_iff (sum_nonneg hI0)] at hsum
  rw [mul_sum]
  exact hsum

end Generic

end AdversarialBco.Lower.Stop
