/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Grow.Arith
public import AdversarialBco.StatementMatched
public import AdversarialBco.UnifiedLower.Prog

@[expose] public section

/-!
# Theorem GROW, Gaussian form (Route G): `TheoremGrowG` and `TheoremGrowGProg`

Route G on every body. For `d ≥ 4·10^6`, `ℓ = log (1/δ) ≥ 60` and `n ≥ d^6 ℓ`:

* `growG_prob`: the position of the body (`position_facts`) sends it between `B̄(0, 1/2)` and `B̄(0, posR d)`; Route G
  on the image (`growBody_mid` at the parameters `pG d n ℓ`, `routeG_pG`) gives a strategy whose regret is measurable,
  nonnegative and at least `(1 - η) M₀` with probability at least `q₀ e^{-(B + (2B)^{1/2})/q₀} > δ` (`qZero_ge`,
  `delta_lt`); its pull-back by the position (Lemma AFF) is in `StratsLowU K n r0` since `L_D posR d ≤ 1/8`
  (`lipG_le`), with the same regret, and `(1 - η) M₀` is at least the target (`target_le`);
* `theoremGrowG : TheoremGrowG`;
* `growGProg_of_growG : TheoremGrowG → TheoremGrowGProg`, as `progUDQ_of_lowerUDQ`: the learner of a program that
  meets `MachineOK` (Lemma BRIDGE, `progLearner_isLearner`) meets a strategy of `StratsLowU`, whose closed loop with the
  program (Lemma REAL, `clLoss`, `closedLoop_cl`, `noisyAdv_cl`) is an environment of `TheoremUnified` with the
  program's windows and the noise `0`, and the regrets agree coin sequence by coin sequence (`regretU_cl`);
* `theoremGrowGProg : TheoremGrowGProg`.
-/

open MeasureTheory ProbabilityTheory

namespace AdversarialBco.Grow

open RealRAM AdversarialBco.Lower AdversarialBco.Lower.Top AdversarialBco.UnifiedLower AdversarialBco.UnifiedLower.Body
  Minimax

/-- **Route G on every body.** -/
theorem growG_prob {d n : ℕ} (hd : 4000000 ≤ d) {K : Set (E d)} {a : E d} {r0 R0 : ℝ} (hb : BodyU K a r0 R0)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] {pol : Learner Ω d}
    (hpol : IsLearnerAd K n pol) {δ : ℝ} (hδ : 0 < δ) (hℓ : 60 ≤ Real.log (1 / δ))
    (hn : (d : ℝ) ^ 6 * Real.log (1 / δ) ≤ n) :
    ∃ p : ENNReal, ENNReal.ofReal δ < p ∧
      LowerProbNN K n r0 μ pol
        (8 / 10 ^ 6 * d * Real.sqrt (n * Real.log (1 / δ)) / (Real.log d * Real.sqrt (Real.log n))) p := by
  set ℓ := Real.log (1 / δ) with hℓdef
  obtain ⟨T, hKc, hK1, hK2, hT⟩ := position_facts hd hb
  obtain ⟨hR1, -⟩ := posR_bounds hd
  have hR := routeG_pG hd hℓ hn
  have hq := qZero_ge hd hℓ hn
  obtain ⟨σ', hσ', hm, hnn, hge⟩ :=
    growBody_mid hR hKc hK1 hK2 μ (isLearnerAd_push T hpol) (by linarith)
  have hr0 := hb.1
  have hLD0 : 0 ≤ (pG d n ℓ).g / (pG d n ℓ).k * (5 * Real.sqrt d) * frameC d := by
    have := (gG_pos hd hℓ hn).le
    have := kG_ge hd
    show 0 ≤ gG d n ℓ / kG d * (5 * Real.sqrt d) * (2 * Real.sqrt ((d : ℝ) + 2))
    positivity
  have hpull := pullStrat_mem_mid T (M := posR d / r0) hLD0 hT hσ'
  have hp0 : 0 < qZero d n (pG d n ℓ) (1 / 5) (ellB n) *
      Real.exp (-(bG ℓ + Real.sqrt (2 * bG ℓ)) / qZero d n (pG d n ℓ) (1 / 5) (ellB n)) := by
    have : 0 < qZero d n (pG d n ℓ) (1 / 5) (ellB n) := by linarith
    positivity
  refine ⟨_, (ENNReal.ofReal_lt_ofReal_iff hp0).2 (delta_lt hδ hℓ hq), pullStrat T σ',
    stratsMid_lowU hr0 ?_ hpull, ?_, fun ω => ?_, hge.trans (measure_mono fun ω hω => ?_)⟩
  · have hlip : gG d n ℓ / kG d * (5 * Real.sqrt d) * frameC d * posR d ≤ 1 / 8 := lipG_le hd hℓ hn
    change gG d n ℓ / kG d * (5 * Real.sqrt d) * frameC d * (posR d / r0) ≤ 1 / (4 * r0)
    rw [← mul_div_assoc, div_le_div_iff₀ hr0 (by positivity)]
    nlinarith
  · simpa only [regretAd_pushLearner] using hm
  · simpa only [regretAd_pushLearner] using hnn ω
  · simp only [Set.mem_ofPred_eq, regretAd_pushLearner] at hω ⊢
    exact (target_le hd hℓ hn).trans hω

/-- **Theorem GROW, Gaussian form** (`TheoremGrowG`). -/
theorem theoremGrowG : TheoremGrowG := by
  intro d _ n _ a r0 R0 K hb Ω _ μ _ pol hpol δ hδ hd hℓ hn
  exact growG_prob hd hb μ hpol hδ hℓ hn

open BitRAM BitRAMO Unified UnifiedLower UnifiedLower.Prog UnifiedLower.LowerSanity in
/-- `TheoremGrowGProg` from `TheoremGrowG`, as `TheoremLowerUDProgQ` from `TheoremLowerUDQ`
(`progUDQ_of_lowerUDQ`). -/
theorem growGProg_of_growG (hG : TheoremGrowG) : TheoremGrowGProg := by
  intro P d hd n hn δ r0 R0 hδ0 hδ1 hr0 hr0R a K hKc hKv hK1 hK2 orc _ B D D' hM δ' h0 h1 h2 h3
  have hs0 : (initU d n δ r0 R0 a).rounds = 0 := rfl
  have hb := bodyU_of_unified hr0 hr0R a hKc hKv hK1 hK2
  have hpol := progLearner_isLearner hKv hM hs0
  obtain ⟨p, hp, σ, hσ, hm, hnn, hge⟩ := hG d hd n hn (toE a) r0 R0 K hb (ℕ → Bool) _ coinStream inferInstance
    (progLearner P (initU d n δ r0 R0 a) orc) hpol δ' h0 h1 h2 h3
  refine ⟨p, hp, σ, clLoss P (initU d n δ r0 R0 a) orc σ, hσ, closedLoop_cl _ _ _ _ hσ, noisyAdv_cl hσ hM, ?_, ?_,
    ?_⟩
  · simpa only [regretU_cl] using hm
  · simpa only [regretU_cl] using hnn
  · simpa only [regretU_cl] using hge

/-- **Theorem GROW, Gaussian form, for the programs of the oracle machine, in the objects of `TheoremUnified`**
(`TheoremGrowGProg`). -/
theorem theoremGrowGProg : TheoremGrowGProg :=
  growGProg_of_growG theoremGrowG

end AdversarialBco.Grow
