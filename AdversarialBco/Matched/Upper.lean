/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Minimax.Upper
public import AdversarialBco.StatementUW

@[expose] public section

/-!
# The upper half of the matched minimax theorem from `TheoremUW`

`minimax_upper_of_UW : TheoremUW → ...`: the program of `TheoremUW`, with its windows, is a learner within cost and
space `B = C' (d log(2dn/δ) S)^k` (clause (i)), and in every environment with its windows the probability clause of
(ii), `μ {Reg_n > C W} ≤ δ` with `W = d^{3/2} √n log^5(2dn) + d √(n log(2/δ)) log^{9/2}(2dn)` (`thrW`), gives its
quantile payoff at most `C W` and its mean payoff at most `C W + n δ` (`payoff_le_of_prob`). The mean clause of
`TheoremUW` is not used: the bound in expectation is derived from the bound in probability and `Reg_n ≤ n`. The
constant is `max C 0`, so that `C W ≥ 0`. As `minimax_upper_of_unified` (Minimax/Upper.lean) for `TheoremUnified`.
-/

open MeasureTheory Set

namespace AdversarialBco.Matched

open BitRAM BitRAMO Unified UnifiedLower Minimax

/-- The bound of `TheoremUW` without its constant:
`d^{3/2} √n log^5(2dn) + d √(n log(2/δ)) log^{9/2}(2dn)`. -/
noncomputable def thrW (d n : ℕ) (δ : ℝ) : ℝ :=
  (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n * Real.log (2 * d * n) ^ 5 +
    d * Real.sqrt (n * Real.log (2 / δ)) * Real.log (2 * d * n) ^ (9 / 2 : ℝ)

/-- `log (2 d n) > 0` for `d, n ≥ 1`. -/
theorem log2dn_pos {d n : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n) : 0 < Real.log (2 * d * n) := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  exact Real.log_pos (by nlinarith)

/-- The bound of `TheoremUW` is nonnegative for `d, n ≥ 1`. -/
theorem thrW_nonneg {d n : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n) (δ : ℝ) : 0 ≤ thrW d n δ := by
  have h := log2dn_pos hd hn
  have h9 : 0 ≤ Real.log (2 * d * n) ^ (9 / 2 : ℝ) := Real.rpow_nonneg h.le _
  unfold thrW
  positivity

/-- The threshold of `TheoremUW` at `C` is at most the one at `max C 0`. -/
theorem thrW_le_max (C : ℝ) {d n : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n) (δ : ℝ) :
    C * thrW d n δ ≤ max C 0 * thrW d n δ :=
  mul_le_mul_of_nonneg_right (le_max_left C 0) (thrW_nonneg hd hn δ)

/-- **The upper half of the matched minimax theorem, from `TheoremUW`.** Constants `C ≥ 0`, `C'`, `k` such that for
every input of the class, with `U_W = C thrW` and `B = C' (d log(2dn/δ) S)^k`: a learner within cost and space `B`
(the program of `TheoremUW` with its windows) has every mean payoff at most `U_W + n δ` and every quantile payoff at
most `U_W`; `V⁺(G) ≤ V⁺_B(G) ≤ U_W + n δ` and `V_δ(G) ≤ V_{δ,B}(G) ≤ U_W`. -/
theorem minimax_upper_of_UW (hU : TheoremUW) :
    ∃ (C C' : ℝ) (k : ℕ), 0 ≤ C ∧
    ∀ d : ℕ, 1 ≤ d → ∀ n : ℕ, 1 ≤ n → ∀ δ r0 R0 : ℚ, 0 < δ → δ < 1 → 0 < r0 → r0 ≤ R0 →
    ∀ (a : Fin d → ℚ) (K : Set (E d)), IsCompact K → Convex ℝ K →
      Metric.closedBall (toE a) (r0 : ℝ) ⊆ K → K ⊆ Metric.closedBall (toE a) (R0 : ℝ) →
    ∀ orc : (Fin d → ℚ) → ℕ → Bool, WeakMemOracle K orc →
      (∃ ℓ ∈ LearnersB K orc (initU d n δ r0 R0 a) n
          (C' * ((d : ℝ) * Real.log (2 * d * n / (δ : ℝ)) * sizeU δ r0 R0 a) ^ k),
        (∀ v ∈ payoffs K n (initU d n δ r0 R0 a) orc meanPosOf ℓ, v ≤ C * thrW d n δ + n * (δ : ℝ)) ∧
        ∀ v ∈ payoffs K n (initU d n δ r0 R0 a) orc (quantileOf (δ : ℝ)) ℓ, v ≤ C * thrW d n δ) ∧
      valMean d n δ r0 R0 a K orc ≤
        valMeanB d n δ r0 R0 a K orc (C' * ((d : ℝ) * Real.log (2 * d * n / (δ : ℝ)) * sizeU δ r0 R0 a) ^ k) ∧
      valMeanB d n δ r0 R0 a K orc (C' * ((d : ℝ) * Real.log (2 * d * n / (δ : ℝ)) * sizeU δ r0 R0 a) ^ k) ≤
        C * thrW d n δ + n * (δ : ℝ) ∧
      valQuant d n δ r0 R0 a K orc δ ≤
        valQuantB d n δ r0 R0 a K orc
          (C' * ((d : ℝ) * Real.log (2 * d * n / (δ : ℝ)) * sizeU δ r0 R0 a) ^ k) δ ∧
      valQuantB d n δ r0 R0 a K orc
          (C' * ((d : ℝ) * Real.log (2 * d * n / (δ : ℝ)) * sizeU δ r0 R0 a) ^ k) δ ≤ C * thrW d n δ := by
  obtain ⟨P, C, C', k, D, D', h⟩ := hU
  refine ⟨max C 0, C', k, le_max_right C 0,
    fun d hd n hn δ r0 R0 hδ0 hδ1 hr0 hr0R a K hK hc hb1 hb2 orc horc => ?_⟩
  obtain ⟨hmach, hreg⟩ := h d hd n hn δ r0 R0 hδ0 hδ1 hr0 hr0R a K hK hc hb1 hb2 orc horc
  have hne : K.Nonempty := body_nonempty hr0 hb1
  have hδ0' : (0 : ℝ) ≤ δ := by exact_mod_cast hδ0.le
  have hδ1' : (δ : ℝ) < 1 := by exact_mod_cast hδ1
  have hX0 : 0 ≤ max C 0 * thrW d n δ := mul_nonneg (le_max_right C 0) (thrW_nonneg hd hn δ)
  set B := C' * ((d : ℝ) * Real.log (2 * d * n / (δ : ℝ)) * sizeU δ r0 R0 a) ^ k with hB
  set ℓ : ProgWin := ⟨P, D d n δ r0 R0 a, D' d n δ r0 R0 a⟩ with hℓdef
  have hℓ : ℓ ∈ LearnersB K orc (initU d n δ r0 R0 a) n B := hmach
  have hℓL : ℓ ∈ Learners K orc (initU d n δ r0 R0 a) n := learnersB_subset B hℓ
  -- the probability clause of `TheoremUW` at `max C 0`, in every environment with the windows of `ℓ`
  have hprob : ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) (coin : Ω → ℕ → Bool) (loss : ℕ → Ω → E d → ℝ)
      (noise : ℕ → Ω → ℝ), NoisyAdv K n ℓ.D ℓ.D' μ coin loss noise →
      μ {ω | max C 0 * thrW d n δ < regretU ℓ.prog K n (initU d n δ r0 R0 a) (envWorld orc coin loss noise ω)} ≤
        ENNReal.ofReal δ := by
    intro Ω _ μ coin loss noise hA
    refine (measure_mono fun ω hω => ?_).trans (hreg Ω μ coin loss noise hA).2.2.1
    exact lt_of_le_of_lt (thrW_le_max C hd hn δ) hω
  have hpay : ∀ v ∈ payoffs K n (initU d n δ r0 R0 a) orc (quantileOf δ) ℓ, v ≤ max C 0 * thrW d n δ := by
    rintro v ⟨Ω, _, μ, coin, loss, noise, hA, rfl⟩
    exact (payoff_le_of_prob hℓL hne hA hX0 hδ0' hδ1' (hprob Ω μ coin loss noise hA)).1
  have hpayM : ∀ v ∈ payoffs K n (initU d n δ r0 R0 a) orc meanPosOf ℓ, v ≤ max C 0 * thrW d n δ + n * δ := by
    rintro v ⟨Ω, _, μ, coin, loss, noise, hA, rfl⟩
    exact (payoff_le_of_prob hℓL hne hA hX0 hδ0' hδ1' (hprob Ω μ coin loss noise hA)).2
  refine ⟨⟨ℓ, hℓ, hpayM, hpay⟩, ?_, ?_, ?_, ?_⟩
  · exact value_anti subset_rfl (learnersB_subset B) ⟨ℓ, hℓ⟩ meanPosOf_range hc hne
  · exact value_le (learnersB_subset B) meanPosOf_range hc hne hℓ hpayM
  · exact value_anti subset_rfl (learnersB_subset B) ⟨ℓ, hℓ⟩ (quantileOf_range hδ1') hc hne
  · exact value_le (learnersB_subset B) (quantileOf_range hδ1') hc hne hℓ hpay

/-- The class of learners of every input of `TheoremUnified`'s class is nonempty: it contains the program of
`TheoremUW` with its windows. -/
theorem learners_nonempty_of_UW (hU : TheoremUW) :
    ∀ d : ℕ, 1 ≤ d → ∀ n : ℕ, 1 ≤ n → ∀ δ r0 R0 : ℚ, 0 < δ → δ < 1 → 0 < r0 → r0 ≤ R0 →
    ∀ (a : Fin d → ℚ) (K : Set (E d)), IsCompact K → Convex ℝ K →
      Metric.closedBall (toE a) (r0 : ℝ) ⊆ K → K ⊆ Metric.closedBall (toE a) (R0 : ℝ) →
    ∀ orc : (Fin d → ℚ) → ℕ → Bool, WeakMemOracle K orc →
      (Learners K orc (initU d n δ r0 R0 a) n).Nonempty := by
  obtain ⟨C, C', k, -, h⟩ := minimax_upper_of_UW hU
  intro d hd n hn δ r0 R0 hδ0 hδ1 hr0 hr0R a K hK hc hb1 hb2 orc horc
  obtain ⟨ℓ, hℓ, -⟩ := (h d hd n hn δ r0 R0 hδ0 hδ1 hr0 hr0R a K hK hc hb1 hb2 orc horc).1
  exact ⟨ℓ, learnersB_subset _ hℓ⟩

end AdversarialBco.Matched
