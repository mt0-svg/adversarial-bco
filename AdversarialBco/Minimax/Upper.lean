/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Minimax.Value

@[expose] public section

/-!
# The upper half of the minimax theorem from `TheoremUnified`

`minimax_upper_of_unified : TheoremUnified → ...`: the program of `TheoremUnified`, with its windows, is a learner
within cost and space `B = C' (d log(2dn/δ) S)^k` (clause (i)), and in every environment with its windows the
probability clause of (ii), `μ {Reg_n > U} ≤ δ`, gives its quantile payoff at most `U` and its mean payoff at most
`U + n δ` (`payoff_le_of_prob`: the tail is at most `1` on `(0, U]`, at most `δ` beyond `U`, `0` from `n` on). The
expectation clause of (ii) is not used: the bound in expectation is derived from the bound in probability and
`Reg_n ≤ n`. The constant is `max C 0` for the `C` of `TheoremUnified` (the probability clause at `C` implies the
one at `max C 0`, the threshold being larger), so that `U ≥ 0`.

Also: the class of learners is nonempty for every input of the class (`learners_nonempty_of_unified`), so the values
lie in the ranges of the payoffs: no `sInf` of an empty set.
-/

open MeasureTheory Set

namespace AdversarialBco.Minimax

open BitRAM BitRAMO Unified UnifiedLower

/-- A body of `TheoremUnified`'s class is nonempty: it contains its centre. -/
theorem body_nonempty {d : ℕ} {a : Fin d → ℚ} {r0 : ℚ} (hr0 : 0 < r0) {K : Set (E d)}
    (hb1 : Metric.closedBall (toE a) (r0 : ℝ) ⊆ K) : K.Nonempty :=
  ⟨toE a, hb1 (Metric.mem_closedBall_self (by exact_mod_cast hr0.le))⟩

/-- `log (2 d n / δ) > 0` for `d, n ≥ 1` and `0 < δ < 1`. -/
theorem logL_pos {d n : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n) {δ : ℚ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    0 < Real.log (2 * d * n / (δ : ℝ)) := by
  have hδ0' : (0 : ℝ) < δ := by exact_mod_cast hδ0
  have hδ1' : (δ : ℝ) < 1 := by exact_mod_cast hδ1
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  refine Real.log_pos ?_
  rw [lt_div_iff₀ hδ0']
  nlinarith

/-- The threshold of `TheoremUnified` at `C` is at most the one at `max C 0`. -/
theorem thr_le_max (C : ℝ) {d n : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n) {δ : ℚ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    C * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n * Real.log (2 * d * n / (δ : ℝ)) ^ 5 ≤
      max C 0 * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n * Real.log (2 * d * n / (δ : ℝ)) ^ 5 := by
  have hX : 0 ≤ (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n * Real.log (2 * d * n / (δ : ℝ)) ^ 5 := by
    have := logL_pos hd hn hδ0 hδ1
    positivity
  have h := mul_le_mul_of_nonneg_right (le_max_left C 0) hX
  simpa only [mul_assoc] using h

/-- **The upper half of the minimax theorem, from `TheoremUnified`.** Constants `C ≥ 0`, `C'`, `k` such that for every
input of the class, with `U = C d^{3/2} √n log(2dn/δ)^5` and `B = C' (d log(2dn/δ) S)^k`: a learner within cost and
space `B` (the program of `TheoremUnified` with its windows) has every mean payoff at most `U + n δ` and every quantile
payoff at most `U`; `V⁺(G) ≤ V⁺_B(G) ≤ U + n δ` and `V_δ(G) ≤ V_{δ,B}(G) ≤ U`. -/
theorem minimax_upper_of_unified (hU : TheoremUnified) :
    ∃ (C C' : ℝ) (k : ℕ), 0 ≤ C ∧
    ∀ d : ℕ, 1 ≤ d → ∀ n : ℕ, 1 ≤ n → ∀ δ r0 R0 : ℚ, 0 < δ → δ < 1 → 0 < r0 → r0 ≤ R0 →
    ∀ (a : Fin d → ℚ) (K : Set (E d)), IsCompact K → Convex ℝ K →
      Metric.closedBall (toE a) (r0 : ℝ) ⊆ K → K ⊆ Metric.closedBall (toE a) (R0 : ℝ) →
    ∀ orc : (Fin d → ℚ) → ℕ → Bool, WeakMemOracle K orc →
      (∃ ℓ ∈ LearnersB K orc (initU d n δ r0 R0 a) n
          (C' * ((d : ℝ) * Real.log (2 * d * n / (δ : ℝ)) * sizeU δ r0 R0 a) ^ k),
        (∀ v ∈ payoffs K n (initU d n δ r0 R0 a) orc meanPosOf ℓ,
          v ≤ C * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n * Real.log (2 * d * n / (δ : ℝ)) ^ 5 + n * (δ : ℝ)) ∧
        ∀ v ∈ payoffs K n (initU d n δ r0 R0 a) orc (quantileOf (δ : ℝ)) ℓ,
          v ≤ C * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n * Real.log (2 * d * n / (δ : ℝ)) ^ 5) ∧
      valMean d n δ r0 R0 a K orc ≤
        valMeanB d n δ r0 R0 a K orc (C' * ((d : ℝ) * Real.log (2 * d * n / (δ : ℝ)) * sizeU δ r0 R0 a) ^ k) ∧
      valMeanB d n δ r0 R0 a K orc (C' * ((d : ℝ) * Real.log (2 * d * n / (δ : ℝ)) * sizeU δ r0 R0 a) ^ k) ≤
        C * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n * Real.log (2 * d * n / (δ : ℝ)) ^ 5 + n * (δ : ℝ) ∧
      valQuant d n δ r0 R0 a K orc δ ≤
        valQuantB d n δ r0 R0 a K orc
          (C' * ((d : ℝ) * Real.log (2 * d * n / (δ : ℝ)) * sizeU δ r0 R0 a) ^ k) δ ∧
      valQuantB d n δ r0 R0 a K orc
          (C' * ((d : ℝ) * Real.log (2 * d * n / (δ : ℝ)) * sizeU δ r0 R0 a) ^ k) δ ≤
        C * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n * Real.log (2 * d * n / (δ : ℝ)) ^ 5 := by
  obtain ⟨P, C, C', k, D, D', h⟩ := hU
  refine ⟨max C 0, C', k, le_max_right C 0,
    fun d hd n hn δ r0 R0 hδ0 hδ1 hr0 hr0R a K hK hc hb1 hb2 orc horc => ?_⟩
  obtain ⟨hmach, hreg⟩ := h d hd n hn δ r0 R0 hδ0 hδ1 hr0 hr0R a K hK hc hb1 hb2 orc horc
  have hne : K.Nonempty := body_nonempty hr0 hb1
  have hδ0' : (0 : ℝ) ≤ δ := by exact_mod_cast hδ0.le
  have hδ1' : (δ : ℝ) < 1 := by exact_mod_cast hδ1
  have hX0 : 0 ≤ max C 0 * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n * Real.log (2 * d * n / (δ : ℝ)) ^ 5 := by
    have := logL_pos hd hn hδ0 hδ1
    have := le_max_right C 0
    positivity
  set B := C' * ((d : ℝ) * Real.log (2 * d * n / (δ : ℝ)) * sizeU δ r0 R0 a) ^ k with hB
  set ℓ : ProgWin := ⟨P, D d n δ r0 R0 a, D' d n δ r0 R0 a⟩ with hℓdef
  have hℓ : ℓ ∈ LearnersB K orc (initU d n δ r0 R0 a) n B := hmach
  have hℓL : ℓ ∈ Learners K orc (initU d n δ r0 R0 a) n := learnersB_subset B hℓ
  -- every payoff of `ℓ` from the probability clause
  have hpay : ∀ v ∈ payoffs K n (initU d n δ r0 R0 a) orc (quantileOf δ) ℓ,
      v ≤ max C 0 * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n * Real.log (2 * d * n / (δ : ℝ)) ^ 5 := by
    rintro v ⟨Ω, _, μ, coin, loss, noise, hA, rfl⟩
    have hP := (hreg Ω μ coin loss noise hA).2.2.1
    refine (payoff_le_of_prob hℓL hne hA hX0 hδ0' hδ1' ((measure_mono fun ω hω => ?_).trans hP)).1
    exact lt_of_le_of_lt (thr_le_max C hd hn hδ0 hδ1) hω
  have hpayM : ∀ v ∈ payoffs K n (initU d n δ r0 R0 a) orc meanPosOf ℓ,
      v ≤ max C 0 * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n * Real.log (2 * d * n / (δ : ℝ)) ^ 5 + n * δ := by
    rintro v ⟨Ω, _, μ, coin, loss, noise, hA, rfl⟩
    have hP := (hreg Ω μ coin loss noise hA).2.2.1
    refine (payoff_le_of_prob hℓL hne hA hX0 hδ0' hδ1' ((measure_mono fun ω hω => ?_).trans hP)).2
    exact lt_of_le_of_lt (thr_le_max C hd hn hδ0 hδ1) hω
  refine ⟨⟨ℓ, hℓ, hpayM, hpay⟩, ?_, ?_, ?_, ?_⟩
  · exact value_anti subset_rfl (learnersB_subset B) ⟨ℓ, hℓ⟩ meanPosOf_range hc hne
  · exact value_le (learnersB_subset B) meanPosOf_range hc hne hℓ hpayM
  · exact value_anti subset_rfl (learnersB_subset B) ⟨ℓ, hℓ⟩ (quantileOf_range hδ1') hc hne
  · exact value_le (learnersB_subset B) (quantileOf_range hδ1') hc hne hℓ hpay

/-- The class of learners of every input of `TheoremUnified`'s class is nonempty: it contains the program of
`TheoremUnified` with its windows. -/
theorem learners_nonempty_of_unified (hU : TheoremUnified) :
    ∀ d : ℕ, 1 ≤ d → ∀ n : ℕ, 1 ≤ n → ∀ δ r0 R0 : ℚ, 0 < δ → δ < 1 → 0 < r0 → r0 ≤ R0 →
    ∀ (a : Fin d → ℚ) (K : Set (E d)), IsCompact K → Convex ℝ K →
      Metric.closedBall (toE a) (r0 : ℝ) ⊆ K → K ⊆ Metric.closedBall (toE a) (R0 : ℝ) →
    ∀ orc : (Fin d → ℚ) → ℕ → Bool, WeakMemOracle K orc →
      (Learners K orc (initU d n δ r0 R0 a) n).Nonempty := by
  obtain ⟨C, C', k, -, h⟩ := minimax_upper_of_unified hU
  intro d hd n hn δ r0 R0 hδ0 hδ1 hr0 hr0R a K hK hc hb1 hb2 orc horc
  obtain ⟨ℓ, hℓ, -⟩ := (h d hd n hn δ r0 R0 hδ0 hδ1 hr0 hr0R a K hK hc hb1 hb2 orc horc).1
  exact ⟨ℓ, learnersB_subset _ hℓ⟩

end AdversarialBco.Minimax

