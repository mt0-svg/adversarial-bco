/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.LowerDeltaQ.Statement
public import AdversarialBco.LowerDeltaQ.Sanity
public import AdversarialBco.Minimax.Lower
public import AdversarialBco.LowerDeltaQ.Conj1
public import AdversarialBco.LowerDeltaQ.LowerUB
public import AdversarialBco.UW.TheoremU

@[expose] public section

/-!
# `TheoremMinimaxQ`

The minimax theorem of AdversarialBco/StatementMinimaxQ.lean, with the
lower bounds read from `TheoremLowerUDProgQ`:

* the upper bounds and the learner within cost and space `B`: `minimax_upper_of_unified` with `theoremUnified`,
  Theorem U as the corollary of Theorem UW (UW/TheoremU.lean);
* `√n / (4 √3) ≤ V⁺(G)`: `minimax_lower_small_of_lowerUDQ`, clause (c) of `TheoremLowerUDProgQ`;
* `3.71·10^-9 Λ ≤ V⁺(G)` and `7.42·10^-9 Λ ≤ V_δ(G)` for `δ < 1/2`: `minimax_lower_of_lowerUDQ`, clause (a) of
  `TheoremLowerUDProgQ` at the failure `1/2`, whose range holds for every `d ≥ 4·10^6` (`range_half`), with threshold
  `2.1·10^-8 (1/2)^{3/2} Λ ≥ 7.42·10^-9 Λ` (`c742_le`) and probability `1/2`, read through the tail for the mean;
* `7.42·10^-9 (1 - δ)^{3/2} Λ ≤ V_δ(G)` for `δ ≥ 1/2` under the range at `(1 - δ)/2`: `minimax_lower_high_of_lowerUDQ`,
  clause (a) at the failure `(1 - δ)/2`, threshold `2.1·10^-8 ((1 - δ)/2)^{3/2} Λ = 2.1·10^-8 · 2^{-3/2} (1 - δ)^{3/2} Λ`
  and probability `(1 + δ)/2 > δ`.

The solution module of the Comparator configuration config-minimax-q.json, the configuration of
StatementMinimaxQ.lean in the release: it imports the witnesses of LowerDeltaQ/Sanity.lean,
Minimax/Sanity.lean, UnifiedLower/Sanity.lean and Conj1LowerPolyD/Sanity.lean, `theoremConj1LowerPolyDQ_holds`
(LowerDeltaQ/Conj1.lean) and clause (b) of the v2.3 statements TheoremLowerU and TheoremLowerUProg
(LowerDeltaQ/LowerUB.lean).
-/

open MeasureTheory Set

namespace AdversarialBco.LowerDeltaQ

open BitRAM BitRAMO Unified UnifiedLower Minimax

/-- `7.42·10^-9 ≤ 2.1·10^-8 · (1/2)^{3/2}`. -/
theorem c742_le : (742 / 10 ^ 11 : ℝ) ≤ 21 / 10 ^ 9 * (1 / 2 : ℝ) ^ (3 / 2 : ℝ) := by
  obtain ⟨-, -, h3⟩ := sqrt_facts (show (0 : ℝ) < 1 / 2 by norm_num)
  rw [← h3]
  have := sqrt_half_cube_ge
  linarith

/-- `7.42·10^-9 · 2^{3/2} ≤ 2.1·10^-8`, so `7.42·10^-9 y ≤ 2.1·10^-8 (y / 2^{3/2})` for `y ≥ 0`. -/
theorem c742_two : (742 / 10 ^ 11 : ℝ) * (2 : ℝ) ^ (3 / 2 : ℝ) ≤ 21 / 10 ^ 9 := by
  rw [Lower.rpow_three_halves 2 (by norm_num)]
  have h : Real.sqrt 2 ≤ 14143 / 10000 := by
    rw [show (14143 / 10000 : ℝ) = Real.sqrt ((14143 / 10000) ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  nlinarith

/-- The range of clause (a) of `TheoremLowerUDQ` at `δ₀ = 1/2`, in the form of the statement. -/
theorem range_half_stmt {d : ℕ} (hd : 4000000 ≤ d) :
    1024 * (120 * Real.log d + 68) ≤ min (1 / 2 : ℝ) (1 / 2) * d ∧
      10 * (120 * Real.log d + 68) ≤ min (1 / 2 : ℝ) (1 / 2) ^ (3 / 2 : ℝ) * d := by
  obtain ⟨-, h2, h3⟩ := sqrt_facts (show (0 : ℝ) < 1 / 2 by norm_num)
  obtain ⟨hD1, hD3⟩ := range_half hd
  rw [h2] at hD1
  rw [h3] at hD3
  rw [min_self]
  exact ⟨hD1, hD3⟩

/-- **The lower half of the minimax theorem in the range `d ≥ 4·10^6`, `n ≥ d^10`, from clause (a) of
`TheoremLowerUDProgQ` at the failure `1/2`.** With `c = 7.42·10^-9 d^{3/2} √n / log d`, at most the threshold
`2.1·10^-8 min(1/2, 1/2)^{3/2} d^{3/2} √n / log d` of that clause: `c / 2 ≤ V⁺(G)` and `c ≤ V_δ(G)` when `δ < 1/2`. -/
theorem minimax_lower_of_lowerUDQ (hLD : TheoremLowerUDProgQ) {d : ℕ} (hd : 4000000 ≤ d) {n : ℕ} (hn : d ^ 10 ≤ n)
    {δ r0 R0 : ℚ} (hδ0 : 0 < δ) (hδ1 : δ < 1) (hr0 : 0 < r0) (hr0R : r0 ≤ R0) (a : Fin d → ℚ) {K : Set (E d)}
    (hK : IsCompact K) (hc : Convex ℝ K) (hb1 : Metric.closedBall (toE a) (r0 : ℝ) ⊆ K)
    (hb2 : K ⊆ Metric.closedBall (toE a) (R0 : ℝ)) {orc : (Fin d → ℚ) → ℕ → Bool} (horc : WeakMemOracle K orc)
    (hLne : (Learners K orc (initU d n δ r0 R0 a) n).Nonempty) :
    1 / 2 * (742 / 10 ^ 11 * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n / Real.log d) ≤ valMean d n δ r0 R0 a K orc ∧
      ((δ : ℝ) < 1 / 2 →
        742 / 10 ^ 11 * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n / Real.log d ≤ valQuant d n δ r0 R0 a K orc δ) := by
  have hd1 : 1 ≤ d := le_trans (by norm_num) hd
  have hn1 : 1 ≤ n := le_trans (Nat.one_le_pow _ _ (by omega)) hn
  have hdR : (4000000 : ℝ) ≤ d := by exact_mod_cast hd
  have hL := Lower.ripeB_log d hdR
  have hD : 0 ≤ (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n / Real.log d := by positivity
  have hc0 : 0 ≤ 742 / 10 ^ 11 * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n / Real.log d := by positivity
  have hle : 742 / 10 ^ 11 * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n / Real.log d ≤
      21 / 10 ^ 9 * min (1 / 2 : ℝ) (1 / 2) ^ (3 / 2 : ℝ) * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n / Real.log d := by
    rw [min_self]
    have e1 : 742 / 10 ^ 11 * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n / Real.log d =
        742 / 10 ^ 11 * ((d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n / Real.log d) := by ring
    have e2 : 21 / 10 ^ 9 * (1 / 2 : ℝ) ^ (3 / 2 : ℝ) * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n / Real.log d =
        21 / 10 ^ 9 * (1 / 2 : ℝ) ^ (3 / 2 : ℝ) * ((d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n / Real.log d) := by ring
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_right c742_le hD
  have hp : ENNReal.ofReal (1 - 1 / 2 : ℝ) = 1 / 2 := by
    rw [show (1 - 1 / 2 : ℝ) = 1 / 2 by norm_num]; exact ofReal_half
  obtain ⟨hD1, hD3⟩ := range_half_stmt hd
  refine minimax_lower_of_env hr0 hb1 hLne hc0 fun ℓ hℓ => ?_
  obtain ⟨B, hM⟩ := hℓ
  obtain ⟨σ, loss, -, -, hN, -, -, hpr⟩ :=
    (hLD ℓ.prog d hd1 n hn1 δ r0 R0 hδ0 hδ1 hr0 hr0R a K hK hc hb1 hb2 orc horc B ℓ.D ℓ.D' hM).1 (1 / 2)
      (by norm_num) (by norm_num) hd hn hD1 hD3
  rw [hp] at hpr
  exact ⟨ℕ → Bool, inferInstance, coinStream, id, loss, fun _ _ => 0, hN,
    hpr.trans (measure_mono fun ω hω => le_trans hle hω)⟩

/-- **The lower bound `√n / (4 √3)` on the mean value, for every `d` and `n`**, from clause (c) of
`TheoremLowerUDProgQ` (a mean) and `E max(Reg_n, 0) ≥ E Reg_n`. -/
theorem minimax_lower_small_of_lowerUDQ (hLD : TheoremLowerUDProgQ) {d : ℕ} (hd : 1 ≤ d) {n : ℕ} (hn : 1 ≤ n)
    {δ r0 R0 : ℚ} (hδ0 : 0 < δ) (hδ1 : δ < 1) (hr0 : 0 < r0) (hr0R : r0 ≤ R0) (a : Fin d → ℚ) {K : Set (E d)}
    (hK : IsCompact K) (hc : Convex ℝ K) (hb1 : Metric.closedBall (toE a) (r0 : ℝ) ⊆ K)
    (hb2 : K ⊆ Metric.closedBall (toE a) (R0 : ℝ)) {orc : (Fin d → ℚ) → ℕ → Bool} (horc : WeakMemOracle K orc)
    (hLne : (Learners K orc (initU d n δ r0 R0 a) n).Nonempty) :
    Real.sqrt n / (4 * Real.sqrt 3) ≤ valMean d n δ r0 R0 a K orc := by
  refine le_valMean_of_mean hLne (body_nonempty hr0 hb1) fun ℓ hℓ => ?_
  obtain ⟨B, hM⟩ := hℓ
  obtain ⟨σ, loss, -, -, hN, hint, hm⟩ :=
    (hLD ℓ.prog d hd n hn δ r0 R0 hδ0 hδ1 hr0 hr0R a K hK hc hb1 hb2 orc horc B ℓ.D ℓ.D' hM).2.2.1
  exact ⟨ℕ → Bool, inferInstance, coinStream, id, loss, fun _ _ => 0, hN, hint, hm⟩

/-- **The lower bound on the quantile value for `δ ≥ 1/2`**, from clause (a) of `TheoremLowerUDProgQ` at the failure
probability `(1 - δ) / 2`: every learner has an environment with
`P(Reg_n ≥ 2.1·10^-8 ((1 - δ)/2)^{3/2} Λ) ≥ (1 + δ) / 2`, which is `> δ` for `δ < 1`, and
`2.1·10^-8 ((1 - δ)/2)^{3/2} ≥ 7.42·10^-9 (1 - δ)^{3/2}`, under the range at `(1 - δ)/2`. -/
theorem minimax_lower_high_of_lowerUDQ (hLD : TheoremLowerUDProgQ) {d : ℕ} (hd : 4000000 ≤ d) {n : ℕ}
    (hn : d ^ 10 ≤ n) {δ r0 R0 : ℚ} (hδ0 : 0 < δ) (hδ1 : δ < 1) (hr0 : 0 < r0) (hr0R : r0 ≤ R0) (a : Fin d → ℚ)
    {K : Set (E d)} (hK : IsCompact K) (hc : Convex ℝ K) (hb1 : Metric.closedBall (toE a) (r0 : ℝ) ⊆ K)
    (hb2 : K ⊆ Metric.closedBall (toE a) (R0 : ℝ)) {orc : (Fin d → ℚ) → ℕ → Bool} (horc : WeakMemOracle K orc)
    (hLne : (Learners K orc (initU d n δ r0 R0 a) n).Nonempty)
    (hD1 : 1024 * (120 * Real.log d + 68) ≤ (1 - (δ : ℝ)) / 2 * d)
    (hD3 : 10 * (120 * Real.log d + 68) ≤ ((1 - (δ : ℝ)) / 2) ^ (3 / 2 : ℝ) * d) :
    742 / 10 ^ 11 * (1 - (δ : ℝ)) ^ (3 / 2 : ℝ) * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n / Real.log d ≤
      valQuant d n δ r0 R0 a K orc δ := by
  have hd1 : 1 ≤ d := le_trans (by norm_num) hd
  have hn1 : 1 ≤ n := le_trans (Nat.one_le_pow _ _ (by omega)) hn
  have hdR : (4000000 : ℝ) ≤ d := by exact_mod_cast hd
  have hδ0' : (0 : ℝ) < δ := by exact_mod_cast hδ0
  have hδ1' : (δ : ℝ) < 1 := by exact_mod_cast hδ1
  have hmin := min_half_fail hδ0'.le
  have hf0 : 0 < (1 - (δ : ℝ)) / 2 := by linarith
  have hf1 : (1 - (δ : ℝ)) / 2 < 1 := by linarith
  have hL := Lower.ripeB_log d hdR
  have hD : 0 ≤ (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n / Real.log d := by positivity
  have hy : 0 ≤ (1 - (δ : ℝ)) ^ (3 / 2 : ℝ) := Real.rpow_nonneg (by linarith) _
  have h2 : 0 < (2 : ℝ) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
  have hdiv : ((1 - (δ : ℝ)) / 2) ^ (3 / 2 : ℝ) = (1 - (δ : ℝ)) ^ (3 / 2 : ℝ) / (2 : ℝ) ^ (3 / 2 : ℝ) :=
    Real.div_rpow (by linarith) (by norm_num) _
  have hle : 742 / 10 ^ 11 * (1 - (δ : ℝ)) ^ (3 / 2 : ℝ) * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n / Real.log d ≤
      21 / 10 ^ 9 * min ((1 - (δ : ℝ)) / 2) (1 / 2) ^ (3 / 2 : ℝ) * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n /
        Real.log d := by
    rw [hmin, hdiv]
    have e1 : 742 / 10 ^ 11 * (1 - (δ : ℝ)) ^ (3 / 2 : ℝ) * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n / Real.log d =
        742 / 10 ^ 11 * ((1 - (δ : ℝ)) ^ (3 / 2 : ℝ) * ((d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n / Real.log d)) := by
      ring
    have e2 : 21 / 10 ^ 9 * ((1 - (δ : ℝ)) ^ (3 / 2 : ℝ) / (2 : ℝ) ^ (3 / 2 : ℝ)) * (d : ℝ) ^ (3 / 2 : ℝ) *
        Real.sqrt n / Real.log d = 21 / 10 ^ 9 / (2 : ℝ) ^ (3 / 2 : ℝ) *
          ((1 - (δ : ℝ)) ^ (3 / 2 : ℝ) * ((d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n / Real.log d)) := by
      ring
    rw [e1, e2]
    have hc : (742 / 10 ^ 11 : ℝ) ≤ 21 / 10 ^ 9 / (2 : ℝ) ^ (3 / 2 : ℝ) := by
      rw [le_div_iff₀ h2]; exact c742_two
    exact mul_le_mul_of_nonneg_right hc (mul_nonneg hy hD)
  refine le_valQuant_of hLne (body_nonempty hr0 hb1) hδ1' fun ℓ hℓ => ?_
  obtain ⟨B, hM⟩ := hℓ
  obtain ⟨σ, loss, -, -, hN, -, -, hp⟩ :=
    (hLD ℓ.prog d hd1 n hn1 δ r0 R0 hδ0 hδ1 hr0 hr0R a K hK hc hb1 hb2 orc horc B ℓ.D ℓ.D' hM).1
      ((1 - (δ : ℝ)) / 2) hf0 hf1 hd hn (by rw [hmin]; exact hD1) (by rw [hmin]; exact hD3)
  refine ⟨ℕ → Bool, inferInstance, coinStream, id, loss, fun _ _ => 0, hN,
    lt_of_lt_of_le ?_ (hp.trans (measure_mono fun ω hω => le_trans hle hω))⟩
  exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)

/-- **The minimax theorem at the constants of Theorem LU-DQ, from the upper theorem and `TheoremLowerUDProgQ`.** -/
theorem theoremMinimaxQ_of_UD (hU : TheoremUnified) (hLD : TheoremLowerUDProgQ) : TheoremMinimaxQ := by
  obtain ⟨C, C', k, -, h⟩ := minimax_upper_of_unified hU
  refine ⟨C, C', k, fun d hd n hn δ r0 R0 hδ0 hδ1 hr0 hr0R a K hK hc hb1 hb2 orc horc => ?_⟩
  obtain ⟨hne, h1, h2, h3, h4⟩ := h d hd n hn δ r0 R0 hδ0 hδ1 hr0 hr0R a K hK hc hb1 hb2 orc horc
  have hLne := learners_nonempty_of_unified hU d hd n hn δ r0 R0 hδ0 hδ1 hr0 hr0R a K hK hc hb1 hb2 orc horc
  refine ⟨hne, h1, h2, h3, h4,
    minimax_lower_small_of_lowerUDQ hLD hd hn hδ0 hδ1 hr0 hr0R a hK hc hb1 hb2 horc hLne, fun hd4 hn10 => ?_⟩
  obtain ⟨hM, hQ⟩ := minimax_lower_of_lowerUDQ hLD hd4 hn10 hδ0 hδ1 hr0 hr0R a hK hc hb1 hb2 horc hLne
  exact ⟨le_of_eq_of_le (by ring) hM, hQ, fun _ hD1 hD3 =>
    minimax_lower_high_of_lowerUDQ hLD hd4 hn10 hδ0 hδ1 hr0 hr0R a hK hc hb1 hb2 horc hLne hD1 hD3⟩

/-- **Theorem MM at the constants of Theorem LU-DQ** (`TheoremMinimaxQ`). -/
theorem theoremMinimaxQ : TheoremMinimaxQ :=
  theoremMinimaxQ_of_UD theoremUnified theoremLowerUDProgQ

end AdversarialBco.LowerDeltaQ
