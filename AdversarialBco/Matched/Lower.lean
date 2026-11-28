/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Minimax.Lower
public import AdversarialBco.StatementMatched
public import AdversarialBco.Matched.Arith

@[expose] public section

/-!
# The lower half of the matched minimax theorem from `TheoremLowerUDProgQ` and `TheoremGrowGProg`

With `Λ = d^{3/2} √n`:

* `minimax_lower_of_lowerUDQ`: clause (a) of `TheoremLowerUDProgQ` at the failure `1/2`, whose range hypotheses hold
  for every `d ≥ 4·10^6` (`range_half`), gives every learner an environment with
  `P(Reg_n ≥ 7.42·10^-9 Λ / log d) ≥ 1/2` (the threshold `2.1·10^-8 (1/2)^{3/2} Λ / log d` is at least that,
  `three_halves_half`); so `V⁺(G) ≥ 3.71·10^-9 Λ / log d` (the expectation form, read through the tail) and
  `V_δ(G) ≥ 7.42·10^-9 Λ / log d` for `δ < 1/2` (`Minimax.minimax_lower_of_env`);
* `minimax_lower_small_of_lowerUDQ`: `V⁺(G) ≥ √n / (4 √3)` from clause (c) of `TheoremLowerUDProgQ`;
* `minimax_lower_high_of_lowerUDQ`: for `δ ≥ 1/2`, clause (a) at the failure `(1 - δ)/2`, probability
  `(1 + δ)/2 > δ`, threshold `2.1·10^-8 ((1 - δ)/2)^{3/2} Λ / log d ≥ 7.42·10^-9 (1 - δ)^{3/2} Λ / log d`
  (`rpow_three_halves_mul`);
* `minimax_lower_grow_of_growG`: for `log (1/δ) ≥ 60` and `n ≥ d^6 log (1/δ)`, `TheoremGrowGProg` at `δ' = δ` gives
  every learner an environment with `P(Reg_n ≥ 8·10^-6 d √(n log(1/δ)) / (log d √log n)) > δ`, so `V_δ(G)` is at least
  that (`le_valQuant_of`);
* `minimax_matched_of`: the matched clause, by `matched_combine` (the case `log (1/δ) < 60` by `small_ell`).
-/

open MeasureTheory Set

namespace AdversarialBco.Matched

open BitRAM BitRAMO Unified UnifiedLower Minimax

/-- **The lower bounds of the range `d ≥ 4·10^6`, `n ≥ d^10`, from clause (a) of `TheoremLowerUDProgQ` at the failure
`1/2`.** With `c = 7.42·10^-9 d^{3/2} √n / log d`: `c / 2 ≤ V⁺(G)` and `c ≤ V_δ(G)` when `δ < 1/2`. -/
theorem minimax_lower_of_lowerUDQ (hLD : TheoremLowerUDProgQ) {d : ℕ} (hd : 4000000 ≤ d) {n : ℕ}
    (hn : d ^ 10 ≤ n) {δ r0 R0 : ℚ} (hδ0 : 0 < δ) (hδ1 : δ < 1) (hr0 : 0 < r0) (hr0R : r0 ≤ R0) (a : Fin d → ℚ)
    {K : Set (E d)} (hK : IsCompact K) (hc : Convex ℝ K) (hb1 : Metric.closedBall (toE a) (r0 : ℝ) ⊆ K)
    (hb2 : K ⊆ Metric.closedBall (toE a) (R0 : ℝ)) {orc : (Fin d → ℚ) → ℕ → Bool} (horc : WeakMemOracle K orc)
    (hLne : (Learners K orc (initU d n δ r0 R0 a) n).Nonempty) :
    1 / 2 * (742 / 10 ^ 11 * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n / Real.log d) ≤ valMean d n δ r0 R0 a K orc ∧
      ((δ : ℝ) < 1 / 2 →
        742 / 10 ^ 11 * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n / Real.log d ≤ valQuant d n δ r0 R0 a K orc δ) := by
  have hd1 : 1 ≤ d := le_trans (by norm_num) hd
  have hn1 : 1 ≤ n := le_trans (Nat.one_le_pow _ _ (by omega)) hn
  have hlog : 0 ≤ Real.log d := Real.log_nonneg (by exact_mod_cast hd1)
  have hΛ : 0 ≤ (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n / Real.log d := by positivity
  have hthr : 742 / 10 ^ 11 * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n / Real.log d ≤
      21 / 10 ^ 9 * min (1 / 2 : ℝ) (1 / 2) ^ (3 / 2 : ℝ) * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n / Real.log d := by
    rw [min_self]
    have h := mul_le_mul_of_nonneg_right three_halves_half hΛ
    simpa only [mul_div_assoc, mul_assoc] using h
  have hp : ENNReal.ofReal (1 - 1 / 2 : ℝ) = 1 / 2 := by
    rw [show (1 - 1 / 2 : ℝ) = 1 / 2 by norm_num]; exact ofReal_half
  refine minimax_lower_of_env hr0 hb1 hLne (by positivity) fun ℓ hℓ => ?_
  obtain ⟨B, hM⟩ := hℓ
  obtain ⟨hr1, hr2⟩ := range_half d hd
  obtain ⟨σ, loss, -, -, hN, -, -, hpr⟩ :=
    (hLD ℓ.prog d hd1 n hn1 δ r0 R0 hδ0 hδ1 hr0 hr0R a K hK hc hb1 hb2 orc horc B ℓ.D ℓ.D' hM).1 (1 / 2)
      (by norm_num) (by norm_num) hd hn hr1 hr2
  rw [hp] at hpr
  exact ⟨ℕ → Bool, inferInstance, coinStream, id, loss, fun _ _ => 0, hN,
    hpr.trans (measure_mono fun cs hcs => le_trans hthr hcs)⟩

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
`(1 - δ) / 2`: every learner has an environment with `P(Reg_n ≥ 7.42·10^-9 (1 - δ)^{3/2} Λ / log d) ≥ (1 + δ) / 2`,
which is `> δ` for `δ < 1`. -/
theorem minimax_lower_high_of_lowerUDQ (hLD : TheoremLowerUDProgQ) {d : ℕ} (hd : 4000000 ≤ d) {n : ℕ}
    (hn : d ^ 10 ≤ n) {δ r0 R0 : ℚ} (hδ0 : 0 < δ) (hδ1 : δ < 1) (hr0 : 0 < r0) (hr0R : r0 ≤ R0) (a : Fin d → ℚ)
    {K : Set (E d)} (hK : IsCompact K) (hc : Convex ℝ K) (hb1 : Metric.closedBall (toE a) (r0 : ℝ) ⊆ K)
    (hb2 : K ⊆ Metric.closedBall (toE a) (R0 : ℝ)) {orc : (Fin d → ℚ) → ℕ → Bool} (horc : WeakMemOracle K orc)
    (hLne : (Learners K orc (initU d n δ r0 R0 a) n).Nonempty)
    (hr1 : 1024 * (120 * Real.log d + 68) ≤ (1 - (δ : ℝ)) / 2 * d)
    (hr2 : 10 * (120 * Real.log d + 68) ≤ ((1 - (δ : ℝ)) / 2) ^ (3 / 2 : ℝ) * d) :
    742 / 10 ^ 11 * (1 - (δ : ℝ)) ^ (3 / 2 : ℝ) * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n / Real.log d ≤
      valQuant d n δ r0 R0 a K orc δ := by
  have hd1 : 1 ≤ d := le_trans (by norm_num) hd
  have hn1 : 1 ≤ n := le_trans (Nat.one_le_pow _ _ (by omega)) hn
  have hδ0' : (0 : ℝ) < δ := by exact_mod_cast hδ0
  have hδ1' : (δ : ℝ) < 1 := by exact_mod_cast hδ1
  have hmin := min_half_fail hδ0'.le
  have hf0 : 0 < (1 - (δ : ℝ)) / 2 := by linarith
  have hf1 : (1 - (δ : ℝ)) / 2 < 1 := by linarith
  have hlog : 0 ≤ Real.log d := Real.log_nonneg (by exact_mod_cast hd1)
  have hΛ : 0 ≤ (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n / Real.log d := by positivity
  have hthr : 742 / 10 ^ 11 * (1 - (δ : ℝ)) ^ (3 / 2 : ℝ) * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n / Real.log d ≤
      21 / 10 ^ 9 * min ((1 - (δ : ℝ)) / 2) (1 / 2) ^ (3 / 2 : ℝ) * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n /
        Real.log d := by
    rw [hmin]
    have h := mul_le_mul_of_nonneg_right (rpow_three_halves_mul (1 - (δ : ℝ)) (by linarith)) hΛ
    simpa only [mul_div_assoc, mul_assoc] using h
  refine le_valQuant_of hLne (body_nonempty hr0 hb1) hδ1' fun ℓ hℓ => ?_
  obtain ⟨B, hM⟩ := hℓ
  obtain ⟨σ, loss, -, -, hN, -, -, hp⟩ :=
    (hLD ℓ.prog d hd1 n hn1 δ r0 R0 hδ0 hδ1 hr0 hr0R a K hK hc hb1 hb2 orc horc B ℓ.D ℓ.D' hM).1
      ((1 - (δ : ℝ)) / 2) hf0 hf1 hd hn (by rw [hmin]; exact hr1) (by rw [hmin]; exact hr2)
  refine ⟨ℕ → Bool, inferInstance, coinStream, id, loss, fun _ _ => 0, hN,
    lt_of_lt_of_le ?_ (hp.trans (measure_mono fun cs hcs => le_trans hthr hcs))⟩
  exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)

/-- **The growing lower bound on the quantile value**, from `TheoremGrowGProg` at the failure `δ' = δ`: for
`d ≥ 4·10^6`, `log (1/δ) ≥ 60` and `n ≥ d^6 log (1/δ)`, every learner has an environment with
`P(Reg_n ≥ 8·10^-6 d √(n log(1/δ)) / (log d √log n)) > δ`, so `V_δ(G)` is at least that threshold. -/
theorem minimax_lower_grow_of_growG (hG : TheoremGrowGProg) {d : ℕ} (hd : 4000000 ≤ d) {n : ℕ} (hn1 : 1 ≤ n)
    {δ r0 R0 : ℚ} (hδ0 : 0 < δ) (hδ1 : δ < 1) (hr0 : 0 < r0) (hr0R : r0 ≤ R0) (a : Fin d → ℚ) {K : Set (E d)}
    (hK : IsCompact K) (hc : Convex ℝ K) (hb1 : Metric.closedBall (toE a) (r0 : ℝ) ⊆ K)
    (hb2 : K ⊆ Metric.closedBall (toE a) (R0 : ℝ)) {orc : (Fin d → ℚ) → ℕ → Bool} (horc : WeakMemOracle K orc)
    (hLne : (Learners K orc (initU d n δ r0 R0 a) n).Nonempty) (hl : 60 ≤ Real.log (1 / (δ : ℝ)))
    (hw : (d : ℝ) ^ 6 * Real.log (1 / (δ : ℝ)) ≤ n) :
    8 / 10 ^ 6 * d * Real.sqrt (n * Real.log (1 / (δ : ℝ))) / (Real.log d * Real.sqrt (Real.log n)) ≤
      valQuant d n δ r0 R0 a K orc δ := by
  have hd1 : 1 ≤ d := le_trans (by norm_num) hd
  have hδ0' : (0 : ℝ) < δ := by exact_mod_cast hδ0
  have hδ1' : (δ : ℝ) < 1 := by exact_mod_cast hδ1
  refine le_valQuant_of hLne (body_nonempty hr0 hb1) hδ1' fun ℓ hℓ => ?_
  obtain ⟨B, hM⟩ := hℓ
  obtain ⟨p, hδp, σ, loss, -, -, hN, -, -, hp⟩ :=
    hG ℓ.prog d hd1 n hn1 δ r0 R0 hδ0 hδ1 hr0 hr0R a K hK hc hb1 hb2 orc horc B ℓ.D ℓ.D' hM δ hδ0' hd hl hw
  exact ⟨ℕ → Bool, inferInstance, coinStream, id, loss, fun _ _ => 0, hN, lt_of_lt_of_le hδp hp⟩

/-- **The matched clause.** For `d ≥ 4·10^6`, `n ≥ d^10`, `δ < 1/2` and `log (1/δ) ≤ n / d^6`:
`7·10^-9 (d^{3/2} √n / log d + d √(n log(1/δ)) / (log d √log n)) ≤ V_δ(G)`, from `minimax_lower_of_lowerUDQ`
(always) and `minimax_lower_grow_of_growG` (when `log (1/δ) ≥ 60`) by `matched_combine`. -/
theorem minimax_matched_of (hLD : TheoremLowerUDProgQ) (hG : TheoremGrowGProg) {d : ℕ} (hd : 4000000 ≤ d) {n : ℕ}
    (hn : d ^ 10 ≤ n) {δ r0 R0 : ℚ} (hδ0 : 0 < δ) (hδ1 : δ < 1) (hr0 : 0 < r0) (hr0R : r0 ≤ R0) (a : Fin d → ℚ)
    {K : Set (E d)} (hK : IsCompact K) (hc : Convex ℝ K) (hb1 : Metric.closedBall (toE a) (r0 : ℝ) ⊆ K)
    (hb2 : K ⊆ Metric.closedBall (toE a) (R0 : ℝ)) {orc : (Fin d → ℚ) → ℕ → Bool} (horc : WeakMemOracle K orc)
    (hLne : (Learners K orc (initU d n δ r0 R0 a) n).Nonempty) (hδ : (δ : ℝ) < 1 / 2)
    (hw : Real.log (1 / (δ : ℝ)) ≤ n / (d : ℝ) ^ 6) :
    7 / 10 ^ 9 * ((d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n / Real.log d +
        d * Real.sqrt (n * Real.log (1 / (δ : ℝ))) / (Real.log d * Real.sqrt (Real.log n))) ≤
      valQuant d n δ r0 R0 a K orc δ := by
  have hd1 : 1 ≤ d := le_trans (by norm_num) hd
  have hn1 : 1 ≤ n := le_trans (Nat.one_le_pow _ _ (by omega)) hn
  have hδ0' : (0 : ℝ) < δ := by exact_mod_cast hδ0
  have hd0 : (0 : ℝ) < (d : ℝ) ^ 6 := by positivity
  have hld : 0 < Real.log d := Real.log_pos (by exact_mod_cast (show 1 < d by omega))
  have hℓ0 : 0 ≤ Real.log (1 / (δ : ℝ)) :=
    Real.log_nonneg (by rw [le_div_iff₀ hδ0']; linarith)
  have h1 := (minimax_lower_of_lowerUDQ hLD hd hn hδ0 hδ1 hr0 hr0R a hK hc hb1 hb2 horc hLne).2 hδ
  refine matched_combine (ℓ := Real.log (1 / (δ : ℝ))) (by positivity) (by positivity) hld
    (one_le_sqrt_log d n hd hn) (by rw [← mul_assoc]; exact h1) (fun hl => ?_)
    (fun hl => small_ell d n _ hd hl)
  have hw' : (d : ℝ) ^ 6 * Real.log (1 / (δ : ℝ)) ≤ n := by
    rw [le_div_iff₀ hd0] at hw; linarith
  have h2 := minimax_lower_grow_of_growG hG hd hn1 hδ0 hδ1 hr0 hr0R a hK hc hb1 hb2 horc hLne hl hw'
  rw [← mul_assoc]; exact h2

end AdversarialBco.Matched
