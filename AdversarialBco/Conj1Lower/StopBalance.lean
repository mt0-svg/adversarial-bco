/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Conj1Lower.BalanceK

@[expose] public section

/-!
# The stopped balance of Proposition STOP

Proposition STOP, the stopped balance: the per-round inequalities of the balance integrated over the stopped live
events `S'_t = S_t ∩ E_t` (`E_t`: the observed cumulative `Σ_{s < t} (o_s - b)` stayed at most `x` up to round `t`),
the ledger and the count telescoped to the stopping time, the stopped regret bounded by `Y`. Pure arithmetic on reals,
beside `GameFacts` and `ripe_balance` of Balance.lean.

* `StopFacts`: the fields of `GameFacts` over the stopped events, with `live` replaced by `1 - p - q ≤ l'_t` (`p` the
  probability that the posterior at the stopping time is dead, `q` that the cumulative crosses `x`) and the field
  `regret`, `Σ_t D'_t ≤ Y`.
* `stop_balance`: `q ≥ 0.7 - (g/(σ² P_R)) Y/N* - (2Y/g + 12 N*/k)/(0.999 n)`.
* `stop_rate_K`: at the parameters of Corollary RIPE-K-B and `Y = 10⁻⁵ σ d^{3/2} (n Γ)^{1/2}/k`, `q ≥ 0.53`. The two
  steps that read `R0`, (R2-K) and (N1), are hypotheses, so that the lemma serves `R0 ≤ d` and `R0 ≤ d k` alike.
-/

open Finset

namespace AdversarialBco.Lower

/-- The expectations of the stopped game, round by round, `t ∈ range n`, each quantity times the indicator of the
stopped live event `S'_t`: `Jm t = E[J_t; S'_t]`, `Pm t = E[P'_t; S'_t]`, `am t = E[a_t; S'_t]`,
`Dm t = E[D_t; S'_t]`, `lm t = P(S'_t)`; `p` the probability that the posterior at the stopping time is dead, `q` the
probability that the observed cumulative crosses the threshold, `Y` the bound on the stopped regret. -/
structure StopFacts (dd k g σ B w : ℝ) (n : ℕ) (p q Y : ℝ) (Jm Pm am Dm lm : ℕ → ℝ) : Prop where
  /-- (F1), first inequality. -/
  round_J : ∀ t < n, Jm t ≤ (4 * (3 * Real.log dd + 1) + 8 * B) / k * Pm t + g / (σ ^ 2 * priceR dd k) * Dm t
  /-- (F1), second inequality. -/
  round_floor : ∀ t < n, g / 2 * (999 / 1000 * lm t - am t) ≤ Dm t
  /-- (F1), third inequality. -/
  round_mass : ∀ t < n, am t ≤ 4 / k * Pm t
  /-- (F4). -/
  live : ∀ t < n, 1 - p - q ≤ lm t
  /-- (F2). -/
  payment : ∑ t ∈ range n, Pm t ≤ ledgerR dd w
  /-- (F3). -/
  count : nStar dd w * p ≤ ∑ t ∈ range n, Jm t
  /-- (F5). -/
  regret : ∑ t ∈ range n, Dm t ≤ Y

/-- Proposition STOP, the consequence: `q ≥ 0.7 - c Y/N* - (2Y/g + 12 N*/k)/(0.999 n)`, `c = g/(σ² P_R)`. -/
theorem stop_balance {dd k g σ L B : ℝ} {n : ℕ} {p q Y : ℝ} {Jm Pm am Dm lm : ℕ → ℝ} (hk : 1 ≤ k) (hg : 0 < g)
    (hσ : 0 < σ) (hL : 0 < L) (hB : 0 ≤ B) (hR1 : 40 * (3 * Real.log dd + 1 + 2 * B) ≤ k) (hR1' : 2048 * k ≤ dd)
    (hR2 : g ≤ k * L / (40 * dd)) (hn : 0 < n)
    (h : StopFacts dd k g σ B (wStar dd k L g) n p q Y Jm Pm am Dm lm) :
    7 / 10 - g / (σ ^ 2 * priceR dd k) * Y / nStar dd (wStar dd k L g) -
      (2 * Y / g + 12 * nStar dd (wStar dd k L g) / k) / (999 / 1000 * n) ≤ q := by
  have hk0 : 0 < k := by linarith
  have hd0 : 0 < dd := by linarith
  have hlog : 0 ≤ Real.log dd := Real.log_nonneg (by linarith)
  have hd12 : 12288 ≤ dd := by nlinarith
  set w := wStar dd k L g with hw
  have hX : 16 ≤ xCount dd w := xCount_wStar_ge dd k L g hd0 hk0 hL hg hR2
  have hN : dd / 2 ≤ nStar dd w := nStar_half dd w hd12 (by linarith)
  have hN0 : 0 < nStar dd w := by linarith
  have hRL : ledgerR dd w ≤ 3 * nStar dd w := ledgerR_three dd w hd12 (by linarith)
  have hP : ∑ t ∈ range n, Pm t ≤ 3 * nStar dd w := h.payment.trans hRL
  set c1 := (4 * (3 * Real.log dd + 1) + 8 * B) / k with hc1
  set c := g / (σ ^ 2 * priceR dd k) with hc
  have hc1n : 0 ≤ c1 := by rw [hc1]; positivity
  have hc13 : 3 * c1 ≤ 3 / 10 := coef_R1 dd k B hk0 hR1
  have hPR : 0 < priceR dd k := by unfold priceR; positivity
  have hcpos : 0 < c := by rw [hc]; positivity
  have hJ : ∑ t ∈ range n, Jm t ≤ c1 * ∑ t ∈ range n, Pm t + c * ∑ t ∈ range n, Dm t := by
    rw [mul_sum, mul_sum, ← sum_add_distrib]
    exact sum_le_sum fun t ht => h.round_J t (mem_range.mp ht)
  have hF : ∑ t ∈ range n, g / 2 * (999 / 1000 * lm t - am t) ≤ ∑ t ∈ range n, Dm t :=
    sum_le_sum fun t ht => h.round_floor t (mem_range.mp ht)
  have hA : ∑ t ∈ range n, am t ≤ 4 / k * ∑ t ∈ range n, Pm t := by
    rw [mul_sum]
    exact sum_le_sum fun t ht => h.round_mass t (mem_range.mp ht)
  have hLv : (n : ℝ) * (1 - p - q) ≤ ∑ t ∈ range n, lm t := by
    rw [← (by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] :
      ∑ t ∈ range n, (1 - p - q) = (n : ℝ) * (1 - p - q))]
    exact Finset.sum_le_sum fun t ht => h.live t (Finset.mem_range.mp ht)
  -- the count: `p ≤ 0.3 + c Y/N*`
  have hp : p ≤ 3 / 10 + c * Y / nStar dd w := by
    have h1 : c1 * ∑ t ∈ range n, Pm t ≤ c1 * (3 * nStar dd w) := mul_le_mul_of_nonneg_left hP hc1n
    have h2 : c * ∑ t ∈ range n, Dm t ≤ c * Y := mul_le_mul_of_nonneg_left h.regret hcpos.le
    have h3 : nStar dd w * p ≤ 3 / 10 * nStar dd w + c * Y := by nlinarith [h.count]
    rw [show 3 / 10 + c * Y / nStar dd w = (3 / 10 * nStar dd w + c * Y) / nStar dd w by field_simp]
    rw [le_div_iff₀ hN0]
    linarith
  -- the floor: `0.999 n (1 - p - q) ≤ 2Y/g + 12 N*/k`
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hfl : 999 / 1000 * n * (1 - p - q) ≤ 2 * Y / g + 12 * nStar dd w / k := by
    rw [← mul_sum, sum_sub_distrib, ← mul_sum] at hF
    have h4 : ∑ t ∈ range n, am t ≤ 12 * nStar dd w / k := by
      calc ∑ t ∈ range n, am t ≤ 4 / k * ∑ t ∈ range n, Pm t := hA
        _ ≤ 4 / k * (3 * nStar dd w) := mul_le_mul_of_nonneg_left hP (by positivity)
        _ = 12 * nStar dd w / k := by ring
    have h5 : g / 2 * (999 / 1000 * n * (1 - p - q) - 12 * nStar dd w / k) ≤ Y := by
      refine le_trans ?_ (hF.trans h.regret)
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith
    have h6 : 999 / 1000 * n * (1 - p - q) - 12 * nStar dd w / k ≤ 2 * Y / g := by
      rw [le_div_iff₀ hg]
      linarith
    linarith
  have hq : 1 - p - q ≤ (2 * Y / g + 12 * nStar dd w / k) / (999 / 1000 * n) := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  have : c * Y / nStar dd w = g / (σ ^ 2 * priceR dd k) * Y / nStar dd w := rfl
  linarith

/-- `12 N*/k ≤ 10⁻⁶ n` at the parameters of the rate, from (N2). -/
theorem nStar_ripe_tiny (dd nn k Γ N : ℝ) (hk : 240 ≤ k) (hd : 491520 ≤ dd) (hΓ : 0 ≤ Γ)
    (hn : nn = dd ^ 5 * Real.exp Γ) (hN : N ≤ dd / 4 * (Γ + 4 * Real.log k + 118 / 10)) :
    12 * N / k ≤ 1 / 10 ^ 6 * nn := by
  have hk0 : 0 < k := by linarith
  have hd0 : 0 < dd := by linarith
  have hlk : Real.log k ≤ k := (Real.log_le_sub_one_of_pos hk0).trans (by linarith)
  have hE : Γ + 1 ≤ Real.exp Γ := by linarith [Real.add_one_le_exp Γ]
  have hE1 : 1 ≤ Real.exp Γ := Real.one_le_exp hΓ
  generalize Real.exp Γ = E at *
  -- `Γ + 4 ln k + 11.8 ≤ Γ + 5 k ≤ 5 k E`
  have hb : Γ + 4 * Real.log k + 118 / 10 ≤ 5 * k * E := by nlinarith
  have hN2 : N ≤ dd / 4 * (5 * k * E) := hN.trans (mul_le_mul_of_nonneg_left hb (by positivity))
  have hd4 : 10 ^ 8 ≤ dd ^ 4 := by
    have : (491520 : ℝ) ^ 4 ≤ dd ^ 4 := pow_le_pow_left₀ (by norm_num) hd 4
    nlinarith
  rw [div_le_iff₀ hk0, hn]
  have h0 : 0 ≤ dd * E * k := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hd4 h0]

/-- `c Y = 8.388744·10⁻³ d Γ` and `2Y/g = n/10` at `Y = 10⁻⁵ σ d^{3/2} (n Γ)^{1/2}/k`,
`g = 2·10⁻⁴ σ d^{3/2} Γ^{1/2}/(k n^{1/2})`. -/
theorem stop_Y_ids (dd nn k σ Γ g Y : ℝ) (hd : 0 < dd) (hk : 0 < k) (hσ : 0 < σ) (hn : 0 < nn) (hΓ : 0 < Γ)
    (hg : g = 2 / 10 ^ 4 * σ * (dd * Real.sqrt dd) * Real.sqrt Γ / (k * Real.sqrt nn))
    (hY : Y = 1 / 10 ^ 5 * σ * (dd * Real.sqrt dd) * Real.sqrt (nn * Γ) / k) :
    g / (σ ^ 2 * priceR dd k) * Y = 8388744 / 10 ^ 9 * dd * Γ ∧ 2 * Y / g = nn / 10 := by
  rw [hg, hY, Real.sqrt_mul hn.le]
  unfold priceR
  have hs := Real.sq_sqrt hd.le
  have hr := Real.sq_sqrt hn.le
  have hu := Real.sq_sqrt hΓ.le
  have hs0 := Real.sqrt_pos.mpr hd
  have hr0 := Real.sqrt_pos.mpr hn
  have hu0 := Real.sqrt_pos.mpr hΓ
  generalize Real.sqrt dd = s at *
  generalize Real.sqrt nn = r at *
  generalize Real.sqrt Γ = u at *
  subst hs hr hu
  constructor
  · field_simp
    ring
  · field_simp

/-- Proposition STOP at the parameters of Corollary RIPE-K-B with `Y = 10⁻⁵ σ d^{3/2} (n Γ)^{1/2}/k`: the
cumulative crosses the threshold with probability at least `0.53`. The two steps that read `R0`, (R2-K) and (N1),
are hypotheses. -/
theorem stop_rate_K {dd σ R0 : ℝ} {n : ℕ} {p q Y : ℝ} {Jm Pm am Dm lm : ℕ → ℝ} (hd1 : 1 ≤ dd) (hσ : 0 < σ)
    (hR : 1 ≤ R0) (hn4 : Real.exp 4 * dd ^ 5 ≤ n) (hd : 2048 * kRipe dd ≤ dd)
    (hR2 : gRipe dd n σ ≤ kRipe dd * (σ / R0) / (40 * dd))
    (hN1 : gamR dd n / 2 ≤ Real.log (kRipe dd ^ 4 * n / (4 / 10 ^ 6 * dd ^ 5 * gamR dd n) / R0 ^ 2 / 2))
    (hY : Y = 1 / 10 ^ 5 * σ * (dd * Real.sqrt dd) * Real.sqrt (n * gamR dd n) / kRipe dd)
    (h : StopFacts dd (kRipe dd) (gRipe dd n σ) σ (chanBK (σ / R0) R0 (gRipe dd n σ) σ)
      (wStar dd (kRipe dd) (σ / R0) (gRipe dd n σ)) n p q Y Jm Pm am Dm lm) :
    53 / 100 ≤ q := by
  obtain ⟨hk240, hd491⟩ := kRipe_ge dd hd1 hd
  have hd0 : 0 < dd := by linarith
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le (by positivity) hn4
  have hnN : 0 < n := by exact_mod_cast hn0
  have hR0 : 0 < R0 := by linarith
  have hΓ : 4 ≤ gamR dd n := gamR_ge dd n hd0 hn4
  have hg : 0 < gRipe dd n σ := gRipe_pos dd n σ hd1 hd hσ hn4
  have hgle : gRipe dd n σ ≤ σ / 81920 := gRipe_le dd n σ hd1 hd hσ hn4
  have hB := (chanBK_le_chanB σ R0 (gRipe dd n σ) hσ hR hg.le).trans (chanB_ripe σ (gRipe dd n σ) hσ hg.le hgle)
  have hB0 : 0 ≤ chanBK (σ / R0) R0 (gRipe dd n σ) σ := by unfold chanBK; positivity
  have hbal := stop_balance (by linarith) hg hσ (div_pos hσ hR0) hB0 (R1_ripe dd _ hB) hd hR2 hnN h
  set w := wStar dd (kRipe dd) (σ / R0) (gRipe dd n σ) with hw
  have hX : xCount dd w = kRipe dd ^ 4 * n / (4 / 10 ^ 6 * dd ^ 5 * gamR dd n) / R0 ^ 2 :=
    xCount_ripe_K dd n σ R0 hd0 (by linarith) hσ hn0 (by linarith) hR0
  have hd12 : 12288 ≤ dd := by linarith
  have hNge : 1248 / 10000 * dd * gamR dd n ≤ nStar dd w := by
    apply nStar_ripe_ge dd _ _ hd0 hΓ
    have h1 := nStar_ge_x dd w hd12
    rw [hX] at h1
    nlinarith
  have hNle : nStar dd w ≤ dd / 4 * (gamR dd n + 4 * Real.log (kRipe dd) + 118 / 10) := by
    have h1 := nStar_le_x dd w hd1
    have h2 := log_x_ripe_le_K dd n (kRipe dd) R0 (by linarith) hd0 hn0 (by linarith) hR
    rw [hX] at h1
    nlinarith
  have hN0 : 0 < nStar dd w := lt_of_lt_of_le (by positivity) hNge
  obtain ⟨hcY, h2Y⟩ := stop_Y_ids dd n (kRipe dd) σ (gamR dd n) (gRipe dd n σ) Y hd0 (by linarith) hσ hn0
    (by linarith) rfl hY
  have htiny := nStar_ripe_tiny dd n (kRipe dd) (gamR dd n) (nStar dd w) hk240 hd491 (by linarith)
    (n_eq_exp dd n hd0 hn0) hNle
  -- the three terms
  have t1 : gRipe dd n σ / (σ ^ 2 * priceR dd (kRipe dd)) * Y / nStar dd w ≤ 6722 / 100000 := by
    rw [hcY, div_le_iff₀ hN0]
    nlinarith
  have t2 : (2 * Y / gRipe dd n σ + 12 * nStar dd w / kRipe dd) / (999 / 1000 * n) ≤ 1002 / 10000 := by
    rw [h2Y, div_le_iff₀ (by positivity)]
    nlinarith
  linarith

end AdversarialBco.Lower
