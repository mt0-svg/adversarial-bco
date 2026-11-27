/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Conj1Lower.Main

@[expose] public section

/-!
# LOW-R0: the lower bound on a body for `1 ≤ R0 ≤ d (120 ln d + 68)`

Lemma R0-EXT (every body between two balls): Theorem RIPE-K's rate, Corollary RIPE-K-B and Theorem lowerbody
hold, with the same parameters and constants, for `1 ≤ R0 ≤ d k`, `k = kRipe d = 120 ln d + 68`, at `d ≥ 4·10^6` and
`n ≥ d^10`. In the Lean chain (Conj1Lower/BalanceK.lean and Top.lean) the hypothesis `R0 ≤ d` is read by two scalar
lemmas only, `log_R0_le` (through (N1), `log_x_ripe_ge_K`) and `R2_ripe_K`; every other use passes it on. This module
proves their generalizations and reruns the chain above them under `R0 ≤ d · kRipe d`, beside the old theorems (no
frozen statement and no existing declaration changes):

* `log_R0_le_ext`: `ln R0 ≤ Γ/5 + ln k` (from `R0 ≤ d k` and `5 ln d ≤ Γ`, `Γ = ln(n/d^5)`).
* `log_x_ripe_ge_Kext`: (N1), `ln(X_K/2) ≥ Γ/2`, from that bound (the old proof with `R0 ≤ k e^{Γ/5}` in place of
  `R0 ≤ e^{Γ/5}`; the factor `k²` is absorbed by the `k⁴` of `X_K`).
* `R2_ripe_Kext`: (R2-K) with `R0 ≤ d k`: `6.4·10⁻⁵ d^7 Γ ≤ k² n` replaces `≤ k⁴ n`.
* `ripe_rate_Kext`, `ripeK_params_ext`, `ripeK_balance_ext`, `Top.good_pK_ext`, `Top.gameFacts_ext`,
  `Top.lowerBody_of_inputs_ext`: the statements of BalanceK.lean and Top.lean with `hRk : R0 ≤ d * kRipe d` in place
  of `hRd : R0 ≤ d`, proofs copied with the two lemmas swapped.
-/

open MeasureTheory ProbabilityTheory Finset

namespace AdversarialBco.Lower

/-- `R0 ≤ d k ≤ k e^{Γ/5}` when `n ≥ d^10`: `ln R0 ≤ Γ/5 + ln k`. -/
theorem log_R0_le_ext (dd nn k R0 : ℝ) (hd : 1 ≤ dd) (hk : 0 < k) (hR : 0 < R0) (hRk : R0 ≤ dd * k)
    (hn : dd ^ 10 ≤ nn) : Real.log R0 ≤ gamR dd nn / 5 + Real.log k := by
  have hd0 : 0 < dd := by linarith
  have h5 := log_R0_le dd nn dd hd hd0 le_rfl hn
  have hdk : Real.log R0 ≤ Real.log (dd * k) := Real.log_le_log hR hRk
  rw [Real.log_mul hd0.ne' hk.ne'] at hdk
  linarith

/-- (N1) for `R0 ≤ k e^{Γ/5}`: `ln(X_K/2) ≥ Γ/2`. -/
theorem log_x_ripe_ge_Kext (dd nn k R0 : ℝ) (hk : 1 ≤ k) (hd : 0 < dd) (hn : 0 < nn) (hΓ : 0 < gamR dd nn)
    (hR : 0 < R0) (hRΓ : Real.log R0 ≤ gamR dd nn / 5 + Real.log k) :
    gamR dd nn / 2 ≤ Real.log (k ^ 4 * nn / (4 / 10 ^ 6 * dd ^ 5 * gamR dd nn) / R0 ^ 2 / 2) := by
  set Γ := gamR dd nn with hΓ_def
  have hk0 : 0 < k := by linarith
  have hpos_arg : 0 < k ^ 4 * nn / (4 / 10 ^ 6 * dd ^ 5 * Γ) / R0 ^ 2 / 2 := by positivity
  rw [Real.le_log_iff_exp_le hpos_arg, div_div, div_div, ← mul_assoc]
  have hDpos : 0 < (4 / ((10 : ℝ) ^ 6) * dd ^ 5 * Γ) * R0 ^ 2 * 2 := by positivity
  apply (le_div_iff₀ hDpos).mpr
  have h_exp_Gamma : Real.exp Γ = nn / dd ^ 5 := by
    rw [hΓ_def, gamR]
    exact Real.exp_log (div_pos hn (pow_pos hd 5))
  have hn_eq : nn = dd ^ 5 * Real.exp Γ := by
    rw [h_exp_Gamma]
    field_simp
  rw [hn_eq]
  have hGamma_bound : 8 / ((10 : ℝ) ^ 6) * Γ ≤ Real.exp (Γ / 10) := by
    have := Real.add_one_le_exp (Γ / 10)
    nlinarith
  have hR0_le : R0 ≤ k * Real.exp (Γ / 5) := by
    calc R0 = Real.exp (Real.log R0) := (Real.exp_log hR).symm
      _ ≤ Real.exp (Γ / 5 + Real.log k) := Real.exp_le_exp.mpr hRΓ
      _ = k * Real.exp (Γ / 5) := by rw [Real.exp_add, Real.exp_log hk0, mul_comm]
  have h2 : Real.exp (Γ / 5) ^ 2 = Real.exp (2 * Γ / 5) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hR0_sq_le : R0 ^ 2 ≤ k ^ 2 * Real.exp (2 * Γ / 5) := by
    rw [← h2, ← mul_pow]
    exact pow_le_pow_left₀ hR.le hR0_le 2
  have hk2 : k ^ 2 ≤ k ^ 4 := pow_le_pow_right₀ hk (by norm_num)
  have hE : Real.exp (Γ / 2) * (Real.exp (Γ / 10) * Real.exp (2 * Γ / 5)) = Real.exp Γ := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hEpos := Real.exp_pos Γ
  calc Real.exp (Γ / 2) * ((4 / ((10 : ℝ) ^ 6) * dd ^ 5 * Γ) * R0 ^ 2 * 2)
      = dd ^ 5 * (Real.exp (Γ / 2) * ((8 / ((10 : ℝ) ^ 6) * Γ) * R0 ^ 2)) := by ring
    _ ≤ dd ^ 5 * (Real.exp (Γ / 2) * (Real.exp (Γ / 10) * (k ^ 2 * Real.exp (2 * Γ / 5)))) := by
      gcongr
    _ = k ^ 2 * (dd ^ 5 * (Real.exp (Γ / 2) * (Real.exp (Γ / 10) * Real.exp (2 * Γ / 5)))) := by ring
    _ = k ^ 2 * (dd ^ 5 * Real.exp Γ) := by rw [hE]
    _ ≤ k ^ 4 * (dd ^ 5 * Real.exp Γ) := by gcongr

/-- (R2-K) at the rate's parameters: `g ≤ k (σ/R0)/(40 d)` for `1 ≤ R0 ≤ d k` and `n ≥ d^10`. -/
theorem R2_ripe_Kext (dd nn σ R0 : ℝ) (hd1 : 1 ≤ dd) (hd : 2048 * kRipe dd ≤ dd) (hσ : 0 < σ) (hR : 1 ≤ R0)
    (hRk : R0 ≤ dd * kRipe dd) (hn : dd ^ 10 ≤ nn) : gRipe dd nn σ ≤ kRipe dd * (σ / R0) / (40 * dd) := by
  obtain ⟨hk, -⟩ := kRipe_ge dd hd1 hd
  have hk0 : 0 < kRipe dd := by linarith
  have hd0 : 0 < dd := by linarith
  have hR0 : 0 < R0 := by linarith
  have hn0 : 0 < nn := lt_of_lt_of_le (by positivity) hn
  have hnE := n_eq_exp dd nn hd0 hn0
  have h10 : dd ^ 5 * dd ^ 5 ≤ dd ^ 5 * Real.exp (gamR dd nn) := by
    rw [← hnE]
    calc dd ^ 5 * dd ^ 5 = dd ^ 10 := by ring
      _ ≤ nn := hn
  have hE5 : dd ^ 5 ≤ Real.exp (gamR dd nn) := le_of_mul_le_mul_left h10 (by positivity)
  have hd45 : dd ^ 2 * dd ^ 2 ≤ dd ^ 5 := by
    calc dd ^ 2 * dd ^ 2 = dd ^ 4 := by ring
      _ ≤ dd ^ 5 := pow_le_pow_right₀ hd1 (by norm_num)
  have hΓ0 : 0 ≤ gamR dd nn := Real.one_le_exp_iff.mp ((one_le_pow₀ hd1).trans hE5)
  have hEE : Real.exp (gamR dd nn) = Real.exp (gamR dd nn / 2) * Real.exp (gamR dd nn / 2) := by
    rw [← Real.exp_add]; ring_nf
  have hE0 := Real.exp_pos (gamR dd nn / 2)
  have hEd : dd ^ 2 ≤ Real.exp (gamR dd nn / 2) := by
    by_contra h
    replace h := not_le.mp h
    have := mul_lt_mul'' h h hE0.le hE0.le
    linarith
  have hEΓ : gamR dd nn / 2 ≤ Real.exp (gamR dd nn / 2) := by linarith [Real.add_one_le_exp (gamR dd nn / 2)]
  have hexp : dd ^ 2 * (gamR dd nn / 2) ≤ Real.exp (gamR dd nn) := by
    rw [hEE]; exact mul_le_mul hEd hEΓ (by positivity) hE0.le
  have hk1 : 1 ≤ kRipe dd ^ 2 := one_le_pow₀ (by linarith)
  have key : 64 / 10 ^ 6 * dd ^ 7 * gamR dd nn ≤ kRipe dd ^ 2 * nn := by
    have h1 : dd ^ 5 * (dd ^ 2 * (gamR dd nn / 2)) ≤ dd ^ 5 * Real.exp (gamR dd nn) :=
      mul_le_mul_of_nonneg_left hexp (by positivity)
    have h2 : dd ^ 5 * Real.exp (gamR dd nn) ≤ kRipe dd ^ 2 * (dd ^ 5 * Real.exp (gamR dd nn)) :=
      le_mul_of_one_le_left (by positivity) hk1
    have h3 : 64 / 10 ^ 6 * dd ^ 7 * gamR dd nn ≤ dd ^ 5 * (dd ^ 2 * (gamR dd nn / 2)) := by
      have : 0 ≤ dd ^ 7 * gamR dd nn := by positivity
      nlinarith
    rw [← hnE] at h2
    linarith
  unfold gRipe
  generalize kRipe dd = k at *
  generalize gamR dd nn = Γ at *
  have hs := Real.sq_sqrt hd0.le
  have hr := Real.sq_sqrt hn0.le
  have hu := Real.sq_sqrt hΓ0
  have hs0 := Real.sqrt_pos.mpr hd0
  have hr0 := Real.sqrt_pos.mpr hn0
  have hu0 := Real.sqrt_nonneg Γ
  generalize Real.sqrt dd = s at *
  generalize Real.sqrt nn = r at *
  generalize Real.sqrt Γ = u at *
  subst hs hr hu
  have hsq : 8 / 10 ^ 3 * s ^ 7 * u ≤ k * r := by
    have : (8 / 10 ^ 3 * s ^ 7 * u) ^ 2 ≤ (k * r) ^ 2 := by nlinarith
    exact (sq_le_sq₀ (by positivity) (by positivity)).mp this
  have hRs : s ^ 5 * u * R0 ≤ s ^ 7 * u * k := by
    have := mul_le_mul_of_nonneg_left hRk (by positivity : (0 : ℝ) ≤ s ^ 5 * u)
    nlinarith
  rw [mul_div_assoc', div_div, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left hsq (by positivity : (0 : ℝ) ≤ σ * k), mul_le_mul_of_nonneg_left hRs hσ.le]

/-- Theorem RIPE-K, the rate: `E R_n ≥ 2.5·10⁻⁵ σ d^{3/2} (n ln(n/d⁵))^{1/2}/(120 ln d + 68)` for the strategy with
`L_K = σ/R0`, `σ ≤ 1/4`, `1 ≤ R0 ≤ d k`, `n ≥ d^10` and `d ≥ 2048 (120 ln d + 68)`. -/
theorem ripe_rate_Kext {dd σ R0 : ℝ} {n : ℕ} {p : ℝ} {Jm Pm am Dm lm : ℕ → ℝ} (hd1 : 1 ≤ dd) (hσ : 0 < σ)
    (hσ' : σ ≤ 1 / 4) (hR : 1 ≤ R0) (hRk : R0 ≤ dd * kRipe dd) (hn : dd ^ 10 ≤ n) (hn4 : Real.exp 4 * dd ^ 5 ≤ n)
    (hd : 2048 * kRipe dd ≤ dd)
    (h : GameFacts dd (kRipe dd) (gRipe dd n σ) σ (chanBK (σ / R0) R0 (gRipe dd n σ) σ)
      (wStar dd (kRipe dd) (σ / R0) (gRipe dd n σ)) n p Jm Pm am Dm lm) :
    25 / 10 ^ 6 * σ * (dd * Real.sqrt dd) * Real.sqrt (n * gamR dd n) / kRipe dd ≤ ∑ t ∈ range n, Dm t := by
  obtain ⟨hk240, hd491⟩ := kRipe_ge dd hd1 hd
  have hd0 : 0 < dd := by linarith
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le (by positivity) hn4
  have hR0 : 0 < R0 := by linarith
  have hΓ : 4 ≤ gamR dd n := gamR_ge dd n hd0 hn4
  have hg : 0 < gRipe dd n σ := gRipe_pos dd n σ hd1 hd hσ hn4
  have hgle : gRipe dd n σ ≤ σ / 81920 := gRipe_le dd n σ hd1 hd hσ hn4
  have hB := (chanBK_le_chanB σ R0 (gRipe dd n σ) hσ hR hg.le).trans (chanB_ripe σ (gRipe dd n σ) hσ hg.le hgle)
  have hB0 : 0 ≤ chanBK (σ / R0) R0 (gRipe dd n σ) σ := by unfold chanBK; positivity
  obtain ⟨hhi, hlo⟩ := ripe_balance (by linarith) hg hσ (div_pos hσ hR0) hB0 (R1_ripe dd _ hB) hd
    (R2_ripe_Kext dd n σ R0 hd1 hd hσ hR hRk hn) h
  set w := wStar dd (kRipe dd) (σ / R0) (gRipe dd n σ) with hw
  have hX : xCount dd w = kRipe dd ^ 4 * n / (4 / 10 ^ 6 * dd ^ 5 * gamR dd n) / R0 ^ 2 :=
    xCount_ripe_K dd n σ R0 hd0 (by linarith) hσ hn0 (by linarith) hR0
  have hd12 : 12288 ≤ dd := by linarith
  have hNge : 1248 / 10000 * dd * gamR dd n ≤ nStar dd w := by
    apply nStar_ripe_ge dd _ _ hd0 hΓ
    have h1 := nStar_ge_x dd w hd12
    have h2 := log_x_ripe_ge_Kext dd n (kRipe dd) R0 (by linarith) hd0 hn0 (by linarith) hR0
      (log_R0_le_ext dd n (kRipe dd) R0 hd1 (by linarith) hR0 hRk hn)
    rw [hX] at h1
    nlinarith
  have hNle : nStar dd w ≤ dd / 4 * (gamR dd n + 4 * Real.log (kRipe dd) + 118 / 10) := by
    have h1 := nStar_le_x dd w hd1
    have h2 := log_x_ripe_le_K dd n (kRipe dd) R0 (by linarith) hd0 hn0 (by linarith) hR
    rw [hX] at h1
    nlinarith
  by_cases hp : 1 / 2 ≤ p
  · exact (rate_hi dd n (kRipe dd) σ (gamR dd n) (gRipe dd n σ) (nStar dd w) p hd0 (by linarith) hσ hn0
      (by linarith) rfl hNge hp).trans hhi
  · rw [not_le] at hp
    have hsmall := nStar_ripe_small dd n (kRipe dd) (gamR dd n) (nStar dd w) hk240 (by linarith) hd491 hΓ
      (n_eq_exp dd n hd0 hn0) hNle
    exact (rate_lo dd n (kRipe dd) σ (gamR dd n) (gRipe dd n σ) (nStar dd w) p hd0 (by linarith) hσ hn0
      (by linarith) rfl hsmall hp).trans hlo

/-- The parameters of Corollary RIPE-K-B: `L_K = σ/R0 ∈ (0, 1/4]`, the range `L_K (R0 + 1/2) + g ≤ 1/2` (Lemma
LEGAL-K), `X_K ≥ 16` at the floor (Lemma COUNT). -/
theorem ripeK_params_ext {d n : ℕ} {R0 : ℝ} (hd : 4000000 ≤ d) (hn : d ^ 10 ≤ n) (hR : 1 ≤ R0) (hRk : R0 ≤ d * kRipe d) :
    0 < sigB n / R0 ∧ sigB n / R0 ≤ 1 / 4 ∧ sigB n / R0 * (R0 + 1 / 2) + gRipe d n (sigB n) ≤ 1 / 2 ∧
      16 ≤ xCount d (wStar d (kRipe d) (sigB n / R0) (gRipe d n (sigB n))) := by
  have h := ripeB_params hd hn
  rcases h with ⟨hσpos, hσle, hgpos, hgle, hsum, hkge, hkd, hxcount, hchan, hkbound, hexp⟩
  have hR0pos : 0 < R0 := by linarith
  have hdpos : 0 < (d : ℝ) := by
    have : (0 : ℕ) < d := by omega
    exact_mod_cast this
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by
    have : (1 : ℕ) ≤ d := by omega
    exact_mod_cast this
  have h1 : 0 < sigB n / R0 := div_pos hσpos hR0pos
  have h2 : sigB n / R0 ≤ 1 / 4 := by
    calc
      sigB n / R0 ≤ sigB n := div_le_self hσpos.le hR
      _ ≤ 1 / 4 := hσle
  have h3 : sigB n / R0 * (R0 + 1 / 2) + gRipe d n (sigB n) ≤ 1 / 2 := by
    apply rangeK_le (sigB n) R0 (gRipe d n (sigB n)) hσpos.le hR hsum
  have hR2 : gRipe (d : ℝ) (n : ℝ) (sigB n) ≤ kRipe (d : ℝ) * (sigB n / R0) / (40 * (d : ℝ)) := by
    apply R2_ripe_Kext (d : ℝ) (n : ℝ) (sigB n) R0 hd1 hkd hσpos hR hRk
    exact_mod_cast hn
  have hkRipe_pos : 0 < kRipe (d : ℝ) := by
    have hlog : 0 ≤ Real.log (d : ℝ) := Real.log_nonneg hd1
    nlinarith
  have h4 : 16 ≤ xCount d (wStar d (kRipe d) (sigB n / R0) (gRipe d n (sigB n))) := by
    apply xCount_wStar_ge (d : ℝ) (kRipe (d : ℝ)) (sigB n / R0) (gRipe (d : ℝ) (n : ℝ) (sigB n))
    · exact hdpos
    · exact hkRipe_pos
    · exact div_pos hσpos hR0pos
    · exact hgpos
    · simpa using hR2
  exact ⟨h1, h2, h3, h4⟩

/-- Corollary RIPE-K-B, the arithmetic, in the form of `TheoremConj1LowerPoly`: the expectations of the Gaussian game
with `L_K = σ/R0` satisfy `GameFacts`, and the bounded game's mean regret `ER` is at least the Gaussian one minus
`1/n`; then `ER ≥ 7·10⁻⁹ d^{3/2} n^{1/2}/ln d`. -/
theorem ripeK_balance_ext {d n : ℕ} {R0 : ℝ} (hd : 4000000 ≤ d) (hn : d ^ 10 ≤ n) (hR : 1 ≤ R0) (hRk : R0 ≤ d * kRipe d)
    {p : ℝ} {Jm Pm am Dm lm : ℕ → ℝ}
    (h : GameFacts d (kRipe d) (gRipe d n (sigB n)) (sigB n)
      (chanBK (sigB n / R0) R0 (gRipe d n (sigB n)) (sigB n))
      (wStar d (kRipe d) (sigB n / R0) (gRipe d n (sigB n))) n p Jm Pm am Dm lm)
    {ER : ℝ} (hER : ∑ t ∈ range n, Dm t - 1 / n ≤ ER) :
    7 / 10 ^ 9 * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n / Real.log d ≤ ER := by
  have hdR : (4000000 : ℝ) ≤ d := by exact_mod_cast hd
  have hnR : (d : ℝ) ^ 10 ≤ n := by exact_mod_cast hn
  obtain ⟨hs0, hs4⟩ := ripeB_sig d n hdR hnR
  have hdim := ripeB_dim d hdR
  have hd1 : (1 : ℝ) ≤ d := by linarith
  have hn4 := ripeB_n d n hdR hnR
  have hrate := ripe_rate_Kext hd1 hs0 hs4 hR hRk hnR hn4 hdim h
  obtain ⟨hk240, -⟩ := kRipe_ge d hd1 hdim
  have hn1 : (1 : ℝ) < n := by
    have : (1 : ℝ) < (d : ℝ) ^ 10 := one_lt_pow₀ (by linarith) (by norm_num)
    linarith
  have hcoef := ripeB_coef n (gamR d n) hn1 (ripeB_gam d n hd1 hnR)
  have hfin := ripeB_final d n hdR hnR
  rw [rpow_three_halves d (by linarith)]
  have hdd : 0 ≤ (d : ℝ) * Real.sqrt d := by positivity
  have h1 : 9 / 10 ^ 7 * ((d : ℝ) * Real.sqrt d) * Real.sqrt n / kRipe d ≤ ∑ t ∈ range n, Dm t := by
    refine le_trans ?_ hrate
    rw [div_le_div_iff_of_pos_right (by linarith)]
    have h2 : 9 / 10 ^ 7 * Real.sqrt n ≤ 25 / 10 ^ 6 * sigB n * Real.sqrt (n * gamR d n) :=
      le_trans (by nlinarith [Real.sqrt_nonneg (n : ℝ)]) hcoef
    nlinarith [mul_le_mul_of_nonneg_left h2 hdd]
  linarith

end AdversarialBco.Lower

namespace AdversarialBco.Lower.Top

open RealRAM Bayes

theorem good_pK_ext {d n : ℕ} {R0 : ℝ} (hd : 4000000 ≤ d) (hn : d ^ 10 ≤ n) (hR : 1 ≤ R0)
    (hRk : R0 ≤ d * kRipe d) : Good (pK d n R0) d R0 := by
  obtain ⟨h1, -, h3, -, -, h6, h7, -⟩ := ripeB_params hd hn
  obtain ⟨k1, k2, k3, -⟩ := ripeK_params_ext hd hn hR hRk
  exact ⟨h3, h6, k1, h1, k2, h7, k3, rfl⟩

section Game

variable {d : ℕ} {R0 : ℝ} {Ω : Type} [MeasurableSpace Ω]

/-- `GameFacts` at the parameters of Corollary RIPE-K-B, for plays in `B(0, R0)`. -/
theorem gameFacts_ext (I : Inputs) {n : ℕ} (hd : 4000000 ≤ d) (hn : d ^ 10 ≤ n) (hR1 : 1 ≤ R0) (hRk : R0 ≤ d * kRipe d)
    (μ : Measure Ω) [IsProbabilityMeasure μ] {pol : Learner Ω d} (hpol : IsLearnerAd (Metric.closedBall 0 R0) n pol) :
    GameFacts d (kRipe d) (gRipe d n (sigB n)) (sigB n) (chanBK (sigB n / R0) R0 (gRipe d n (sigB n)) (sigB n))
      (wStar d (kRipe d) (sigB n / R0) (gRipe d n (sigB n))) n
      ((gameLaw (prior d (1 / 2)) μ).real (liveSet (pK d n R0) pol n)ᶜ)
      (fun t => ∫ s in liveSet (pK d n R0) pol t, Jf (pK d n R0) pol t s ∂gameLaw (prior d (1 / 2)) μ)
      (fun t => ∫ s in liveSet (pK d n R0) pol t, Pf (pK d n R0) pol t s ∂gameLaw (prior d (1 / 2)) μ)
      (fun t => ∫ s in liveSet (pK d n R0) pol t, af (pK d n R0) pol t s ∂gameLaw (prior d (1 / 2)) μ)
      (fun t => ∫ s in liveSet (pK d n R0) pol t, Df (pK d n R0) pol t s ∂gameLaw (prior d (1 / 2)) μ)
      (fun t => (gameLaw (prior d (1 / 2)) μ).real (liveSet (pK d n R0) pol t)) := by
  have hP := good_pK_ext hd hn hR1 hRk
  have hG : IsProbabilityMeasure (gameLaw (prior d (1 / 2)) μ) := isProbabilityMeasure_gameLaw _ μ
  have hpol' : ∀ t < n, Measurable fun p : Ω × (Fin t → E d) × (Fin t → ℝ) => pol t p.1 p.2.1 p.2.2 :=
    fun t ht => (hpol t ht).1
  have hR := ruleS_meas_prior hP
  have hsc : (pK d n R0).sc ≠ 0 := hP.sc_pos.ne'
  have hS₀ : ∀ t < n, ∀ h θ ω, |(ruleS d (pK d n R0)).sig (post (prior d (1 / 2)) (ruleS d (pK d n R0)) (pK d n R0).sc t h)
      (play pol t ω h) θ| ≤ 1 := fun t ht h θ ω => abs_sig_post_le I hP t h ((hpol t ht).2 _ _ _) θ
  have hk : 0 < (pK d n R0).k := by linarith [hP.k_ge]
  have hB : 0 ≤ chanBK (pK d n R0).L R0 (pK d n R0).g (pK d n R0).sc := by unfold chanBK; positivity
  have hLedger := I.ledger_game hP.d_pos (show (0 : ℝ) < 1 / 2 by norm_num) μ (ruleS d (pK d n R0)) hR hsc hpol'
    hP.w_pos.ne'
  have hJi : ∀ t < n, Integrable (Jf (pK d n R0) pol t) (gameLaw (prior d (1 / 2)) μ) := fun t ht =>
    I.integrable_infoRound (prior d (1 / 2)) μ (ruleS d (pK d n R0)) hR hsc hpol' hS₀ ht
  have hPi : ∀ t < n, Integrable (Pf (pK d n R0) pol t) (gameLaw (prior d (1 / 2)) μ) := fun t ht =>
    hLedger.1 t ht
  have hai : ∀ t < n, Integrable (af (pK d n R0) pol t) (gameLaw (prior d (1 / 2)) μ) := fun t ht =>
    (integrable_const (1 : ℝ)).mono' (measurable_af hP hpol ht).aestronglyMeasurable
      (ae_of_all _ fun s => by
        obtain ⟨h0, h1⟩ := af_mem hP pol t s
        rw [Real.norm_eq_abs, abs_le]
        constructor <;> linarith)
  have hDi : ∀ t < n, Integrable (Df (pK d n R0) pol t) (gameLaw (prior d (1 / 2)) μ) := fun t ht =>
    (integrable_const (1 : ℝ)).mono' (measurable_Df hP hpol ht).aestronglyMeasurable
      (ae_of_all _ fun s => by
        obtain ⟨h0, h1⟩ := Df_mem I hP hpol ht s
        rw [Real.norm_eq_abs, abs_le]
        constructor <;> linarith)
  have hround : ∀ t < n, _ := fun t ht =>
    round_integral (gameLaw (prior d (1 / 2)) μ) (liveSet (pK d n R0) pol t) (measurableSet_liveSet hP hpol ht.le)
      ((4 * (3 * Real.log d + 1) + 8 * chanBK (pK d n R0).L R0 (pK d n R0).g (pK d n R0).sc) / (pK d n R0).k)
      ((pK d n R0).g / ((pK d n R0).sc ^ 2 * priceR d (pK d n R0).k)) (pK d n R0).g (pK d n R0).k
      (Jf (pK d n R0) pol t) (Pf (pK d n R0) pol t) (af (pK d n R0) pol t) (Df (pK d n R0) pol t)
      (hJi t ht) (hPi t ht) (hai t ht) (hDi t ht) fun s hs => by
        obtain ⟨pr, H, Iann, Irest, Drest, preg, hRF⟩ := roundFacts_at I hP hpol ht hs
        exact round_bound hk hP.dim hP.g_pos.le hB hRF
  have hlive := measurableSet_liveSet hP hpol (le_refl n)
  have hX : Real.exp 1 / 2 ≤ xCount d ((pK d n R0).w d) := by
    have h16 := (ripeK_params_ext hd hn hR1 hRk).2.2.2
    have := Real.exp_one_lt_three
    exact le_trans (by linarith) h16
  refine
    { round_J := fun t ht => (hround t ht).1
      round_floor := fun t ht => (hround t ht).2.1
      round_mass := fun t ht => (hround t ht).2.2
      live := fun t ht => ?_
      payment := ?_
      count := ?_ }
  · rw [probReal_compl_eq_one_sub hlive, sub_sub_cancel]
    exact measureReal_mono (liveSet_anti hP pol ht.le)
  · have he : ∀ t ∈ Finset.range n, ∫ s in liveSet (pK d n R0) pol t, Pf (pK d n R0) pol t s ∂gameLaw (prior d (1 / 2)) μ =
        ∫ s, Pf (pK d n R0) pol t s ∂gameLaw (prior d (1 / 2)) μ := fun t _ =>
      setIntegral_eq_integral_of_forall_compl_eq_zero fun s hs => Pf_dead I pol t hs
    rw [Finset.sum_congr rfl he]
    exact hLedger.2
  · have hset : {s : Sample d Ω | dLive ((pK d n R0).w d) (covM (post (prior d (1 / 2)) (ruleS d (pK d n R0)) (pK d n R0).sc n
        (hist (prior d (1 / 2)) (ruleS d (pK d n R0)) (pK d n R0).sc pol n s))) < d / 2} = (liveSet (pK d n R0) pol n)ᶜ := by
      ext s
      exact (not_le (α := ℝ)).symm
    have hJ : ∀ t ∈ Finset.range n, ∫ s in liveSet (pK d n R0) pol t, Jf (pK d n R0) pol t s ∂gameLaw (prior d (1 / 2)) μ =
        ∫ s, infoRound (prior d (1 / 2)) (ruleS d (pK d n R0)) (pK d n R0).sc pol t s ∂gameLaw (prior d (1 / 2)) μ :=
      fun t _ => setIntegral_eq_integral_of_forall_compl_eq_zero fun s hs => Jf_dead I hP pol t hs
    rw [Finset.sum_congr rfl hJ, ← hset]
    exact I.count_game (by have := hP.d_pos; omega) μ (ruleS d (pK d n R0)) hR hsc hpol' hS₀ hP.w_pos hX

end Game

section Compose

variable {d : ℕ} {R0 : ℝ} {Ω : Type} [MeasurableSpace Ω]

/-- The lower bound on a body (Corollary RIPE-K-B, deterministic form): on a convex `K` with
`B(0, 1/2) ⊆ K ⊆ B(0, R0)`, `1 ≤ R0 ≤ d k` (`k = 120 ln d + 68`), for `d ≥ 4·10^6` and `n ≥ d^10`, every learner of `IsLearnerAd K n` meets a
strategy of `StratsLip K n` against which its regret is integrable with mean at least `7·10^-9 d^{3/2} n^{1/2}/log d`;
from the statements `Inputs`, which Main.lean discharges (`lowerTopInputs`). -/
theorem lowerBody_of_inputs_ext (I : Inputs) {n : ℕ} (hd : 4000000 ≤ d) (hn : d ^ 10 ≤ n) {K : Set (E d)}
    (hK : Convex ℝ K) (hK1 : Metric.closedBall (0 : E d) (1 / 2) ⊆ K) (hK2 : K ⊆ Metric.closedBall 0 R0)
    (hR1 : 1 ≤ R0) (hRk : R0 ≤ d * kRipe d) (μ : Measure Ω) [IsProbabilityMeasure μ] {pol : Learner Ω d}
    (hpol : IsLearnerAd K n pol) :
    ∃ σ ∈ StratsLip K n, Integrable (fun ω => regretAd K σ (fun t => pol t ω) n) μ ∧
      7 / 10 ^ 9 * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n / Real.log d ≤
        ∫ ω, regretAd K σ (fun t => pol t ω) n ∂μ := by
  have hP := good_pK_ext hd hn hR1 hRk
  have hpolB : IsLearnerAd (Metric.closedBall 0 R0) n pol := fun t ht =>
    ⟨(hpol t ht).1, fun ω x o => hK2 ((hpol t ht).2 ω x o)⟩
  have hn1 : 1 < n := by
    have h1 : 1 < d ^ 10 := Nat.one_lt_pow (by norm_num) (by omega)
    omega
  have hbal := ripeK_balance_ext hd hn hR1 hRk (gameFacts_ext I hd hn hR1 hRk μ hpolB)
    (ER := ∫ s, regG (prior d (1 / 2)) (pK d n R0) pol n (s.1, clampZ (ellB n) s.2.1, s.2.2)
      ∂gameLaw (prior d (1 / 2)) μ)
    (by rw [sum_Df_eq I hP μ hpolB]; exact coupling I hP μ hn1 hpolB)
  rw [integral_gameLaw_assoc (prior d (1 / 2)) μ
    (fun s => regG (prior d (1 / 2)) (pK d n R0) pol n (s.1, clampZ (ellB n) s.2.1, s.2.2))] at hbal
  have hm : Measurable fun p : (E d × (ℕ → ℝ)) × Ω =>
      regG (prior d (1 / 2)) (pK d n R0) pol n (p.1.1, clampZ (ellB n) p.1.2, p.2) :=
    (measurable_regG hP hpolB).comp ((measurable_fst.comp measurable_fst).prodMk
      (((measurable_clampZ _).comp (measurable_snd.comp measurable_fst)).prodMk measurable_snd))
  have hb : ∀ p : (E d × (ℕ → ℝ)) × Ω,
      |regG (prior d (1 / 2)) (pK d n R0) pol n (p.1.1, clampZ (ellB n) p.1.2, p.2)| ≤ n / 2 := fun p =>
    abs_le.2 ⟨by linarith [regG_nonneg hP (prior d (1 / 2)) pol n (p.1.1, clampZ (ellB n) p.1.2, p.2),
      (by positivity : (0 : ℝ) ≤ n / 2)], regG_le I hP hpolB _⟩
  have hN : ((prior d (1 / 2)).prod gaussStream)
      {a : E d × (ℕ → ℝ) | a.1 ∉ Metric.closedBall (0 : E d) (1 / 2)} = 0 := by
    have h0 := ae_iff.1 (prior_ae_mem d (1 / 2))
    have hs : {a : E d × (ℕ → ℝ) | a.1 ∉ Metric.closedBall (0 : E d) (1 / 2)} =
        {θ | θ ∉ Metric.closedBall (0 : E d) (1 / 2)} ×ˢ Set.univ := by
      ext a
      simp
    rw [hs, Measure.prod_prod, h0, zero_mul]
  obtain ⟨a, haN, ha⟩ := exists_good_point ((prior d (1 / 2)).prod gaussStream) μ hm hb hN
  have ha1 : a.1 ∈ Metric.closedBall (0 : E d) (1 / 2) := by
    by_contra h
    exact haN h
  have hxo : a.1 ∈ K := hK1 ha1
  have hℓ : 0 ≤ ellB n := Real.sqrt_nonneg _
  have hz : ∀ i, |(pK d n R0).sc * clampZ (ellB n) a.2 i| ≤ 1 / 8 := fun i => by
    rw [abs_mul, abs_of_pos hP.sc_pos, ← sigB_mul_ellB hn1]
    exact mul_le_mul_of_nonneg_left (abs_clampZ_le hℓ a.2 i) hP.sc_pos.le
  have hσ := stratOf_mem I hP hK hK2 n a.1 (clampZ (ellB n) a.2) hz
  refine ⟨_, hσ, integrable_regretAd_stratOf I hP μ hpolB hxo _, ?_⟩
  have he : (fun ω => regretAd K
      (stratOf (prior d (1 / 2)) (ruleS d (pK d n R0)) (pK d n R0).sc a.1 (clampZ (ellB n) a.2))
        (fun t => pol t ω) n) =
      fun ω => regG (prior d (1 / 2)) (pK d n R0) pol n (a.1, clampZ (ellB n) a.2, ω) :=
    funext fun ω => regretAd_stratOf hP (prior d (1 / 2)) pol n hxo _ ω
  rw [he]
  exact hbal.trans ha

end Compose

end AdversarialBco.Lower.Top

