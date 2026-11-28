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
lemmas only, `log_R0_le` (through (N1)) and (R2-K); every other use passes it on. This module proves their
generalizations and the parameters of the chain above them under `R0 ≤ d · kRipe d`, beside the old theorems (no
frozen statement and no existing declaration changes):

* `log_R0_le_ext`: `ln R0 ≤ Γ/5 + ln k` (from `R0 ≤ d k` and `5 ln d ≤ Γ`, `Γ = ln(n/d^5)`).
* `log_x_ripe_ge_Kext`: (N1), `ln(X_K/2) ≥ Γ/2`, from that bound (the old proof with `R0 ≤ k e^{Γ/5}` in place of
  `R0 ≤ e^{Γ/5}`; the factor `k²` is absorbed by the `k⁴` of `X_K`).
* `R2_ripe_Kext`: (R2-K) with `R0 ≤ d k`: `6.4·10⁻⁵ d^7 Γ ≤ k² n` replaces `≤ k⁴ n`.
* `ripeK_params_ext`: the parameters of Corollary RIPE-K-B with `hRk : R0 ≤ d * kRipe d` in place of `hRd : R0 ≤ d`,
  proof copied with the two lemmas swapped.
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

end AdversarialBco.Lower

