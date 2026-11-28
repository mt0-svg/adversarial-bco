/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.LowerDelta.Arith

@[expose] public section

/-!
# Theorem LU-DQ, the arithmetic

The parameters of Theorem LU-DQ with the failure `δ₀ = s²`, `0 < s`, `s² ≤ 1/2`, written with
`s` so that `δ₀^{3/2} = s³` needs no `rpow`: `k = k₀/(2 s²)` (the order `m k₀` at `m = 1/(2 δ₀)`),
`g = c_q s³ g₀` with `c_q = 1.0256` and `g₀ = gRipe d n σ` (that is `g = c_g σ d^{3/2} Γ^{1/2}/(k n^{1/2})` with
`c_g = 1.0256·10^-4 s`, a little below `1.0256289·10^-4 s`), the level `x = 0.99 n g` and `β = 1/4`. Pure
arithmetic on reals.

* `wStar_scaleQ`, `xCount_scaleQ`: the floor and the count under the scaling of `k` and `g`.
* `three_c1_le`: (R1) gives `3 c₁ ≤ 0.6 s²` (Step 2).
* `c2x_idQ`: `c₂ x = 4194372 · 0.99 · c_q² · 10^-8 s² d Γ ≤ 0.35 · 0.1248 s² d Γ` (Step 3).
* `k2_le`: (D3) `10 k₀ ≤ s³ d` gives `12 k²/d² ≤ 0.03 s²` (Step 4).
* `thr_idQ`: `(3/8) x = 7.425 c_q s³ Y₀` with `Y₀ = 10^-5 σ d^{3/2} (n Γ)^{1/2}/k₀` (Step 5).
* `fail_budgetQ`: the failure of Proposition Q-STOP and the clamp at most `s²` (Steps 6 and 7).
-/

open Finset

namespace AdversarialBco.LowerDeltaQ

open AdversarialBco.Lower AdversarialBco.LowerDelta

/-! ## Scaling -/

theorem wStar_scaleQ (dd k0 L g0 s : ℝ) (hs : 0 < s) :
    wStar dd (k0 / (2 * s ^ 2)) L (10256 / 10000 * s ^ 3 * g0) = 2 * (10256 / 10000) * s ^ 5 * wStar dd k0 L g0 := by
  unfold wStar
  have : s ≠ 0 := hs.ne'
  by_cases hk : k0 = 0
  · subst hk; simp
  field_simp

theorem xCount_scaleQ (dd w c : ℝ) : xCount dd (c * w) = xCount dd w / c ^ 2 := by
  unfold xCount
  by_cases hc : c = 0
  · subst hc; simp
  by_cases hw : w = 0
  · subst hw; simp
  by_cases hd : dd = 0
  · subst hd; simp
  field_simp

/-! ## The terms of the failure -/

/-- Step 2: (R1) at `k₀`, `40 (3 ln d + 1 + 2B) ≤ k₀`, gives `3 c₁ ≤ 0.6 s²` at `k = k₀/(2 s²)`. -/
theorem three_c1_le {dd k0 B s : ℝ} (hk0 : 0 < k0) (hs : 0 < s) (hR1 : 40 * (3 * Real.log dd + 1 + 2 * B) ≤ k0) :
    3 * ((4 * (3 * Real.log dd + 1) + 8 * B) / (k0 / (2 * s ^ 2))) ≤ 3 / 5 * s ^ 2 := by
  have hs2 : 0 < s ^ 2 := by positivity
  have e : 3 * ((4 * (3 * Real.log dd + 1) + 8 * B) / (k0 / (2 * s ^ 2))) =
      24 * s ^ 2 * (3 * Real.log dd + 1 + 2 * B) / k0 := by
    field_simp
    ring
  rw [e, div_le_iff₀ hk0]
  nlinarith

/-- Step 3: `c₂ x = 4194372 · 0.99 · c_q² · 10^-8 s² d Γ` at `g = c_q s³ g₀`, `k = k₀/(2 s²)`, `x = 0.99 n g`,
`g₀ = 2·10^-4 σ d^{3/2} Γ^{1/2}/(k₀ n^{1/2})`. -/
theorem c2x_idQ (dd nn k0 σ Γ s : ℝ) (hd : 0 < dd) (hk : 0 < k0) (hσ : 0 < σ) (hn : 0 < nn) (hΓ : 0 < Γ)
    (hs : 0 < s) :
    10256 / 10000 * s ^ 3 * (2 / 10 ^ 4 * σ * (dd * Real.sqrt dd) * Real.sqrt Γ / (k0 * Real.sqrt nn)) /
        (σ ^ 2 * priceR dd (k0 / (2 * s ^ 2))) *
      (99 / 100 * nn * (10256 / 10000 * s ^ 3 * (2 / 10 ^ 4 * σ * (dd * Real.sqrt dd) * Real.sqrt Γ /
        (k0 * Real.sqrt nn)))) =
      4194372 * (99 / 100) * (10256 / 10000) ^ 2 / 10 ^ 8 * s ^ 2 * dd * Γ := by
  unfold priceR
  have hs' := Real.sq_sqrt hd.le
  have hr := Real.sq_sqrt hn.le
  have hu := Real.sq_sqrt hΓ.le
  have hs0 := Real.sqrt_pos.mpr hd
  have hr0 := Real.sqrt_pos.mpr hn
  have hu0 := Real.sqrt_pos.mpr hΓ
  generalize Real.sqrt dd = a at *
  generalize Real.sqrt nn = r at *
  generalize Real.sqrt Γ = u at *
  subst hs' hr hu
  field_simp

/-- Step 4: (D3) `10 k₀ ≤ s³ d` gives `12 k²/d² ≤ 0.03 s²` at `k = k₀/(2 s²)`. -/
theorem k2_le {dd k0 s : ℝ} (hd : 0 < dd) (hk0 : 0 ≤ k0) (hs : 0 < s) (hD3 : 10 * k0 ≤ s ^ 3 * dd) :
    12 * (k0 / (2 * s ^ 2)) ^ 2 / dd ^ 2 ≤ 3 / 100 * s ^ 2 := by
  have hs2 : 0 < s ^ 2 := by positivity
  have e : 12 * (k0 / (2 * s ^ 2)) ^ 2 / dd ^ 2 = 3 * k0 ^ 2 / (s ^ 4 * dd ^ 2) := by
    field_simp
    ring
  rw [e, div_le_iff₀ (by positivity)]
  have h1 : (10 * k0) ^ 2 ≤ (s ^ 3 * dd) ^ 2 := pow_le_pow_left₀ (by positivity) hD3 2
  nlinarith

/-- Step 5: `(3/8) x = 7.425 c_q s³ Y₀` at `x = 0.99 n g`, `g = c_q s³ g₀`, with
`Y₀ = 10^-5 σ d^{3/2} (n Γ)^{1/2}/k₀`, since `n g₀ = 20 Y₀`. -/
theorem thr_idQ (dd nn k0 σ Γ s : ℝ) (hd : 0 < dd) (hk : 0 < k0) (hn : 0 < nn) (hΓ : 0 < Γ) :
    3 / 8 * (99 / 100 * nn * (10256 / 10000 * s ^ 3 * (2 / 10 ^ 4 * σ * (dd * Real.sqrt dd) * Real.sqrt Γ /
        (k0 * Real.sqrt nn)))) =
      7425 / 1000 * (10256 / 10000) * s ^ 3 * (1 / 10 ^ 5 * σ * (dd * Real.sqrt dd) * Real.sqrt (nn * Γ) / k0) := by
  rw [Real.sqrt_mul hn.le]
  have hr := Real.sq_sqrt hn.le
  have hr0 := Real.sqrt_pos.mpr hn
  generalize Real.sqrt nn = r at *
  subst hr
  field_simp
  ring

/-! ## The failure budget -/

/-- Steps 6 and 7: the failure of Proposition Q-STOP at `β = 1/4` and the clamp are at most `s²`, from
`3 c₁ ≤ 0.6 s²` and `R_L ≤ 3 N*` (the first term), `c₂ x ≤ 0.35 s² N*` (the second), `12 k²/d² ≤ 0.03 s²` (the main
part of the fourth), and the small terms: `ρ ≤ 1/2`, `x ≥ 1000`, `16 ρ R_L ≤ 0.005 s² k x`, `2/n² ≤ 0.005 s²`. -/
theorem fail_budgetQ {c1 c2 RL N x ρ k dd nn s : ℝ} (hc2 : 0 ≤ c2) (hRL0 : 0 ≤ RL) (hN : 0 < N)
    (hk : 0 < k) (hd : 0 < dd) (hρ : ρ ≤ 1 / 2) (hx : 1000 ≤ x) (hs : 0 < s)
    (h1 : 3 * c1 ≤ 3 / 5 * s ^ 2) (hRL : RL ≤ 3 * N) (h2 : c2 * x ≤ 35 / 100 * s ^ 2 * N)
    (h4 : 12 * k ^ 2 / dd ^ 2 ≤ 3 / 100 * s ^ 2) (h5 : 16 * ρ * RL ≤ 5 / 1000 * s ^ 2 * (k * x))
    (h6 : 2 / nn ^ 2 ≤ 5 / 1000 * s ^ 2) :
    1 - s ^ 2 ≤ 1 - (c1 * RL + c2 * (x + ρ)) / N -
      (4 * ρ * RL / k + 3 * k ^ 2 / dd ^ 2 * (x + ρ)) / (1 / 4 * x) - 2 / nn ^ 2 := by
  have hx0 : 0 < x := by linarith
  have hs2 : 0 < s ^ 2 := by positivity
  -- the first two terms
  have t12 : (c1 * RL + c2 * (x + ρ)) / N ≤ 3 / 5 * s ^ 2 + 35 / 100 * s ^ 2 * (1 + 1 / 2000) := by
    rw [div_le_iff₀ hN]
    have a1 : c1 * RL ≤ 3 / 5 * s ^ 2 * N := by nlinarith
    have a2 : c2 * ρ ≤ 35 / 100 * s ^ 2 * N / 2000 := by
      have : c2 * ρ * 1000 ≤ c2 * x * (1 / 2) := by nlinarith
      nlinarith
    nlinarith
  -- the fourth term
  have t4 : (4 * ρ * RL / k + 3 * k ^ 2 / dd ^ 2 * (x + ρ)) / (1 / 4 * x) ≤
      5 / 1000 * s ^ 2 + 3 / 100 * s ^ 2 * (1 + 1 / 2000) := by
    rw [div_le_iff₀ (by positivity)]
    have b1 : 4 * ρ * RL / k ≤ 5 / 1000 * s ^ 2 * (1 / 4 * x) := by
      rw [div_le_iff₀ hk]
      nlinarith
    have hK : 0 ≤ 3 * k ^ 2 / dd ^ 2 := by positivity
    have b2 : 3 * k ^ 2 / dd ^ 2 * (x + ρ) ≤ 3 / 100 * s ^ 2 * (1 + 1 / 2000) * (1 / 4 * x) := by
      have e : 3 * k ^ 2 / dd ^ 2 = (12 * k ^ 2 / dd ^ 2) / 4 := by ring
      rw [e]
      have hρx : x + ρ ≤ x * (1 + 1 / 2000) := by nlinarith
      have h4' : 0 ≤ 12 * k ^ 2 / dd ^ 2 := by positivity
      calc 12 * k ^ 2 / dd ^ 2 / 4 * (x + ρ) ≤ 12 * k ^ 2 / dd ^ 2 / 4 * (x * (1 + 1 / 2000)) :=
            mul_le_mul_of_nonneg_left hρx (by positivity)
        _ ≤ 3 / 100 * s ^ 2 / 4 * (x * (1 + 1 / 2000)) :=
            mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        _ = 3 / 100 * s ^ 2 * (1 + 1 / 2000) * (1 / 4 * x) := by ring
    nlinarith
  nlinarith

end AdversarialBco.LowerDeltaQ
