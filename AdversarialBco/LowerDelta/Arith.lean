/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Lower.R0Ext
public import AdversarialBco.Conj1Lower.StopTop

@[expose] public section

/-!
# Theorem LU-D, the arithmetic

Pure arithmetic on reals at the parameters of Corollary LU-P (`k₀ = kRipe d`, `g₀ = gRipe d n σ`,
`Y₀ = 10^-5 σ d^{3/2} (n Γ)^{1/2}/k₀`):

* `chanBK_mono`: the channel bound `chanBK L R0 g σ` is monotone in `g`.
* `ripe_Y0_ge`: `Y₀ ≥ 2.88·10^-9 D`, `D = d^{3/2} n^{1/2}/ln d`.

No `rpow`: `d^{3/2}` is `d √d`.
-/

open Finset

namespace AdversarialBco.LowerDelta

open AdversarialBco.Lower

/-! ## The scaling of the derived constants -/

theorem chanBK_mono {L R0 g g' σ : ℝ} (h0 : 0 ≤ L * (R0 + 1 / 2)) (hg : 0 ≤ g) (hgg : g ≤ g') :
    chanBK L R0 g σ ≤ chanBK L R0 g' σ := by
  unfold chanBK
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact pow_le_pow_left₀ (by linarith) (by linarith) 2

/-! ## The threshold -/

/-- `Y₀ ≥ 2.88·10⁻⁹ d^{3/2} n^{1/2}/ln d`. -/
theorem ripe_Y0_ge (dd nn : ℝ) (hd : 4000000 ≤ dd) (hn : dd ^ 10 ≤ nn) :
    288 / 10 ^ 11 * (dd * Real.sqrt dd) * Real.sqrt nn / Real.log dd ≤
      1 / 10 ^ 5 * sigB nn * (dd * Real.sqrt dd) * Real.sqrt (nn * gamR dd nn) / kRipe dd := by
  have hL := ripeB_log dd hd
  have hd0 : 0 < dd := by linarith
  have hd10 : (4000000 : ℝ) ^ 10 ≤ dd ^ 10 := pow_le_pow_left₀ (by norm_num) hd 10
  have hnbig : (4000000 : ℝ) ^ 10 ≤ nn := hd10.trans hn
  have hn1 : 1 < nn := lt_of_lt_of_le (by norm_num) hnbig
  have hcoef := ripeB_coef nn (gamR dd nn) hn1 (ripeB_gam dd nn (by linarith) hn)
  set L := Real.log dd with hL_def
  set A := dd * Real.sqrt dd with hA_def
  set r := Real.sqrt nn with hr_def
  set σ := sigB nn with hσ_def
  have hk : kRipe dd = 120 * L + 68 := rfl
  have hk0 : 0 < kRipe dd := by rw [hk]; linarith
  have hL0 : 0 < L := by linarith
  have hA0 : 0 ≤ A := by positivity
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hY : 3608 / 10 ^ 10 * A * r / kRipe dd ≤
      1 / 10 ^ 5 * σ * A * Real.sqrt (nn * gamR dd nn) / kRipe dd := by
    rw [div_le_div_iff_of_pos_right hk0]
    have := mul_le_mul_of_nonneg_left hcoef hA0
    nlinarith
  have h1 : 288 / 10 ^ 11 * A * r / L ≤ 3608 / 10 ^ 10 * A * r / kRipe dd := by
    rw [div_le_div_iff₀ hL0 hk0]
    have hc : 288 / 10 ^ 11 * kRipe dd ≤ 3608 / 10 ^ 10 * L := by rw [hk]; linarith
    have := mul_le_mul_of_nonneg_left hc (mul_nonneg hA0 hr0)
    nlinarith
  linarith

end AdversarialBco.LowerDelta
