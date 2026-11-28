/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Grow.Prob

@[expose] public section

/-!
# Route G: the parameters and their arithmetic

For `d ≥ 4·10^6`, `ℓ = log (1/δ) ≥ 60` and `n ≥ d^6 ℓ`: `k = 3 log d`, `B = 4ℓ/5`, `η = 1/5`, `σ = sigB n`,
`ℓ_c = ellB n`, `R0 = posR d` and `g = (B d² / (192 (2^20 + 17) n k² log n))^{1/2}`, which makes the budget
`M₀ ≤ B / (a/(2σ²))` an equality. Then:

* `routeG_params`: the hypotheses `RouteG` of Route G, with the Lipschitz constant `L_D` of the dent at most
  `1/(8 posR d)`;
* `qZero_ge`: `q₀ ≥ 49/50` (the Chebyshev failure is at most `0.0138`, the clamp failure at most `2/n`);
* `delta_lt`: `δ < q₀ e^{-(B + (2B)^{1/2})/q₀}`;
* `target_le`: `8·10^-6 d (n ℓ)^{1/2} / (log d (log n)^{1/2}) ≤ (1 - η) M₀`.
-/

open Real

namespace AdversarialBco.Grow

open AdversarialBco.Lower AdversarialBco.Lower.Top AdversarialBco.UnifiedLower.Body

/-! ## The parameters -/

/-- `k = 3 log d`. -/
noncomputable def kG (d : ℕ) : ℝ := 3 * Real.log d

/-- The budget `B = 4ℓ/5`. -/
noncomputable def bG (ℓ : ℝ) : ℝ := 4 / 5 * ℓ

/-- The height `g = (B d² / (192 (2^20 + 17) n k² log n))^{1/2}`. -/
noncomputable def gG (d n : ℕ) (ℓ : ℝ) : ℝ :=
  Real.sqrt (bG ℓ * (d : ℝ) ^ 2 / (192 * (2 ^ 20 + 17) * n * kG d ^ 2 * Real.log n))

/-- The parameters of the static game. -/
noncomputable def pG (d n : ℕ) (ℓ : ℝ) : GP := ⟨gG d n ℓ, kG d, 1 / 4, sigB n⟩

/-! ## Bounds on `log d` -/

theorem log_d_ge {d : ℕ} (hd : 4000000 ≤ d) : 29 / 2 ≤ Real.log d := by
  have hdR : (2097152 : ℝ) ≤ d := by
    have : (4000000 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have h : Real.log 2097152 ≤ Real.log d := Real.log_le_log (by norm_num) hdR
  have h2 : Real.log 2097152 = 21 * Real.log 2 := by
    rw [show (2097152 : ℝ) = 2 ^ 21 by norm_num, Real.log_pow]
    norm_num
  have := Real.log_two_gt_d9
  linarith

theorem log_d_le {d : ℕ} (hd : 4000000 ≤ d) : Real.log d ≤ 57 / 4 + d / 4000000 := by
  have hdR : (4000000 : ℝ) ≤ d := by exact_mod_cast hd
  have h1 : Real.log d = Real.log 4000000 + Real.log (d / 4000000) := by
    rw [← Real.log_mul (by norm_num) (by positivity)]
    congr 1
    field_simp
  have h2 : Real.log (d / 4000000) ≤ d / 4000000 - 1 := Real.log_le_sub_one_of_pos (by positivity)
  have h3 : Real.log 4000000 ≤ 22 * Real.log 2 := by
    rw [show (22 : ℝ) * Real.log 2 = Real.log (2 ^ 22) by rw [Real.log_pow]; norm_num]
    exact Real.log_le_log (by norm_num) (by norm_num)
  have := Real.log_two_lt_d9
  linarith

/-- `log d / d ≤ 61/(16·10^6)` for `d ≥ 4·10^6`. -/
theorem log_div_d_le {d : ℕ} (hd : 4000000 ≤ d) : Real.log d / d ≤ 61 / 16000000 := by
  have hdR : (4000000 : ℝ) ≤ d := by exact_mod_cast hd
  have h := log_d_le hd
  rw [div_le_iff₀ (by positivity)]
  nlinarith

theorem kG_le {d : ℕ} (hd : 4000000 ≤ d) : 2048 * kG d ≤ d := by
  have hdR : (4000000 : ℝ) ≤ d := by exact_mod_cast hd
  have h := log_d_le hd
  unfold kG
  nlinarith

theorem kG_ge {d : ℕ} (hd : 4000000 ≤ d) : 87 / 2 ≤ kG d := by
  have h := log_d_ge hd
  unfold kG
  linarith

/-! ## The cells -/

theorem cellsOK_kG {d : ℕ} (hd : 4000000 ≤ d) : CellsOK d (kG d) := by
  have hdR : (4000000 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := by linarith
  have hk := kG_ge hd
  have hkd := kG_le hd
  have hL := log_d_ge hd
  -- `k d/(d + 2) ≥ k - 1`
  have hkd2 : kG d - 1 ≤ kG d * d / (d + 2) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  -- `e^{-(k - 1)} = e/d³`
  have hexp3 : Real.exp (-(kG d - 1)) = Real.exp 1 / (d : ℝ) ^ 3 := by
    rw [show -(kG d - 1) = 1 - (3 : ℕ) * Real.log d by unfold kG; push_cast; ring, Real.exp_sub,
      Real.exp_nat_mul, Real.exp_log hd0]
  have he := Real.exp_one_lt_d9
  have hk3 : (87 / 2 : ℝ) ^ 3 ≤ kG d ^ 3 := pow_le_pow_left₀ (by norm_num) hk 3
  refine ⟨by omega, by linarith, hkd, ?_, ?_, ?_⟩
  · -- `(d + 2)/d ≤ 2 ≤ (2k)^{1/2}`
    have h1 : ((d : ℝ) + 2) / d ≤ 2 := by
      rw [div_le_iff₀ hd0]
      linarith
    have h2 : (2 : ℝ) ≤ Real.sqrt (2 * kG d) := by
      rw [Real.le_sqrt (by norm_num) (by linarith)]
      linarith
    linarith
  · calc Real.exp (-(kG d * d / (d + 2))) ≤ Real.exp (-(kG d - 1)) := Real.exp_le_exp.2 (by linarith)
      _ = Real.exp 1 / (d : ℝ) ^ 3 := hexp3
      _ < kG d ^ 3 / (d : ℝ) ^ 3 := by
        apply div_lt_div_of_pos_right _ (by positivity)
        linarith
  · -- `(2k)^{1/2} = (6 log d)^{1/2} ≤ log d`
    have hs : Real.sqrt (2 * kG d) ≤ Real.log d := by
      rw [Real.sqrt_le_left (by linarith)]
      unfold kG
      nlinarith
    have hexp2 : Real.exp (Real.log d - (kG d - 1)) = Real.exp 1 / (d : ℝ) ^ 2 := by
      rw [show Real.log d - (kG d - 1) = 1 - (2 : ℕ) * Real.log d by unfold kG; push_cast; ring, Real.exp_sub,
        Real.exp_nat_mul, Real.exp_log hd0]
    calc 2 * Real.exp (Real.sqrt (2 * kG d) - kG d * d / (d + 2)) ≤ 2 * Real.exp (Real.log d - (kG d - 1)) := by
          gcongr
      _ = 2 * Real.exp 1 / (d : ℝ) ^ 2 := by rw [hexp2, mul_div_assoc]
      _ < kG d ^ 3 / (d : ℝ) ^ 2 := by
        apply div_lt_div_of_pos_right _ (by positivity)
        linarith

/-! ## The size of `n` and of `g` -/

section Size

variable {d n : ℕ} {ℓ : ℝ}

theorem n_ge (hd : 4000000 ≤ d) (hℓ : 60 ≤ ℓ) (hn : (d : ℝ) ^ 6 * ℓ ≤ n) : (10 : ℝ) ^ 40 ≤ n := by
  have hdR : (4000000 : ℝ) ≤ d := by exact_mod_cast hd
  have h6 : (4000000 : ℝ) ^ 6 ≤ (d : ℝ) ^ 6 := pow_le_pow_left₀ (by norm_num) hdR 6
  have := mul_le_mul h6 hℓ (by norm_num) (by positivity)
  linarith

theorem log_n_ge (hd : 4000000 ≤ d) (hℓ : 60 ≤ ℓ) (hn : (d : ℝ) ^ 6 * ℓ ≤ n) : 1 ≤ Real.log n := by
  have h := n_ge hd hℓ hn
  rw [Real.le_log_iff_exp_le (by linarith)]
  have := Real.exp_one_lt_d9
  linarith

theorem sigB_sq (hn : 0 ≤ Real.log n) : sigB n ^ 2 = 1 / (384 * Real.log n) := by
  unfold sigB
  rw [div_pow, mul_pow, Real.sq_sqrt (by linarith)]
  ring

theorem sigB_pos (hn : 0 < Real.log n) : 0 < sigB n := by
  unfold sigB
  have : 0 < Real.sqrt (6 * Real.log n) := Real.sqrt_pos.2 (by linarith)
  positivity

theorem gG_sq (hℓ : 0 ≤ ℓ) (hn : 0 ≤ Real.log n) :
    gG d n ℓ ^ 2 = bG ℓ * (d : ℝ) ^ 2 / (192 * (2 ^ 20 + 17) * n * kG d ^ 2 * Real.log n) := by
  unfold gG
  rw [Real.sq_sqrt]
  exact div_nonneg (by unfold bG; positivity) (mul_nonneg (by positivity) hn)

theorem gG_pos (hd : 4000000 ≤ d) (hℓ : 60 ≤ ℓ) (hn : (d : ℝ) ^ 6 * ℓ ≤ n) : 0 < gG d n ℓ := by
  have hL := log_n_ge hd hℓ hn
  have hN := n_ge hd hℓ hn
  have hk := kG_ge hd
  have hdR : (4000000 : ℝ) ≤ d := by exact_mod_cast hd
  unfold gG
  apply Real.sqrt_pos.2
  apply div_pos (by unfold bG; positivity)
  have : (0 : ℝ) < n := by linarith
  have : (0 : ℝ) < Real.log n := by linarith
  have : 0 < kG d := by linarith
  positivity

/-- `g² d⁴ k² log n ≤ 10^-8`. -/
theorem gG_small (hd : 4000000 ≤ d) (hℓ : 60 ≤ ℓ) (hn : (d : ℝ) ^ 6 * ℓ ≤ n) :
    gG d n ℓ ^ 2 * (d : ℝ) ^ 4 * kG d ^ 2 * Real.log n ≤ 1 / 10 ^ 8 := by
  have hL := log_n_ge hd hℓ hn
  have hN := n_ge hd hℓ hn
  have hk := kG_ge hd
  have hdR : (4000000 : ℝ) ≤ d := by exact_mod_cast hd
  have hk0 : kG d ≠ 0 := by linarith
  have hL0 : Real.log n ≠ 0 := by linarith
  have hn0 : (n : ℝ) ≠ 0 := by linarith
  have hd0 : (d : ℝ) ≠ 0 := by linarith
  rw [gG_sq (by linarith) (by linarith)]
  have e : bG ℓ * (d : ℝ) ^ 2 / (192 * (2 ^ 20 + 17) * n * kG d ^ 2 * Real.log n) * (d : ℝ) ^ 4 * kG d ^ 2 *
      Real.log n = bG ℓ * (d : ℝ) ^ 6 / (192 * (2 ^ 20 + 17) * n) := by
    field_simp
  rw [e, div_le_iff₀ (by positivity)]
  unfold bG
  nlinarith

/-- `g d² ≤ 10^-5`. -/
theorem gG_mul_le (hd : 4000000 ≤ d) (hℓ : 60 ≤ ℓ) (hn : (d : ℝ) ^ 6 * ℓ ≤ n) :
    gG d n ℓ * (d : ℝ) ^ 2 ≤ 1 / 10 ^ 5 := by
  have h := gG_small hd hℓ hn
  have hL := log_n_ge hd hℓ hn
  have hk := kG_ge hd
  have hg : 0 ≤ gG d n ℓ := Real.sqrt_nonneg _
  have hu0 : 0 ≤ gG d n ℓ * (d : ℝ) ^ 2 := by positivity
  have h2 : (gG d n ℓ * (d : ℝ) ^ 2 * kG d) ^ 2 ≤ (1 / 10 ^ 4) ^ 2 := by
    have e : (gG d n ℓ * (d : ℝ) ^ 2 * kG d) ^ 2 = gG d n ℓ ^ 2 * (d : ℝ) ^ 4 * kG d ^ 2 := by ring
    have h0 : 0 ≤ gG d n ℓ ^ 2 * (d : ℝ) ^ 4 * kG d ^ 2 := by positivity
    rw [e]
    nlinarith
  have h3 : gG d n ℓ * (d : ℝ) ^ 2 * kG d ≤ 1 / 10 ^ 4 :=
    (pow_le_pow_iff_left₀ (mul_nonneg hu0 (by linarith)) (by norm_num) two_ne_zero).1 h2
  nlinarith

theorem wG_pG : wG d (pG d n ℓ) = gG d n ℓ / kG d * (((d : ℝ) + 2) / 2 + kG d) / sigB n := rfl

/-- The fine bound on the shift: `w ≤ 1/100`. -/
theorem wG_le (hd : 4000000 ≤ d) (hℓ : 60 ≤ ℓ) (hn : (d : ℝ) ^ 6 * ℓ ≤ n) : wG d (pG d n ℓ) ≤ 1 / 100 := by
  have h := gG_small hd hℓ hn
  have hL := log_n_ge hd hℓ hn
  have hk := kG_ge hd
  have hkd := kG_le hd
  have hdR : (4000000 : ℝ) ≤ d := by exact_mod_cast hd
  have hg : 0 ≤ gG d n ℓ := Real.sqrt_nonneg _
  have hs := sigB_pos (n := n) (by linarith)
  have hk0 : kG d ≠ 0 := by linarith
  have hL0 : Real.log n ≠ 0 := by linarith
  set A := ((d : ℝ) + 2) / 2 + kG d with hA
  have hA0 : 0 ≤ A := by positivity
  have hAd : A ≤ d := by rw [hA]; linarith
  have hw0 : 0 ≤ wG d (pG d n ℓ) := by
    rw [wG_pG]
    exact div_nonneg (mul_nonneg (div_nonneg hg (by linarith)) hA0) hs.le
  have hw2 : wG d (pG d n ℓ) ^ 2 * ((d : ℝ) ^ 4 * kG d ^ 4) =
      gG d n ℓ ^ 2 * (d : ℝ) ^ 4 * kG d ^ 2 * Real.log n * 384 * A ^ 2 := by
    rw [wG_pG, div_pow, mul_pow, div_pow, sigB_sq (by linarith)]
    field_simp
    ring
  have hX0 : 0 ≤ gG d n ℓ ^ 2 * (d : ℝ) ^ 4 * kG d ^ 2 * Real.log n := by
    have : 0 ≤ Real.log n := by linarith
    positivity
  have hAd2 : A ^ 2 ≤ (d : ℝ) ^ 2 := pow_le_pow_left₀ hA0 hAd 2
  have hd24 : (d : ℝ) ^ 2 ≤ (d : ℝ) ^ 4 * kG d ^ 4 := by
    have h1 : (1 : ℝ) ≤ kG d ^ 4 := one_le_pow₀ (by linarith)
    have h2 : (d : ℝ) ^ 2 ≤ (d : ℝ) ^ 4 := pow_le_pow_right₀ (by linarith) (by norm_num)
    nlinarith [pow_nonneg (show (0 : ℝ) ≤ d by linarith) 4]
  have hD : 0 < (d : ℝ) ^ 4 * kG d ^ 4 := by
    have : 0 < kG d := by linarith
    positivity
  have h1 : gG d n ℓ ^ 2 * (d : ℝ) ^ 4 * kG d ^ 2 * Real.log n * 384 * A ^ 2 ≤ 1 / 10 ^ 8 * 384 * (d : ℝ) ^ 2 := by
    calc gG d n ℓ ^ 2 * (d : ℝ) ^ 4 * kG d ^ 2 * Real.log n * 384 * A ^ 2
        ≤ 1 / 10 ^ 8 * 384 * A ^ 2 := by gcongr
      _ ≤ 1 / 10 ^ 8 * 384 * (d : ℝ) ^ 2 := by gcongr
  have h3 : wG d (pG d n ℓ) ^ 2 ≤ (1 / 100) ^ 2 := by
    rw [← mul_le_mul_iff_left₀ hD, hw2]
    nlinarith
  exact (pow_le_pow_iff_left₀ hw0 (by norm_num) two_ne_zero).1 h3

/-- The Lipschitz constant of the dent against the radius of the position: `L_D posR d ≤ 1/8`. -/
theorem lipG_le (hd : 4000000 ≤ d) (hℓ : 60 ≤ ℓ) (hn : (d : ℝ) ^ 6 * ℓ ≤ n) :
    gG d n ℓ / kG d * (5 * Real.sqrt d) * frameC d * posR d ≤ 1 / 8 := by
  obtain ⟨hR1, hRk⟩ := posR_bounds hd
  have hgd := gG_mul_le hd hℓ hn
  have hk := kG_ge hd
  have hL := log_d_ge hd
  have hdR : (4000000 : ℝ) ≤ d := by exact_mod_cast hd
  have hg : 0 ≤ gG d n ℓ := Real.sqrt_nonneg _
  have hk0 : 0 < kG d := by linarith
  have hsq : Real.sqrt d * Real.sqrt ((d : ℝ) + 2) ≤ 2 * d := by
    rw [← Real.sqrt_mul (by positivity), Real.sqrt_le_left (by positivity)]
    nlinarith
  have hkR : kRipe d ≤ 42 * kG d := by
    unfold kRipe kG
    linarith
  have hR : posR d ≤ d * (42 * kG d) := hRk.trans (mul_le_mul_of_nonneg_left hkR (by positivity))
  have e : gG d n ℓ / kG d * (5 * Real.sqrt d) * frameC d * posR d =
      10 * (gG d n ℓ / kG d) * (Real.sqrt d * Real.sqrt ((d : ℝ) + 2)) * posR d := by
    unfold frameC
    ring
  rw [e]
  calc 10 * (gG d n ℓ / kG d) * (Real.sqrt d * Real.sqrt ((d : ℝ) + 2)) * posR d
      ≤ 10 * (gG d n ℓ / kG d) * (2 * d) * (d * (42 * kG d)) := by gcongr
    _ = 840 * (gG d n ℓ * (d : ℝ) ^ 2) := by
      field_simp
      ring
    _ ≤ 1 / 8 := by linarith

end Size

/-! ## The constants of Route G -/

section Constants

variable {d n : ℕ} {ℓ : ℝ}

theorem gamG_ge (hd : 4000000 ≤ d) : 1 - 1 / 10 ^ 6 ≤ gamG d (kG d) := by
  have hkd := kG_le hd
  have hk := kG_ge hd
  have hdR : (4000000 : ℝ) ≤ d := by exact_mod_cast hd
  unfold gamG
  have : 3 * kG d ^ 2 / (d : ℝ) ^ 2 ≤ 1 / 10 ^ 6 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [mul_le_mul hkd hkd (by linarith) (by linarith)]
  linarith

theorem aG_pG : aG d (pG d n ℓ) = 2 * (2 ^ 20 + 17) * gG d n ℓ * kG d ^ 2 / (gamG d (kG d) * (d : ℝ) ^ 2) := rfl

theorem mZero_pG : mZero d n (pG d n ℓ) = n * (gamG d (kG d) * gG d n ℓ / 2) := rfl

/-- The budget: `M₀ ≤ B / (a/(2σ²))`, an equality at this `g`. -/
theorem budget_pG (hd : 4000000 ≤ d) (hℓ : 60 ≤ ℓ) (hn : (d : ℝ) ^ 6 * ℓ ≤ n) :
    mZero d n (pG d n ℓ) ≤ bG ℓ / (aG d (pG d n ℓ) / (2 * (pG d n ℓ).sc ^ 2)) := by
  have hL := log_n_ge hd hℓ hn
  have hN := n_ge hd hℓ hn
  have hk := kG_ge hd
  have hγ := gamG_ge hd
  have hg := gG_pos hd hℓ hn
  have hdR : (4000000 : ℝ) ≤ d := by exact_mod_cast hd
  have hk0 : kG d ≠ 0 := by linarith
  have hL0 : Real.log n ≠ 0 := by linarith
  have hn0 : (n : ℝ) ≠ 0 := by linarith
  have hd0 : (d : ℝ) ≠ 0 := by linarith
  have hγ0 : gamG d (kG d) ≠ 0 := by linarith
  have hg0 : gG d n ℓ ≠ 0 := hg.ne'
  have hsc : (pG d n ℓ).sc ^ 2 = 1 / (384 * Real.log n) := sigB_sq (by linarith)
  have ha : 0 < aG d (pG d n ℓ) := by
    rw [aG_pG]
    exact div_pos (by have := hk; positivity) (mul_pos (by linarith) (by positivity))
  have hpos : 0 < aG d (pG d n ℓ) / (2 * (pG d n ℓ).sc ^ 2) := by
    rw [hsc]
    exact div_pos ha (by positivity)
  rw [le_div_iff₀ hpos]
  have e : mZero d n (pG d n ℓ) * (aG d (pG d n ℓ) / (2 * (pG d n ℓ).sc ^ 2)) =
      192 * (2 ^ 20 + 17) * n * kG d ^ 2 * Real.log n / (d : ℝ) ^ 2 * gG d n ℓ ^ 2 := by
    rw [mZero_pG, aG_pG, hsc]
    field_simp
    ring
  rw [e, gG_sq (by linarith) (by linarith)]
  apply le_of_eq
  field_simp

/-- The Chebyshev failure: `n a/(η² M₀) ≤ 0.0138` at `η = 1/5`. -/
theorem cheb_fail_le (hd : 4000000 ≤ d) (hℓ : 60 ≤ ℓ) (hn : (d : ℝ) ^ 6 * ℓ ≤ n) :
    n * aG d (pG d n ℓ) / ((1 / 5) ^ 2 * mZero d n (pG d n ℓ)) ≤ 138 / 10000 := by
  have hN := n_ge hd hℓ hn
  have hk := kG_ge hd
  have hγ := gamG_ge hd
  have hg := gG_pos hd hℓ hn
  have hdR : (4000000 : ℝ) ≤ d := by exact_mod_cast hd
  have hn0 : (n : ℝ) ≠ 0 := by linarith
  have hd0 : (d : ℝ) ≠ 0 := by linarith
  have hγ0 : gamG d (kG d) ≠ 0 := by linarith
  have hg0 : gG d n ℓ ≠ 0 := hg.ne'
  have e : n * aG d (pG d n ℓ) / ((1 / 5) ^ 2 * mZero d n (pG d n ℓ)) =
      100 * (2 ^ 20 + 17) * (kG d / d) ^ 2 / gamG d (kG d) ^ 2 := by
    rw [aG_pG, mZero_pG]
    field_simp
    ring
  rw [e, div_le_iff₀ (by positivity)]
  have hx : kG d / d ≤ 183 / 16000000 := by
    have := log_div_d_le hd
    unfold kG
    rw [mul_div_assoc]
    linarith
  have hx0 : 0 ≤ kG d / d := div_nonneg (by linarith) (by linarith)
  have hx2 : (kG d / d) ^ 2 ≤ (183 / 16000000) ^ 2 := pow_le_pow_left₀ hx0 hx 2
  have hγ2 : (1 - 1 / 10 ^ 6 : ℝ) ^ 2 ≤ gamG d (kG d) ^ 2 := pow_le_pow_left₀ (by norm_num) hγ 2
  nlinarith

/-- The clamp failure: `2 n e^{-(ℓ_c - w)²/2} ≤ 10^-3`. -/
theorem clamp_fail_le (hd : 4000000 ≤ d) (hℓ : 60 ≤ ℓ) (hn : (d : ℝ) ^ 6 * ℓ ≤ n) :
    (n : ℝ) * (2 * Real.exp (-(ellB n - wG d (pG d n ℓ)) ^ 2 / 2)) ≤ 1 / 1000 := by
  have hw := wG_le hd hℓ hn
  have hL := log_n_ge hd hℓ hn
  have hN := n_ge hd hℓ hn
  have hnR : (0 : ℝ) < n := by linarith
  set s := Real.sqrt (Real.log n) with hsdef
  have hs1 : 1 ≤ s := Real.one_le_sqrt.2 hL
  have hs2 : s ^ 2 = Real.log n := Real.sq_sqrt (by linarith)
  have hell : 12 / 5 * s ≤ ellB n := by
    unfold ellB
    rw [Real.le_sqrt (by positivity) (by linarith)]
    nlinarith
  have h2 : 2 * s ≤ ellB n - wG d (pG d n ℓ) := by linarith
  have h3 : 4 * Real.log n ≤ (ellB n - wG d (pG d n ℓ)) ^ 2 := by nlinarith
  have h4 : Real.exp (-(ellB n - wG d (pG d n ℓ)) ^ 2 / 2) ≤ ((n : ℝ) ^ 2)⁻¹ := by
    have e : ((n : ℝ) ^ 2)⁻¹ = Real.exp (-((2 : ℕ) * Real.log n)) := by
      rw [Real.exp_neg, Real.exp_nat_mul, Real.exp_log hnR]
    rw [e]
    apply Real.exp_le_exp.2
    push_cast
    linarith
  have e2 : (n : ℝ) * (2 * ((n : ℝ) ^ 2)⁻¹) = 2 / n := by
    field_simp
  calc (n : ℝ) * (2 * Real.exp (-(ellB n - wG d (pG d n ℓ)) ^ 2 / 2)) ≤ (n : ℝ) * (2 * ((n : ℝ) ^ 2)⁻¹) := by
        gcongr
    _ = 2 / n := e2
    _ ≤ 1 / 1000 := by
      rw [div_le_iff₀ hnR]
      linarith

/-- `q₀ ≥ 49/50`. -/
theorem qZero_ge (hd : 4000000 ≤ d) (hℓ : 60 ≤ ℓ) (hn : (d : ℝ) ^ 6 * ℓ ≤ n) :
    49 / 50 ≤ qZero d n (pG d n ℓ) (1 / 5) (ellB n) := by
  have h1 := cheb_fail_le hd hℓ hn
  have h2 := clamp_fail_le hd hℓ hn
  unfold qZero
  linarith

/-- `δ < q e^{-(B + (2B)^{1/2})/q}` for `q ≥ 49/50` and `ℓ = log (1/δ) ≥ 60`. -/
theorem delta_lt {δ q : ℝ} (hδ : 0 < δ) (hℓ : 60 ≤ Real.log (1 / δ)) (hq : 49 / 50 ≤ q) :
    δ < q * Real.exp (-(bG (Real.log (1 / δ)) + Real.sqrt (2 * bG (Real.log (1 / δ)))) / q) := by
  set ℓ := Real.log (1 / δ) with hℓdef
  have hδe : δ = Real.exp (-ℓ) := by
    rw [hℓdef, one_div, Real.log_inv, neg_neg, Real.exp_log hδ]
  have hq0 : 0 < q := by linarith
  set X := bG ℓ + Real.sqrt (2 * bG ℓ) with hX
  have e : q * Real.exp (-X / q) = Real.exp (Real.log q - X / q) := by
    rw [neg_div, Real.exp_neg, Real.exp_sub, Real.exp_log hq0]
    ring
  rw [e, hδe]
  apply Real.exp_lt_exp.2
  have hs2 : Real.sqrt ℓ ^ 2 = ℓ := Real.sq_sqrt (by linarith)
  have hs7 : 774 / 100 ≤ Real.sqrt ℓ := by
    rw [Real.le_sqrt (by norm_num) (by linarith)]
    linarith
  have hsX : Real.sqrt (2 * bG ℓ) ≤ 1265 / 1000 * Real.sqrt ℓ := by
    rw [Real.sqrt_le_left (by positivity)]
    unfold bG
    nlinarith
  have key : 1 + X < q * (1 + ℓ) := by
    have : 49 / 50 * (1 + ℓ) ≤ q * (1 + ℓ) := mul_le_mul_of_nonneg_right hq (by linarith)
    have hb : bG ℓ = 4 / 5 * ℓ := rfl
    have hq2 : 1265 / 1000 * Real.sqrt ℓ + 2 / 100 < 18 / 100 * ℓ := by
      nlinarith [mul_le_mul_of_nonneg_right hs7 (Real.sqrt_nonneg ℓ)]
    linarith
  have h1 : (1 + X) / q < 1 + ℓ := by
    rw [div_lt_iff₀ hq0]
    linarith
  have h2 : (1 + X) / q = q⁻¹ + X / q := by ring
  have h3 := Real.one_sub_inv_le_log_of_pos hq0
  linarith

/-- The threshold: `8·10^-6 d (n ℓ)^{1/2} / (log d (log n)^{1/2}) ≤ (1 - η) M₀` at `η = 1/5`. -/
theorem target_le (hd : 4000000 ≤ d) (hℓ : 60 ≤ ℓ) (hn : (d : ℝ) ^ 6 * ℓ ≤ n) :
    8 / 10 ^ 6 * d * Real.sqrt (n * ℓ) / (Real.log d * Real.sqrt (Real.log n)) ≤
      (1 - 1 / 5) * mZero d n (pG d n ℓ) := by
  have hL := log_n_ge hd hℓ hn
  have hLd := log_d_ge hd
  have hN := n_ge hd hℓ hn
  have hγ := gamG_ge hd
  have hg := gG_pos hd hℓ hn
  have hk := kG_ge hd
  have hdR : (4000000 : ℝ) ≤ d := by exact_mod_cast hd
  have hn0 : (n : ℝ) ≠ 0 := by linarith
  have hd0 : (d : ℝ) ≠ 0 := by linarith
  have hL0 : Real.log n ≠ 0 := by linarith
  have hLd0 : Real.log d ≠ 0 := by linarith
  have hsl : 0 < Real.sqrt (Real.log n) := Real.sqrt_pos.2 (by linarith)
  have hlhs : 0 ≤ 8 / 10 ^ 6 * d * Real.sqrt (n * ℓ) / (Real.log d * Real.sqrt (Real.log n)) :=
    div_nonneg (by positivity) (mul_nonneg (by linarith) hsl.le)
  have hrhs : 0 ≤ (1 - 1 / 5) * mZero d n (pG d n ℓ) := by
    rw [mZero_pG]
    have : 0 ≤ gamG d (kG d) := by linarith
    positivity
  rw [← pow_le_pow_iff_left₀ hlhs hrhs two_ne_zero]
  have e1 : (8 / 10 ^ 6 * d * Real.sqrt (n * ℓ) / (Real.log d * Real.sqrt (Real.log n))) ^ 2 =
      ((n : ℝ) * ℓ * (d : ℝ) ^ 2 / (Real.log d ^ 2 * Real.log n)) * (64 / 10 ^ 12) := by
    rw [div_pow, mul_pow, mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by linarith)]
    ring
  have e2 : ((1 - 1 / 5) * mZero d n (pG d n ℓ)) ^ 2 =
      ((n : ℝ) * ℓ * (d : ℝ) ^ 2 / (Real.log d ^ 2 * Real.log n)) *
        (16 / 125 * gamG d (kG d) ^ 2 / (9 * (192 * (2 ^ 20 + 17)))) := by
    rw [mZero_pG, show ((1 - 1 / 5) * (n * (gamG d (kG d) * gG d n ℓ / 2))) ^ 2 =
      4 / 25 * (n : ℝ) ^ 2 * gamG d (kG d) ^ 2 * gG d n ℓ ^ 2 by ring, gG_sq (by linarith) (by linarith)]
    unfold bG kG
    field_simp
    ring
  rw [e1, e2]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [le_div_iff₀ (by norm_num)]
  have hγ2 : (1 - 1 / 10 ^ 6 : ℝ) ^ 2 ≤ gamG d (kG d) ^ 2 := pow_le_pow_left₀ (by norm_num) hγ 2
  nlinarith

/-- **The hypotheses of Route G** at the parameters `pG d n ℓ`, the radius `posR d`, the budget `B = 4ℓ/5`,
`η = 1/5` and the clamp level `ellB n`. -/
theorem routeG_pG (hd : 4000000 ≤ d) (hℓ : 60 ≤ ℓ) (hn : (d : ℝ) ^ 6 * ℓ ≤ n) :
    RouteG d n (pG d n ℓ) (posR d) (bG ℓ) (1 / 5) (ellB n) := by
  have hL := log_n_ge hd hℓ hn
  have hN := n_ge hd hℓ hn
  have hk := kG_ge hd
  have hg := gG_pos hd hℓ hn
  have hgd := gG_mul_le hd hℓ hn
  have hdR : (4000000 : ℝ) ≤ d := by exact_mod_cast hd
  have hell : 1 ≤ ellB n := by
    unfold ellB
    rw [Real.one_le_sqrt]
    linarith
  have hn1 : 0 < n := Nat.cast_pos (α := ℝ) |>.1 (by linarith)
  have hn2 : 1 < n := Nat.one_lt_cast (α := ℝ) |>.1 (by linarith)
  have hw : wG d (pG d n ℓ) ≤ ellB n := (wG_le hd hℓ hn).trans (by linarith)
  have hR0 : 0 ≤ posR d := by linarith [(posR_bounds hd).1]
  have hγ : 0 < gamG d (kG d) := by linarith [gamG_ge hd]
  refine ⟨cellsOK_kG hd, hg, sigB_pos (n := n) (by linarith), rfl, hn1, by unfold bG; linarith,
    by norm_num, by norm_num, hR0, (sigB_mul_ellB hn2).le, hw, ?_, hγ, budget_pG hd hℓ hn⟩
  have hlip := lipG_le hd hℓ hn
  have hgk : gG d n ℓ / kG d * kG d = gG d n ℓ := div_mul_cancel₀ _ (by linarith)
  have hg1 : gG d n ℓ ≤ gG d n ℓ * (d : ℝ) ^ 2 :=
    le_mul_of_one_le_right hg.le (one_le_pow₀ (by linarith))
  show gG d n ℓ / kG d * (5 * Real.sqrt d) * frameC d * posR d + gG d n ℓ / kG d * kG d ≤ 1 / 2
  linarith

end Constants

end AdversarialBco.Grow
