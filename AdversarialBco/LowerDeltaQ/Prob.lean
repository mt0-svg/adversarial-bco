/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.LowerDeltaQ.Stop
public import AdversarialBco.LowerDeltaQ.Arith
public import AdversarialBco.LowerDelta.Prob

@[expose] public section

/-!
# Theorem LU-DQ on a body between `B(0, 1/2)` and `B(0, R0)`

Proposition Q-STOP (`stopQ_prob`, LowerDeltaQ/Stop.lean) at the parameters `pDQ d n R0 s`
(`k = k₀/(2 s²)`, `g = 1.0256 s³ g₀`, `L = σ/R0`, `σ = sigB n`, `b = 1/4`, `δ₀ = s²`), the level `x = 0.99 n g` and
`β = 1/4`, then the clamp coupling and the derandomisation of the indicator, as in Theorem LU-D
(LowerDelta/Prob.lean). Under (D1) `1024 k₀ ≤ s² d` and (D3) `10 k₀ ≤ s³ d`:

    P(Reg_n ≥ 2.1·10^-8 s³ d^{3/2} n^{1/2}/ln d) ≥ 1 - s²,

with the regret in `[0, n/2]` on every run (`lowerBodyProbDeltaQ_mid`).

* `pDQ`, `good_pDQ`: the parameters and `Good`; the strategy is the rule `S'` at `pDQ`, whose class does not read `g`.
* `count_pDQ`: `X ≥ 16`, `X ≤ n`, `N* ≥ 0.1248 d Γ`, `R_L ≤ 3 N*`.
* `c1_pDQ`, `c2x_pDQ`: the first two failure terms (Steps 2 and 3); `thr_pDQ`: the threshold (Step 5).
* `thr_lowQ`, `log_le_four_rootQ`, `ledger_le_levelQ`: the small terms (Step 6): `x ≥ 6.72·10^-5 d^{1/2} n^{1/2}`,
  `ln n ≤ 4 n^{1/4}`, `8 R_L ≤ 0.005 (k₀/2) x`.
-/

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal NNReal

namespace AdversarialBco.LowerDeltaQ

open RealRAM AdversarialBco.Lower AdversarialBco.Lower.Bayes AdversarialBco.Lower.Top AdversarialBco.Lower.Stop
  AdversarialBco.UnifiedLower.Body AdversarialBco.LowerDelta

/-! ## The parameters -/

/-- The parameters of Theorem LU-DQ on a body inside `B(0, R0)` at the failure `δ₀ = s²`:
`g = 1.0256 s³ gRipe d n σ`, `k = kRipe d/(2 s²)`, `L = σ/R0`, `σ = sigB n`, `b = 1/4`. -/
noncomputable def pDQ (d n : ℕ) (R0 s : ℝ) : SParams :=
  ⟨10256 / 10000 * s ^ 3 * gRipe d n (sigB n), kRipe d / (2 * s ^ 2), sigB n / R0, sigB n, 1 / 4⟩

theorem cq_s3_le {s : ℝ} (hs : 0 < s) (hs2 : s ^ 2 ≤ 1 / 2) : 10256 / 10000 * s ^ 3 ≤ 1 := by
  have hs1 : s ≤ 1 := by nlinarith
  have : s ^ 3 ≤ s ^ 2 := by nlinarith
  nlinarith

theorem k_ge_kRipe {k0 s : ℝ} (hk0 : 0 ≤ k0) (hs : 0 < s) (hs2 : s ^ 2 ≤ 1 / 2) : k0 ≤ k0 / (2 * s ^ 2) := by
  rw [le_div_iff₀ (by positivity)]
  nlinarith

theorem good_pDQ {d n : ℕ} {R0 s : ℝ} (hd : 4000000 ≤ d) (hn : d ^ 10 ≤ n) (hR : 1 ≤ R0)
    (hRk : R0 ≤ d * kRipe d) (hs : 0 < s) (hs2 : s ^ 2 ≤ 1 / 2) (hD1 : 1024 * kRipe d ≤ s ^ 2 * d) :
    Good (pDQ d n R0 s) d R0 := by
  obtain ⟨h1, -, h3, -, -, h6, -, -⟩ := ripeB_params hd hn
  obtain ⟨k1, k2, k3, -⟩ := ripeK_params_ext hd hn hR hRk
  have hc := cq_s3_le hs hs2
  have hg : 10256 / 10000 * s ^ 3 * gRipe d n (sigB n) ≤ gRipe d n (sigB n) := by nlinarith
  refine ⟨mul_pos (by positivity) h3, ?_, k1, h1, k2, ?_, ?_, rfl⟩
  · show 240 ≤ kRipe d / (2 * s ^ 2)
    exact h6.trans (k_ge_kRipe (by linarith) hs hs2)
  · show 2048 * (kRipe d / (2 * s ^ 2)) ≤ d
    rw [show 2048 * (kRipe d / (2 * s ^ 2)) = 1024 * kRipe d / s ^ 2 by field_simp; ring,
      div_le_iff₀ (by positivity)]
    linarith
  · show sigB n / R0 * (R0 + 1 / 2) + 10256 / 10000 * s ^ 3 * gRipe d n (sigB n) ≤ 1 / 2
    linarith

/-- The count at `pDQ`: `X ≥ 16`, `X ≤ n`, `N* ≥ 0.1248 d Γ` and `R_L ≤ 3 N*`
(`X = X₀/(4 c_q² s¹⁰) ≥ X₀/(16 s⁸)`, the `X` of Theorem LU-D at the order `k`, so (N1) holds there). -/
theorem count_pDQ {d n : ℕ} {R0 s : ℝ} (hd : 4000000 ≤ d) (hn : d ^ 10 ≤ n) (hR : 1 ≤ R0)
    (hRk : R0 ≤ d * kRipe d) (hs : 0 < s) (hs2 : s ^ 2 ≤ 1 / 2) (hD1 : 1024 * kRipe d ≤ s ^ 2 * d) :
    16 ≤ xCount d ((pDQ d n R0 s).w d) ∧ xCount d ((pDQ d n R0 s).w d) ≤ n ∧
      1248 / 10000 * d * gamR d n ≤ nStar d ((pDQ d n R0 s).w d) ∧
      ledgerR d ((pDQ d n R0 s).w d) ≤ 3 * nStar d ((pDQ d n R0 s).w d) := by
  have hdR : (4000000 : ℝ) ≤ d := by exact_mod_cast hd
  have hnR : (d : ℝ) ^ 10 ≤ n := by exact_mod_cast hn
  have hd0 : (0 : ℝ) < d := by linarith
  have hd1 : (1 : ℝ) ≤ d := by linarith
  have hdim := ripeB_dim d hdR
  obtain ⟨hk240, -⟩ := kRipe_ge d hd1 hdim
  have hn4 := ripeB_n d n hdR hnR
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le (by positivity) hn4
  obtain ⟨hs0, -⟩ := ripeB_sig d n hdR hnR
  have hΓ : 4 ≤ gamR d n := gamR_ge d n hd0 hn4
  have hR0 : 0 < R0 := by linarith
  set k0 := kRipe (d : ℝ) with hk0_def
  set Γ := gamR (d : ℝ) n with hΓ_def
  set X0 := xCount d (wStar d k0 (sigB n / R0) (gRipe d n (sigB n))) with hX0_def
  have hX0 : X0 = k0 ^ 4 * n / (4 / 10 ^ 6 * (d : ℝ) ^ 5 * Γ) / R0 ^ 2 :=
    xCount_ripe_K d n (sigB n) R0 hd0 (by linarith) hs0 hn0 (by linarith) hR0
  have hX016 : 16 ≤ X0 := (ripeK_params_ext hd hn hR hRk).2.2.2
  set c := (2 * (10256 / 10000) * s ^ 5) ^ 2 with hc_def
  have hc0 : 0 < c := by positivity
  have hX : xCount d ((pDQ d n R0 s).w d) = X0 / c := by
    show xCount d (wStar d (k0 / (2 * s ^ 2)) (sigB n / R0) (10256 / 10000 * s ^ 3 * gRipe d n (sigB n))) = _
    rw [wStar_scaleQ _ _ _ _ _ hs, xCount_scaleQ]
  clear_value c X0 Γ k0
  have hs4 : s ^ 4 ≤ 1 / 4 := by
    calc s ^ 4 = (s ^ 2) ^ 2 := by ring
      _ ≤ (1 / 2) ^ 2 := pow_le_pow_left₀ (by positivity) hs2 2
      _ = 1 / 4 := by norm_num
  have hs8 : s ^ 8 ≤ 1 / 16 := by
    calc s ^ 8 = (s ^ 4) ^ 2 := by ring
      _ ≤ (1 / 4) ^ 2 := pow_le_pow_left₀ (by positivity) hs4 2
      _ = 1 / 16 := by norm_num
  have hs80 : 0 < s ^ 8 := by positivity
  have hcs : c ≤ 16 * s ^ 8 := by
    have e : c = 4 * (10256 / 10000) ^ 2 * s ^ 2 * s ^ 8 := by rw [hc_def]; ring
    rw [e]
    have : 4 * (10256 / 10000 : ℝ) ^ 2 * s ^ 2 ≤ 16 := by nlinarith
    nlinarith
  have hXge : X0 / (16 * s ^ 8) ≤ X0 / c := div_le_div_of_nonneg_left (by linarith) hc0 hcs
  have hX0le : X0 ≤ X0 / (16 * s ^ 8) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  -- (N1) at the order `k`
  have hk : k0 ≤ k0 / (2 * s ^ 2) := k_ge_kRipe (by linarith) hs hs2
  have hlogR := log_R0_le_ext d n (k0 / (2 * s ^ 2)) R0 hd1 (by linarith) hR0
    (hRk.trans (mul_le_mul_of_nonneg_left hk hd0.le)) hnR
  have hN1 := log_x_ripe_ge_Kext d n (k0 / (2 * s ^ 2)) R0 (by linarith) hd0 hn0 (by linarith) hR0 hlogR
  have e1 : (k0 / (2 * s ^ 2)) ^ 4 * n / (4 / 10 ^ 6 * (d : ℝ) ^ 5 * Γ) / R0 ^ 2 = X0 / (16 * s ^ 8) := by
    rw [hX0]
    field_simp
    ring
  rw [← hΓ_def, e1] at hN1
  have hlog : Real.log (X0 / (16 * s ^ 8) / 2) ≤ Real.log (xCount d ((pDQ d n R0 s).w d) / 2) := by
    rw [hX]
    exact Real.log_le_log (by positivity) (by linarith)
  have h16 : 16 ≤ xCount d ((pDQ d n R0 s).w d) := by rw [hX]; linarith
  have hd12 : (12288 : ℝ) ≤ d := by linarith
  have hNx := nStar_ge_x d ((pDQ d n R0 s).w d) hd12
  have hN : 1248 / 10000 * d * Γ ≤ nStar d ((pDQ d n R0 s).w d) := by
    apply nStar_ripe_ge d Γ _ hd0 hΓ
    nlinarith
  refine ⟨h16, ?_, hN, ledgerR_three d _ hd12 (by linarith)⟩
  -- `X ≤ n`
  rw [hX, div_le_iff₀ hc0]
  have hsd : (1024 * k0) ^ 5 ≤ (s ^ 2 * d) ^ 5 := pow_le_pow_left₀ (by linarith) hD1 5
  have hR2 : 1 ≤ R0 ^ 2 := one_le_pow₀ hR
  have hX0n : X0 ≤ k0 ^ 4 * n / (4 / 10 ^ 6 * (d : ℝ) ^ 5 * Γ) := by
    rw [hX0]
    exact div_le_self (div_nonneg (by positivity) (mul_pos (mul_pos (by norm_num) (pow_pos hd0 5)) (by linarith)).le)
      hR2
  have hc' : c * (d : ℝ) ^ 5 = 4 * (10256 / 10000) ^ 2 * (s ^ 2 * d) ^ 5 := by rw [hc_def]; ring
  have hΓ0 : 0 < Γ := by linarith
  have hfin : k0 ^ 4 * n / (4 / 10 ^ 6 * (d : ℝ) ^ 5 * Γ) ≤ n * c := by
    rw [div_le_iff₀ (mul_pos (mul_pos (by norm_num) (pow_pos hd0 5)) hΓ0)]
    have h1 : k0 ^ 4 * n ≤ n * (4 * (10256 / 10000) ^ 2 * (1024 * k0) ^ 5) * (4 / 10 ^ 6 * Γ) := by
      have hk4 : 0 ≤ k0 ^ 4 * n := by positivity
      have e : n * (4 * (10256 / 10000) ^ 2 * (1024 * k0) ^ 5) * (4 / 10 ^ 6 * Γ) =
          k0 ^ 4 * n * (16 * (10256 / 10000) ^ 2 * 1024 ^ 5 / 10 ^ 6 * k0 * Γ) := by ring
      rw [e]
      have hkΓ : 1 ≤ k0 * Γ := one_le_mul_of_one_le_of_one_le (by linarith) (by linarith)
      have hC : (1 : ℝ) ≤ 16 * (10256 / 10000 : ℝ) ^ 2 * 1024 ^ 5 / 10 ^ 6 := by norm_num
      have : 1 ≤ 16 * (10256 / 10000 : ℝ) ^ 2 * 1024 ^ 5 / 10 ^ 6 * k0 * Γ := by
        rw [mul_assoc]; exact one_le_mul_of_one_le_of_one_le hC hkΓ
      exact le_mul_of_one_le_right hk4 this
    have h2 : n * (4 * (10256 / 10000) ^ 2 * (1024 * k0) ^ 5) * (4 / 10 ^ 6 * Γ) ≤
        n * (4 * (10256 / 10000) ^ 2 * (s ^ 2 * d) ^ 5) * (4 / 10 ^ 6 * Γ) := by
      apply mul_le_mul_of_nonneg_right _ (mul_pos (by norm_num) hΓ0).le
      apply mul_le_mul_of_nonneg_left _ hn0.le
      exact mul_le_mul_of_nonneg_left hsd (by norm_num)
    have e2 : n * c * (4 / 10 ^ 6 * (d : ℝ) ^ 5 * Γ) =
        n * (4 * (10256 / 10000) ^ 2 * (s ^ 2 * d) ^ 5) * (4 / 10 ^ 6 * Γ) := by
      rw [← hc']; ring
    rw [e2]
    linarith
  linarith

/-! ## The terms of the failure at `pDQ` -/

/-- Step 2 at `pDQ`: (R1) gives `3 c₁ ≤ 0.6 s²`. -/
theorem c1_pDQ {d n : ℕ} {R0 s : ℝ} (hd : 4000000 ≤ d) (hn : d ^ 10 ≤ n) (hR : 1 ≤ R0) (hs : 0 < s)
    (hs2 : s ^ 2 ≤ 1 / 2) :
    3 * ((4 * (3 * Real.log d + 1) + 8 * chanBK (pDQ d n R0 s).L R0 (pDQ d n R0 s).g (pDQ d n R0 s).sc) /
      (pDQ d n R0 s).k) ≤ 3 / 5 * s ^ 2 := by
  obtain ⟨hσ, -, hg, hgle, -, hk240, -, -, -, -, -⟩ := ripeB_params hd hn
  have hc := cq_s3_le hs hs2
  have hgq0 : 0 ≤ 10256 / 10000 * s ^ 3 * gRipe d n (sigB n) := by positivity
  have hgq : 10256 / 10000 * s ^ 3 * gRipe d n (sigB n) ≤ gRipe d n (sigB n) := by nlinarith
  have hR0 : 0 < R0 := by linarith
  have hL0 : 0 ≤ sigB n / R0 * (R0 + 1 / 2) := by positivity
  have hB := ((chanBK_mono hL0 hgq0 hgq).trans (chanBK_le_chanB (sigB n) R0 (gRipe d n (sigB n)) hσ hR hg.le)).trans
    (chanB_ripe (sigB n) (gRipe d n (sigB n)) hσ hg.le hgle)
  exact three_c1_le (by linarith) hs (R1_ripe d _ hB)

/-- Step 3 at `pDQ`: `c₂ x = 4194372 · 0.99 · c_q² · 10^-8 s² d Γ` at the level `x = 0.99 n g`. -/
theorem c2x_pDQ {d n : ℕ} {R0 s : ℝ} (hd : 4000000 ≤ d) (hn : d ^ 10 ≤ n) (hs : 0 < s) :
    (pDQ d n R0 s).g / ((pDQ d n R0 s).sc ^ 2 * priceR d (pDQ d n R0 s).k) * (99 / 100 * n * (pDQ d n R0 s).g) =
      4194372 * (99 / 100) * (10256 / 10000) ^ 2 / 10 ^ 8 * s ^ 2 * d * gamR d n := by
  have hdR : (4000000 : ℝ) ≤ d := by exact_mod_cast hd
  have hnR : (d : ℝ) ^ 10 ≤ n := by exact_mod_cast hn
  have hd0 : (0 : ℝ) < d := by linarith
  have hn4 := ripeB_n d n hdR hnR
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le (by positivity) hn4
  obtain ⟨hσ, -, -, -, -, hk240, -, -, -, -, -⟩ := ripeB_params hd hn
  have hΓ : 4 ≤ gamR d n := gamR_ge d n hd0 hn4
  show 10256 / 10000 * s ^ 3 * gRipe d n (sigB n) / (sigB n ^ 2 * priceR d (kRipe d / (2 * s ^ 2))) *
    (99 / 100 * n * (10256 / 10000 * s ^ 3 * gRipe d n (sigB n))) = _
  unfold gRipe
  exact c2x_idQ d n (kRipe d) (sigB n) (gamR d n) s hd0 (by linarith) hσ hn0 (by linarith) hs

/-- Step 5 at `pDQ`: the threshold `2.1·10^-8 s³ d^{3/2} n^{1/2}/ln d` is at most `(3/8) x`. -/
theorem thr_pDQ {d n : ℕ} (hd : 4000000 ≤ d) (hn : d ^ 10 ≤ n) {s : ℝ} (hs : 0 < s) :
    21 / 10 ^ 9 * s ^ 3 * ((d : ℝ) * Real.sqrt d) * Real.sqrt n / Real.log d ≤
      3 / 8 * (99 / 100 * n * (10256 / 10000 * s ^ 3 * gRipe d n (sigB n))) := by
  have hdR : (4000000 : ℝ) ≤ d := by exact_mod_cast hd
  have hnR : (d : ℝ) ^ 10 ≤ n := by exact_mod_cast hn
  have hd0 : (0 : ℝ) < d := by linarith
  have hn4 := ripeB_n d n hdR hnR
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le (by positivity) hn4
  obtain ⟨-, -, -, -, -, hk240, -, -, -, -, -⟩ := ripeB_params hd hn
  have hΓ : 4 ≤ gamR d n := gamR_ge d n hd0 hn4
  unfold gRipe
  rw [thr_idQ d n (kRipe d) (sigB n) (gamR d n) s hd0 (by linarith) hn0 (by linarith)]
  have hY := ripe_Y0_ge d n hdR hnR
  have hL := ripeB_log d hdR
  have hD : 0 ≤ (d : ℝ) * Real.sqrt d * Real.sqrt n / Real.log d := by positivity
  have hs3 : 0 < s ^ 3 := by positivity
  have e1 : 21 / 10 ^ 9 * s ^ 3 * ((d : ℝ) * Real.sqrt d) * Real.sqrt n / Real.log d =
      s ^ 3 * (21 / 10 ^ 9 * ((d : ℝ) * Real.sqrt d * Real.sqrt n / Real.log d)) := by ring
  have e2 : 288 / 10 ^ 11 * ((d : ℝ) * Real.sqrt d) * Real.sqrt n / Real.log d =
      288 / 10 ^ 11 * ((d : ℝ) * Real.sqrt d * Real.sqrt n / Real.log d) := by ring
  rw [e2] at hY
  rw [e1]
  calc s ^ 3 * (21 / 10 ^ 9 * ((d : ℝ) * Real.sqrt d * Real.sqrt n / Real.log d))
      ≤ s ^ 3 * (7425 / 1000 * (10256 / 10000) *
          (288 / 10 ^ 11 * ((d : ℝ) * Real.sqrt d * Real.sqrt n / Real.log d))) :=
        mul_le_mul_of_nonneg_left (by nlinarith) hs3.le
    _ ≤ s ^ 3 * (7425 / 1000 * (10256 / 10000) * (1 / 10 ^ 5 * sigB n * ((d : ℝ) * Real.sqrt d) *
          Real.sqrt (n * gamR d n) / kRipe d)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hY (by norm_num)) hs3.le
    _ = _ := by ring

/-- The threshold from below under (D3): `2.1·10^-8 s³ d^{3/2} n^{1/2}/ln d ≥ 2.52·10^-5 d^{1/2} n^{1/2}`, since
`s³ d ≥ 10 k₀ ≥ 1200 ln d`. -/
theorem thr_lowQ {dd nn s : ℝ} (hd : 4000000 ≤ dd) (hD3 : 10 * kRipe dd ≤ s ^ 3 * dd) :
    252 / 10 ^ 7 * Real.sqrt dd * Real.sqrt nn ≤
      21 / 10 ^ 9 * s ^ 3 * (dd * Real.sqrt dd) * Real.sqrt nn / Real.log dd := by
  have hL := ripeB_log dd hd
  have hL0 : 0 < Real.log dd := by linarith
  have h : 1200 * Real.log dd ≤ s ^ 3 * dd := by unfold kRipe at hD3; linarith
  rw [le_div_iff₀ hL0]
  have hp : 0 ≤ 21 / 10 ^ 9 * Real.sqrt dd * Real.sqrt nn := by positivity
  have := mul_le_mul_of_nonneg_right h hp
  nlinarith

/-- `log n ≤ 4 n^{1/4}`, with `n^{1/4} = √√n`. -/
theorem log_le_four_rootQ {nn : ℝ} (hn : 0 < nn) : Real.log nn ≤ 4 * Real.sqrt (Real.sqrt nn) := by
  have hu0 : 0 < Real.sqrt (Real.sqrt nn) := Real.sqrt_pos.2 (Real.sqrt_pos.2 hn)
  have hu4 : Real.sqrt (Real.sqrt nn) ^ 4 = nn := by
    have h1 : Real.sqrt (Real.sqrt nn) ^ 2 = Real.sqrt nn := Real.sq_sqrt (Real.sqrt_nonneg _)
    have h2 : Real.sqrt nn ^ 2 = nn := Real.sq_sqrt hn.le
    calc Real.sqrt (Real.sqrt nn) ^ 4 = (Real.sqrt (Real.sqrt nn) ^ 2) ^ 2 := by ring
      _ = nn := by rw [h1, h2]
  have hl : Real.log nn = 4 * Real.log (Real.sqrt (Real.sqrt nn)) := by
    conv_lhs => rw [← hu4]
    rw [Real.log_pow]
    norm_num
  have := Real.log_le_sub_one_of_pos hu0
  rw [hl]
  linarith

/-- The small ledger term: `8 R_L ≤ 0.005 (k₀/2) x` when `R_L ≤ (d/2) ln(1 + X)`, `0 ≤ X ≤ n`, `k₀ ≥ 240` and
`x ≥ 6.72·10^-5 d^{1/2} n^{1/2}`, for `d ≥ 4·10^6`, `n ≥ d^10`. -/
theorem ledger_le_levelQ {dd nn X RL x k0 : ℝ} (hd : 4000000 ≤ dd) (hn : dd ^ 10 ≤ nn) (hX0 : 0 ≤ X) (hXn : X ≤ nn)
    (hRL : RL ≤ dd / 2 * Real.log (1 + X)) (hk0 : 240 ≤ k0)
    (hx : 672 / 10 ^ 7 * Real.sqrt dd * Real.sqrt nn ≤ x) : 8 * RL ≤ 5 / 1000 * (k0 / 2) * x := by
  have hd0 : 0 < dd := by linarith
  have hd1 : 1 ≤ dd := by linarith
  have hdn : dd ≤ nn := (le_self_pow₀ hd1 (by norm_num)).trans hn
  have hn0 : 0 < nn := by linarith
  -- `ln(1 + X) ≤ 2 ln n ≤ 8 u`, `u = √√n`
  have hlogd := ripeB_log dd hd
  have hlogn : Real.log dd ≤ Real.log nn := Real.log_le_log hd0 hdn
  have h2n : Real.log (1 + X) ≤ Real.log (2 * nn) := Real.log_le_log (by linarith) (by linarith)
  have hl2 : Real.log (2 * nn) = Real.log 2 + Real.log nn := Real.log_mul (by norm_num) hn0.ne'
  have hlog2 := Real.log_two_lt_d9
  have hu := log_le_four_rootQ hn0
  set u := Real.sqrt (Real.sqrt nn) with hu_def
  have hu0 : 0 < u := Real.sqrt_pos.2 (Real.sqrt_pos.2 hn0)
  have hlx : Real.log (1 + X) ≤ 8 * u := by linarith
  have hR : RL ≤ 4 * dd * u := hRL.trans (by nlinarith)
  -- `u ≥ 10^6 √d`
  have hu2 : u ^ 2 = Real.sqrt nn := Real.sq_sqrt (Real.sqrt_nonneg _)
  have hsd2 : Real.sqrt dd ^ 2 = dd := Real.sq_sqrt hd0.le
  have hsd0 : 0 < Real.sqrt dd := Real.sqrt_pos.2 hd0
  have hd5 : dd ^ 5 ≤ Real.sqrt nn := by
    rw [Real.le_sqrt (by positivity) hn0.le]
    calc (dd ^ 5) ^ 2 = dd ^ 10 := by ring
      _ ≤ nn := hn
  have hd4 : 10 ^ 12 ≤ dd ^ 4 := by
    calc (10 : ℝ) ^ 12 ≤ 4000000 ^ 4 := by norm_num
      _ ≤ dd ^ 4 := pow_le_pow_left₀ (by norm_num) hd 4
  have hub : 10 ^ 6 * Real.sqrt dd ≤ u := by
    rw [← pow_le_pow_iff_left₀ (by positivity) hu0.le (two_ne_zero), hu2, mul_pow, hsd2]
    calc ((10 : ℝ) ^ 6) ^ 2 * dd = 10 ^ 12 * dd := by norm_num
      _ ≤ dd ^ 4 * dd := mul_le_mul_of_nonneg_right hd4 hd0.le
      _ = dd ^ 5 := by ring
      _ ≤ Real.sqrt nn := hd5
  -- `0.6 x ≥ 4.032·10^-5 √d u² ≥ 40.32 d u`
  have hx' : 672 / 10 ^ 7 * Real.sqrt dd * u ^ 2 ≤ x := by rw [hu2]; exact hx
  have h1 : 3 / 5 * x ≤ 5 / 1000 * (k0 / 2) * x := by
    have : 0 ≤ x := le_trans (by positivity) hx'
    nlinarith
  have h2 : 40 * dd * u ≤ 3 / 5 * (672 / 10 ^ 7 * Real.sqrt dd * u ^ 2) := by
    have := mul_le_mul_of_nonneg_left hub (show 0 ≤ 3 / 5 * (672 / 10 ^ 7) * Real.sqrt dd * u by positivity)
    nlinarith
  nlinarith

/-! ## Theorem LU-DQ on a body inside `B(0, R0)` -/

variable {Ω : Type} [MeasurableSpace Ω] {d : ℕ} {R0 : ℝ}

/-- **Theorem LU-DQ at `δ₀ = s²`** on a convex `K` with `B(0, 1/2) ⊆ K ⊆ B(0, R0)`, `1 ≤ R0 ≤ d kRipe d`: for
`d ≥ 4·10^6`, `n ≥ d^10`, `0 < s`, `s² ≤ 1/2`, (D1) `1024 k₀ ≤ s² d` and (D3) `10 k₀ ≤ s³ d`, every learner of
`IsLearnerAd K n` meets a strategy of `StratsMid K n (sigB n / R0)` against which its regret is measurable in the seed,
in `[0, n/2]` on every seed, and at least `2.1·10^-8 s³ d^{3/2} n^{1/2}/ln d` with probability at least `1 - s²`. -/
theorem lowerBodyProbDeltaQ_mid (I : Inputs) {n : ℕ} (hd : 4000000 ≤ d) (hn : d ^ 10 ≤ n) {K : Set (E d)}
    (hK : Convex ℝ K) (hK1 : Metric.closedBall (0 : E d) (1 / 2) ⊆ K) (hK2 : K ⊆ Metric.closedBall 0 R0)
    (hR1 : 1 ≤ R0) (hRk : R0 ≤ d * kRipe d) {s : ℝ} (hs : 0 < s) (hs2 : s ^ 2 ≤ 1 / 2)
    (hD1 : 1024 * kRipe d ≤ s ^ 2 * d) (hD3 : 10 * kRipe d ≤ s ^ 3 * d) (μ : Measure Ω) [IsProbabilityMeasure μ]
    {pol : Learner Ω d} (hpol : IsLearnerAd K n pol) :
    ∃ σ ∈ StratsMid K n (sigB n / R0), Measurable (fun ω => regretAd K σ (fun t => pol t ω) n) ∧
      (∀ ω, 0 ≤ regretAd K σ (fun t => pol t ω) n ∧ regretAd K σ (fun t => pol t ω) n ≤ n / 2) ∧
      ENNReal.ofReal (1 - s ^ 2) ≤ μ {ω | 21 / 10 ^ 9 * s ^ 3 * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n /
        Real.log d ≤ regretAd K σ (fun t => pol t ω) n} := by
  have hdR : (4000000 : ℝ) ≤ d := by exact_mod_cast hd
  have hnR : (d : ℝ) ^ 10 ≤ n := by exact_mod_cast hn
  have hd0 : (0 : ℝ) < d := by linarith
  have hd1 : (1 : ℝ) ≤ d := by linarith
  have hP := good_pDQ hd hn hR1 hRk hs hs2 hD1
  have hG := isProbabilityMeasure_gameLaw (prior d (1 / 2)) μ
  have hpolB : IsLearnerAd (Metric.closedBall 0 R0) n pol := fun t ht =>
    ⟨(hpol t ht).1, fun ω x o => hK2 ((hpol t ht).2 ω x o)⟩
  have hn1 : 1 < n := by
    have h1 : 1 < d ^ 10 := Nat.one_lt_pow (by norm_num) (by omega)
    omega
  have hn0 : 0 < n := by omega
  have hnn : (0 : ℝ) < n := by exact_mod_cast hn0
  have hR0 : 0 < R0 := by linarith
  obtain ⟨h16, hXn, hN1248, hRL3⟩ := count_pDQ hd hn hR1 hRk hs hs2 hD1
  have hX : Real.exp 1 / 2 ≤ xCount d ((pDQ d n R0 s).w d) := by
    have := Real.exp_one_lt_d9
    exact le_trans (by linarith) h16
  obtain ⟨-, -, hg0, -, -, hk240, -, -, -, -, -⟩ := ripeB_params hd hn
  have hn4 := ripeB_n d n hdR hnR
  have hΓ : 4 ≤ gamR d n := gamR_ge d n hd0 hn4
  have hN : 0 < nStar d ((pDQ d n R0 s).w d) := lt_of_lt_of_le (by positivity) hN1248
  have hg : 0 < (pDQ d n R0 s).g := hP.g_pos
  have hk : 0 < (pDQ d n R0 s).k := lt_of_lt_of_le (by norm_num) hP.k_ge
  -- the level `x = 0.99 n g` and Proposition Q-STOP at `β = 1/4`
  obtain ⟨x, hx_def⟩ : ∃ x : ℝ, x = 99 / 100 * n * (pDQ d n R0 s).g := ⟨_, rfl⟩
  have hx0 : 0 < x := by rw [hx_def]; positivity
  have hxn : x < n * (pDQ d n R0 s).g := by rw [hx_def]; nlinarith
  have hstop := stopQ_prob I hP hX hN μ hpolB hn0 hR0.le hx0 hxn (show (0 : ℝ) < 1 / 4 by norm_num)
  -- the threshold
  obtain ⟨θ, hθ_def⟩ : ∃ θ : ℝ, θ = 21 / 10 ^ 9 * s ^ 3 * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n / Real.log d :=
    ⟨_, rfl⟩
  have hθ' : θ = 21 / 10 ^ 9 * s ^ 3 * ((d : ℝ) * Real.sqrt d) * Real.sqrt n / Real.log d := by
    rw [hθ_def, rpow_three_halves d hd0.le]
  have hθx : θ ≤ 3 / 8 * x := by
    rw [hθ', hx_def]
    exact thr_pDQ hd hn hs
  have hmono : (gameLaw (prior d (1 / 2)) μ).real
      {z | (1 - 1 / 4) * x / 2 < regG (prior d (1 / 2)) (pDQ d n R0 s) pol n z} ≤
      (gameLaw (prior d (1 / 2)) μ).real {z | θ ≤ regG (prior d (1 / 2)) (pDQ d n R0 s) pol n z} :=
    measureReal_mono fun z hz => by
      simp only [Set.mem_ofPred_eq] at hz ⊢
      linarith
  have hclamp := prob_regG_clamped (P := pDQ d n R0 s) μ pol hn1 θ
  -- the failure budget
  have hlow := thr_lowQ (nn := n) hdR hD3
  have hxlow : 672 / 10 ^ 7 * Real.sqrt d * Real.sqrt n ≤ x := by
    rw [← hθ'] at hlow
    linarith
  have hsd : 2000 ≤ Real.sqrt d := by
    rw [Real.le_sqrt (by norm_num) hd0.le]
    linarith
  have hsn : 10 ^ 7 ≤ Real.sqrt n := by
    rw [Real.le_sqrt (by norm_num) hnn.le]
    exact le_trans (by norm_num) ((pow_le_pow_left₀ (by norm_num) hdR 10).trans hnR)
  have hsdn : 2000 * 10 ^ 7 ≤ Real.sqrt d * Real.sqrt n := mul_le_mul hsd hsn (by norm_num) (by positivity)
  have hx1000 : 1000 ≤ x := by linarith only [hxlow, hsdn]
  have hRL0 : 0 ≤ ledgerR d ((pDQ d n R0 s).w d) := by
    unfold ledgerR
    have : 0 ≤ (1 / 2 : ℝ) ^ 2 / (d * (pDQ d n R0 s).w d ^ 2) := by positivity
    exact mul_nonneg (by positivity) (Real.log_nonneg (by linarith))
  have hρ : (pDQ d n R0 s).L * (R0 + 1 / 2) + (pDQ d n R0 s).g ≤ 1 / 2 := hP.rng
  have hc2 : 0 ≤ (pDQ d n R0 s).g / ((pDQ d n R0 s).sc ^ 2 * priceR d (pDQ d n R0 s).k) := by
    unfold priceR
    positivity
  have h2 : (pDQ d n R0 s).g / ((pDQ d n R0 s).sc ^ 2 * priceR d (pDQ d n R0 s).k) * x ≤
      35 / 100 * s ^ 2 * nStar d ((pDQ d n R0 s).w d) := by
    rw [hx_def, c2x_pDQ hd hn hs]
    have hC : (4194372 * (99 / 100) * (10256 / 10000) ^ 2 / 10 ^ 8 : ℝ) ≤ 35 / 100 * (1248 / 10000) := by norm_num
    have hp : 0 ≤ s ^ 2 * d * gamR d n := by positivity
    calc 4194372 * (99 / 100) * (10256 / 10000) ^ 2 / 10 ^ 8 * s ^ 2 * d * gamR d n
        = (4194372 * (99 / 100) * (10256 / 10000) ^ 2 / 10 ^ 8) * (s ^ 2 * d * gamR d n) := by ring
      _ ≤ 35 / 100 * (1248 / 10000) * (s ^ 2 * d * gamR d n) := mul_le_mul_of_nonneg_right hC hp
      _ = 35 / 100 * s ^ 2 * (1248 / 10000 * d * gamR d n) := by ring
      _ ≤ 35 / 100 * s ^ 2 * nStar d ((pDQ d n R0 s).w d) :=
        mul_le_mul_of_nonneg_left hN1248 (by positivity)
  have h4 : 12 * (pDQ d n R0 s).k ^ 2 / (d : ℝ) ^ 2 ≤ 3 / 100 * s ^ 2 :=
    k2_le hd0 (by linarith) hs hD3
  have h5 : 16 * ((pDQ d n R0 s).L * (R0 + 1 / 2) + (pDQ d n R0 s).g) * ledgerR d ((pDQ d n R0 s).w d) ≤
      5 / 1000 * s ^ 2 * ((pDQ d n R0 s).k * x) := by
    have hX0 : 0 ≤ xCount d ((pDQ d n R0 s).w d) := by linarith
    have hl := ledger_le_levelQ hdR hnR hX0 hXn (ledgerR_le_x d _ hd0) (show 240 ≤ kRipe d from hk240) hxlow
    have e : 5 / 1000 * s ^ 2 * ((pDQ d n R0 s).k * x) = 5 / 1000 * (kRipe d / 2) * x := by
      show 5 / 1000 * s ^ 2 * (kRipe d / (2 * s ^ 2) * x) = _
      field_simp
    rw [e]
    have h16 : 16 * ((pDQ d n R0 s).L * (R0 + 1 / 2) + (pDQ d n R0 s).g) * ledgerR d ((pDQ d n R0 s).w d) ≤
        8 * ledgerR d ((pDQ d n R0 s).w d) :=
      mul_le_mul_of_nonneg_right (by linarith only [hρ]) hRL0
    linarith only [h16, hl]
  have h6 : 2 / (n : ℝ) ^ 2 ≤ 5 / 1000 * s ^ 2 := by
    have hdn : (d : ℝ) ≤ n := (le_self_pow₀ hd1 (by norm_num)).trans hnR
    have hs2d : 1 ≤ s ^ 2 * d := by linarith
    rw [div_le_iff₀ (by positivity)]
    have hn4e6 : (4000000 : ℝ) ≤ n := hdR.trans hdn
    have h1 : (d : ℝ) * 4000000 ≤ (n : ℝ) ^ 2 := by
      rw [sq]; exact mul_le_mul hdn hn4e6 (by norm_num) hnn.le
    have h2 := mul_le_mul_of_nonneg_left h1 (sq_nonneg s)
    linarith only [h2, hs2d]
  have hbud := fail_budgetQ (c1 := (4 * (3 * Real.log d + 1) +
      8 * chanBK (pDQ d n R0 s).L R0 (pDQ d n R0 s).g (pDQ d n R0 s).sc) / (pDQ d n R0 s).k) hc2 hRL0 hN hk hd0 hρ
    hx1000 hs (c1_pDQ hd hn hR1 hs hs2) hRL3 h2 h4 h5 h6
  have hpr : 1 - s ^ 2 ≤ (gameLaw (prior d (1 / 2)) μ).real
      {z | θ ≤ regG (prior d (1 / 2)) (pDQ d n R0 s) pol n (z.1, clampZ (ellB n) z.2.1, z.2.2)} := by
    have e : (1 - 1 / 4 : ℝ) * x / 2 = (1 - 1 / 4) * x / 2 := rfl
    linarith
  have hsc : (pDQ d n R0 s).sc * ellB n ≤ 1 / 8 := (sigB_mul_ellB hn1).le
  rw [← hθ_def]
  exact derand_prob_mid_bdd I hP hsc hK hK1 hK2 μ hpol hpr

end AdversarialBco.LowerDeltaQ
