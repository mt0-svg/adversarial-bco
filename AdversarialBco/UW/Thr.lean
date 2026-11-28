/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.UW.RowsW
public import AdversarialBco.Unified.BLOParam

@[expose] public section

/-!
# Lemma thr at T4U

`thrUW_holds : ThrUW Cthr` with `Cthr = 10^21`. Write `k = k_δ`, `Λ_0 = log N_0`, `L = 36 Λ_0`,
`ℓ = log(2dn)`, `ℓ_δ = log(2/δ)`. Then:

* the budget: `δ_c = 1/(2^k N_0)` and `2^k > 1/δ`, so `n δ_c ≤ δ/(15 · 2^17)` and `δ_ref(δ_c) ≤ δ/2`;
* the regret bound at T4U: `2ρ/η + n ε = (2900 L⁴ + 14500 L⁵) d^{3/2} √n √u ≤ 20000 L⁵ d^{3/2} √n √u`, with
  `√u ≤ 1 + ((k + 1) log 2/(7 d Λ_0))^{1/2}`, `Λ_0 ≤ 25 ℓ` and `(k + 1) log 2 ≤ 3 ℓ_δ`; the Azuma term is
  `(2 n (log 7 + k log 2 + Λ_0))^{1/2}`;
* off the case, `ε(u_δ) > 1/8` gives `√n < 116000 d^{3/2} L⁵ √u_δ`, so `n` is below the same bound.

Each term is compared with `d^{3/2} √n ℓ^5` or `d √(n ℓ_δ) ℓ^{9/2}` through `ℓ ≥ log 2`.
-/

namespace AdversarialBco.UW

open AdversarialBco.Poly AdversarialBco.Unified.BLO

variable {d : ℕ}

/-! ## The floor and the level -/

/-- `Λ_0 ≥ 14`. -/
theorem lam0_ge {n : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n) : 14 ≤ lam0 d n := by
  have h := parW_Le_ge hd hn 1
  rw [parW_Le_lam0] at h
  linarith

/-- `Λ_0 ≤ 25 log(2dn)`: `N_0 = 15 · 2^17 d³ n⁴ ≤ (2dn)^25`. -/
theorem lam0_le {n : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n) : lam0 d n ≤ 25 * Real.log (2 * d * n) := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  obtain ⟨hN, -, -, -⟩ := n0W_bounds hd hn
  have hle : (n0W d n : ℝ) ≤ (2 * d * n) ^ 25 := by
    rw [n0W_cast]
    have h1 : (1 : ℝ) ≤ (d : ℝ) * n := one_le_mul_of_one_le_of_one_le hd1 hn1
    have h2 : ((d : ℝ) * n) ^ 4 ≤ ((d : ℝ) * n) ^ 25 := pow_le_pow_right₀ h1 (by norm_num)
    have h3 : (d : ℝ) ^ 3 * (n : ℝ) ^ 4 ≤ ((d : ℝ) * n) ^ 4 := by
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hd1 (by norm_num)) (by positivity)
    calc 15 * 2 ^ 17 * (d : ℝ) ^ 3 * (n : ℝ) ^ 4 = 15 * 2 ^ 17 * ((d : ℝ) ^ 3 * (n : ℝ) ^ 4) := by ring
      _ ≤ 2 ^ 25 * ((d : ℝ) * n) ^ 25 := by
          have : (15 : ℝ) * 2 ^ 17 ≤ 2 ^ 25 := by norm_num
          exact mul_le_mul this (h3.trans h2) (by positivity) (by norm_num)
      _ = (2 * d * n) ^ 25 := by ring
  unfold lam0
  calc Real.log (n0W d n) ≤ Real.log ((2 * d * n) ^ 25) := Real.log_le_log (by linarith) hle
    _ = 25 * Real.log (2 * d * n) := by rw [Real.log_pow]; norm_num

/-- `log 2 ≤ log(2dn)`. -/
theorem log2_le {n : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n) : Real.log 2 ≤ Real.log (2 * d * n) := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  exact Real.log_le_log (by norm_num) (by nlinarith)

/-- `δ_c = 1/(2^k N_0)`. -/
theorem deltaC_eq (d n k : ℕ) : deltaC d n k = 1 / (2 ^ k * (n0W d n : ℝ)) := by
  unfold deltaC n0W NeO
  push_cast
  rw [pow_add]
  ring

/-- **The budget**: `δ_ref(δ_c) ≤ δ/2`. -/
theorem deltaRefW_le {n : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n) {δ : ℚ} (h0 : 0 < δ) (h1 : δ < 1) :
    deltaRefW n (deltaC d n (kDel δ)) ≤ (δ : ℝ) / 2 := by
  obtain ⟨hk, -⟩ := kDel_bounds h0 h1
  obtain ⟨hN, hnN, -, -⟩ := n0W_bounds hd hn
  have hD0 : (0 : ℝ) < δ := by exact_mod_cast h0
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  set K := (2 : ℝ) ^ kDel δ
  set N := (n0W d n : ℝ)
  have hK0 : 0 < K := by positivity
  have hKδ : 1 < K * δ := by rwa [div_lt_iff₀ hD0] at hk
  have hδc : deltaC d n (kDel δ) = 1 / (K * N) := deltaC_eq d n (kDel δ)
  have hδc0 : 0 < 1 / (K * N) := by positivity
  -- `n/(K N) ≤ δ/(15 · 2^17)` and `1/(K N) ≤ δ/(15 · 2^17)`
  have hNn : 15 * 2 ^ 17 * (n : ℝ) ≤ N := by
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have h4 : (n : ℝ) ≤ (n : ℝ) ^ 4 := le_self_pow₀ hn1 (by norm_num)
    have h3 : (1 : ℝ) ≤ (d : ℝ) ^ 3 := one_le_pow₀ hd1
    have h34 : (n : ℝ) ≤ (d : ℝ) ^ 3 * (n : ℝ) ^ 4 := by nlinarith
    have hNc : N = 15 * 2 ^ 17 * ((d : ℝ) ^ 3 * (n : ℝ) ^ 4) := by
      rw [show N = (n0W d n : ℝ) from rfl, n0W_cast]; ring
    rw [hNc]
    exact mul_le_mul_of_nonneg_left h34 (by norm_num)
  have hN0 : 0 < N := by linarith
  have hnKN : (n : ℝ) / (K * N) ≤ δ / (15 * 2 ^ 17) := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have hKN : N ≤ δ * (K * N) := by nlinarith
    nlinarith
  have h1KN : 1 / (K * N) ≤ δ / (15 * 2 ^ 17) := by
    have : 1 / (K * N) ≤ (n : ℝ) / (K * N) := div_le_div_of_nonneg_right (by exact_mod_cast hn) (by positivity)
    linarith
  unfold deltaRefW
  rw [hδc]
  have e : (n : ℝ) * (149 / 168 * (1 / (K * N))) = 149 / 168 * ((n : ℝ) / (K * N)) := by ring
  rw [e]
  nlinarith

/-- `log 7 ≤ 2`: `7 ≤ e²`. -/
theorem log_seven_le : Real.log 7 ≤ 2 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have he1 := Real.exp_one_gt_d9
  have e : Real.exp 2 = Real.exp 1 ^ 2 := by rw [sq, ← Real.exp_add]; norm_num
  rw [e]
  nlinarith

/-! ## The regret bound at T4U -/

/-- `2ρ/η + n ε ≤ 20000 L⁵ d^{3/2} √n √u`, plus the Azuma term. -/
theorem bRegW_le {n : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n) {u : ℝ} (hu : 0 < u) (δc : ℝ) :
    bRegW d n u δc ≤ 20000 * (parW d n u).Le ^ 5 * (Real.sqrt d ^ 3 * Real.sqrt n * Real.sqrt u) +
      Real.sqrt (2 * n * Real.log (7 / δc)) := by
  have hL := parW_Le_ge hd hn u
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hρ : (parW d n u).rho = 2 * 725 * (d : ℝ) ^ 2 * (parW d n u).Le ^ 3 := by
    show 2 * df2oClam * _ * _ = _; rw [df2oClam]; rfl
  have hη : (parW d n u).eta = Real.sqrt d / ((parW d n u).Le * (Real.sqrt n * Real.sqrt u)) := by
    show Real.sqrt d / (_ * Real.sqrt ((n : ℝ) * u)) = _
    rw [Real.sqrt_mul hn0]; rfl
  have hε : (parW d n u).eps = 20 * 725 * (d * Real.sqrt d) * (parW d n u).Le ^ 5 * Real.sqrt u / Real.sqrt n := by
    show 20 * df2oClam * _ * _ ^ 5 * _ / _ = _; rw [df2oClam]; rfl
  unfold bRegW
  rw [hρ, hη, hε]
  have hbd : (d : ℝ) = Real.sqrt d ^ 2 := (Real.sq_sqrt hd0).symm
  have hcn : (n : ℝ) = Real.sqrt n ^ 2 := (Real.sq_sqrt hn0).symm
  have hb : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hd)
  have hc : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hs : 0 < Real.sqrt u := Real.sqrt_pos.2 hu
  set L := (parW d n u).Le
  set Z := Real.sqrt (2 * n * Real.log (7 / δc))
  set b := Real.sqrt (d : ℝ)
  set c := Real.sqrt (n : ℝ)
  set s := Real.sqrt u
  have e1 : 2 * (2 * 725 * (d : ℝ) ^ 2 * L ^ 3 / (b / (L * (c * s)))) = 2900 * L ^ 4 * (b ^ 3 * c * s) := by
    rw [hbd]; field_simp; ring
  have e2 : (n : ℝ) * (20 * 725 * (d * b) * L ^ 5 * s / c) = 14500 * L ^ 5 * (b ^ 3 * c * s) := by
    rw [hbd, hcn]; field_simp; ring
  rw [e1, e2]
  have hX : 0 ≤ L ^ 4 * (b ^ 3 * c * s) := by positivity
  have h : L ^ 4 * (b ^ 3 * c * s) * 2900 ≤ L ^ 4 * (b ^ 3 * c * s) * (5500 * L) :=
    mul_le_mul_of_nonneg_left (by linarith) hX
  nlinarith

/-- The square roots of the bound: `a = Λ_0^{1/2}`, `b = d^{1/2}`, `c = n^{1/2}`, `e = log(2/δ)^{1/2}`,
`f = log(2dn)^{1/2}`. On the interval `[u_δ, u(k_δ + 1)]`, `√u ≤ 1 + e/(b a)`. -/
theorem sqrt_u_le {n : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n) {δ : ℚ} (h0 : 0 < δ) (h1 : δ < 1) {u : ℝ}
    (hu1 : 0 ≤ u) (hu : u ≤ uF d n (kDel δ + 1)) :
    Real.sqrt u ≤ 1 + Real.sqrt (Real.log (2 / δ)) / (Real.sqrt d * Real.sqrt (lam0 d n)) := by
  obtain ⟨-, hk⟩ := kDel_bounds h0 h1
  have hD0 : (0 : ℝ) < δ := by exact_mod_cast h0
  have hD1 : (δ : ℝ) < 1 := by exact_mod_cast h1
  have hl0 := lam0_ge hd hn
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hlδ : Real.log 2 ≤ Real.log (2 / δ) :=
    Real.log_le_log (by norm_num) (by rw [le_div_iff₀ hD0]; linarith)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  -- `(k + 1) log 2 ≤ 3 log(2/δ)`
  have hk2 : (kDel δ : ℝ) * Real.log 2 ≤ 2 * Real.log (2 / δ) := by
    have h : (kDel δ : ℝ) * Real.log 2 = Real.log ((2 : ℝ) ^ kDel δ) := by rw [Real.log_pow]
    rw [h]
    calc Real.log ((2 : ℝ) ^ kDel δ) ≤ Real.log (4 / δ) := Real.log_le_log (by positivity) hk
      _ = Real.log 2 + Real.log (2 / δ) := by
          rw [← Real.log_mul (by norm_num) (by positivity)]; congr 1; ring
      _ ≤ 2 * Real.log (2 / δ) := by linarith
  have hk3 : ((kDel δ + 1 : ℕ) : ℝ) * Real.log 2 ≤ 3 * Real.log (2 / δ) := by push_cast; linarith
  set e := Real.sqrt (Real.log (2 / δ))
  set a := Real.sqrt (lam0 d n)
  set b := Real.sqrt (d : ℝ)
  have he2 : e ^ 2 = Real.log (2 / δ) := Real.sq_sqrt (by linarith)
  have ha2 : a ^ 2 = lam0 d n := Real.sq_sqrt (by linarith)
  have hb2 : b ^ 2 = d := Real.sq_sqrt (by linarith)
  have ha : 0 < a := Real.sqrt_pos.2 (by linarith)
  have hb : 0 < b := Real.sqrt_pos.2 (by linarith)
  have he : 0 ≤ e := Real.sqrt_nonneg _
  have hx : ((kDel δ + 1 : ℕ) : ℝ) * Real.log 2 / (7 * d * lam0 d n) ≤ (e / (b * a)) ^ 2 := by
    rw [div_pow, mul_pow, ha2, hb2, he2, div_le_div_iff₀ (by positivity) (by positivity)]
    have hdl : 0 ≤ (d : ℝ) * lam0 d n := mul_nonneg (by linarith) (by linarith)
    have h3 := mul_le_mul_of_nonneg_right hk3 hdl
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ Real.log (2 / δ)) hdl]
  have hu2 : u ≤ (1 + e / (b * a)) ^ 2 := by
    calc u ≤ uF d n (kDel δ + 1) := hu
      _ = 1 + ((kDel δ + 1 : ℕ) : ℝ) * Real.log 2 / (7 * d * lam0 d n) := rfl
      _ ≤ 1 + (e / (b * a)) ^ 2 := by linarith
      _ ≤ (1 + e / (b * a)) ^ 2 := by have : 0 ≤ e / (b * a) := by positivity
                                      nlinarith
  calc Real.sqrt u ≤ Real.sqrt ((1 + e / (b * a)) ^ 2) := Real.sqrt_le_sqrt hu2
    _ = 1 + e / (b * a) := Real.sqrt_sq (by positivity)


/-- The threshold in the square roots `b = d^{1/2}`, `c = n^{1/2}`, `e = log(2/δ)^{1/2}`, `f = log(2dn)^{1/2}`:
`thrUW C = C (b³ c f^{10} + b² c e f⁹)`. -/
theorem thrUW_eq (C : ℝ) {n : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n) (δ : ℚ) :
    thrUW C d n δ = C * (Real.sqrt d ^ 3 * Real.sqrt n * Real.sqrt (Real.log (2 * d * n)) ^ 10 +
      Real.sqrt d ^ 2 * Real.sqrt n * Real.sqrt (Real.log (2 / δ)) * Real.sqrt (Real.log (2 * d * n)) ^ 9) := by
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hl2 : 0 ≤ Real.log (2 * d * n) := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le.trans (log2_le hd hn)
  have r1 : (d : ℝ) ^ (3 / 2 : ℝ) = Real.sqrt d ^ 3 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hd0]; norm_num
  have r2 : Real.log (2 * d * n) ^ (9 / 2 : ℝ) = Real.sqrt (Real.log (2 * d * n)) ^ 9 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hl2]; norm_num
  have r3 : Real.log (2 * d * n) ^ 5 = Real.sqrt (Real.log (2 * d * n)) ^ 10 := by
    rw [show (10 : ℕ) = 2 * 5 by norm_num, pow_mul, Real.sq_sqrt hl2]
  have r4 : Real.sqrt (n * Real.log (2 / (δ : ℝ))) = Real.sqrt n * Real.sqrt (Real.log (2 / δ)) := Real.sqrt_mul hn0 _
  unfold thrUW
  rw [r1, r2, r3, r4]
  rw [Real.sq_sqrt hd0]
  ring

/-- `(36 a²)⁵ b³ c s ≤ 36⁵ 5^{10} (b³ c f^{10} + b² c e f⁹)` for `0 ≤ s ≤ 1 + e/(b a)` and `a ≤ 5 f`. -/
theorem thr_main (a b c e f : ℝ) (ha : 0 < a) (hb1 : 1 ≤ b) (hc0 : 0 ≤ c) (he0 : 0 ≤ e) (hf0 : 0 ≤ f)
    (haf : a ≤ 5 * f) (s : ℝ) (hs0 : 0 ≤ s) (hs : s ≤ 1 + e / (b * a)) :
    (36 * a ^ 2) ^ 5 * (b ^ 3 * c * s) ≤ 36 ^ 5 * 5 ^ 10 * (b ^ 3 * c * f ^ 10 + b ^ 2 * c * e * f ^ 9) := by
  have hb0 : 0 < b := by linarith
  have h10 : a ^ 10 ≤ 5 ^ 10 * f ^ 10 := by
    calc a ^ 10 ≤ (5 * f) ^ 10 := pow_le_pow_left₀ ha.le haf 10
      _ = 5 ^ 10 * f ^ 10 := by ring
  have h9 : a ^ 9 ≤ 5 ^ 10 * f ^ 9 := by
    have hf9 : 0 ≤ f ^ 9 := by positivity
    calc a ^ 9 ≤ (5 * f) ^ 9 := pow_le_pow_left₀ ha.le haf 9
      _ = 5 ^ 9 * f ^ 9 := by ring
      _ ≤ 5 ^ 10 * f ^ 9 := by linarith
  have e1 : (36 * a ^ 2) ^ 5 * (b ^ 3 * c * (1 + e / (b * a))) =
      36 ^ 5 * (a ^ 10 * (b ^ 3 * c) + a ^ 9 * (b ^ 2 * c * e)) := by
    field_simp
  have hbc : 0 ≤ b ^ 3 * c := by positivity
  have hbce : 0 ≤ b ^ 2 * c * e := by positivity
  calc (36 * a ^ 2) ^ 5 * (b ^ 3 * c * s) ≤ (36 * a ^ 2) ^ 5 * (b ^ 3 * c * (1 + e / (b * a))) := by
        gcongr
    _ = 36 ^ 5 * (a ^ 10 * (b ^ 3 * c) + a ^ 9 * (b ^ 2 * c * e)) := e1
    _ ≤ 36 ^ 5 * (5 ^ 10 * f ^ 10 * (b ^ 3 * c) + 5 ^ 10 * f ^ 9 * (b ^ 2 * c * e)) := by gcongr
    _ = 36 ^ 5 * 5 ^ 10 * (b ^ 3 * c * f ^ 10 + b ^ 2 * c * e * f ^ 9) := by ring

/-- The lower-order terms against `T1 = b³ c f^{10}` and `T2 = b² c e f⁹`, for `f ≥ 0.83`. -/
theorem thr_T (b c e f : ℝ) (hb1 : 1 ≤ b) (hc1 : 1 ≤ c) (he0 : 0 ≤ e) (hf83 : 83 / 100 ≤ f) :
    c * f ≤ 6 * (b ^ 3 * c * f ^ 10) ∧ c * e ≤ 6 * (b ^ 2 * c * e * f ^ 9) ∧ 1 ≤ 7 * (b ^ 3 * c * f ^ 10) := by
  have hf0 : 0 ≤ f := by linarith
  have hf9 : 1 / 6 ≤ f ^ 9 := by
    calc (1 / 6 : ℝ) ≤ (83 / 100) ^ 9 := by norm_num
      _ ≤ f ^ 9 := pow_le_pow_left₀ (by norm_num) hf83 9
  have hf10 : 1 / 7 ≤ f ^ 10 := by
    calc (1 / 7 : ℝ) ≤ (83 / 100) ^ 10 := by norm_num
      _ ≤ f ^ 10 := pow_le_pow_left₀ (by norm_num) hf83 10
  have hb3 : 1 ≤ b ^ 3 := one_le_pow₀ hb1
  have hb2 : 1 ≤ b ^ 2 := one_le_pow₀ hb1
  refine ⟨?_, ?_, ?_⟩
  · have h6 : 1 ≤ 6 * f ^ 9 * b ^ 3 := by
      have := mul_le_mul hf9 hb3 (by norm_num) (by positivity)
      linarith
    have := mul_le_mul_of_nonneg_left h6 (by positivity : 0 ≤ c * f)
    linarith
  · have h6 : 1 ≤ 6 * f ^ 9 * b ^ 2 := by
      have := mul_le_mul hf9 hb2 (by norm_num) (by positivity)
      linarith
    have := mul_le_mul_of_nonneg_left h6 (by positivity : 0 ≤ c * e)
    linarith
  · have h1 : 1 ≤ b ^ 3 * c := one_le_mul_of_one_le_of_one_le hb3 hc1
    have := mul_le_mul h1 hf10 (by norm_num) (by positivity)
    linarith

/-- The Azuma term: `(2 n ℓ_c)^{1/2} ≤ c (8 f + 2 e)` for `c² = n` and `ℓ_c ≤ 28 f² + 2 e²`. -/
theorem thr_az (n lc c e f : ℝ) (hc2 : c ^ 2 = n) (hc0 : 0 ≤ c) (he0 : 0 ≤ e) (hf0 : 0 ≤ f)
    (hlc : lc ≤ 28 * f ^ 2 + 2 * e ^ 2) : Real.sqrt (2 * n * lc) ≤ c * (8 * f + 2 * e) := by
  have h3 : 2 * (28 * f ^ 2 + 2 * e ^ 2) ≤ (8 * f + 2 * e) ^ 2 := by
    nlinarith [mul_nonneg hf0 he0, sq_nonneg f]
  have hc20 : 0 ≤ c ^ 2 := sq_nonneg c
  have h2 : 2 * n * lc ≤ (c * (8 * f + 2 * e)) ^ 2 := by
    rw [← hc2]
    calc 2 * c ^ 2 * lc ≤ c ^ 2 * (2 * (28 * f ^ 2 + 2 * e ^ 2)) := by
          have := mul_le_mul_of_nonneg_left hlc hc20
          linarith
      _ ≤ c ^ 2 * (8 * f + 2 * e) ^ 2 := mul_le_mul_of_nonneg_left h3 hc20
      _ = (c * (8 * f + 2 * e)) ^ 2 := by ring
  calc Real.sqrt (2 * n * lc) ≤ Real.sqrt ((c * (8 * f + 2 * e)) ^ 2) := Real.sqrt_le_sqrt h2
    _ = c * (8 * f + 2 * e) := Real.sqrt_sq (by positivity)

/-- The constant of Lemma thr at T4U. -/
noncomputable def cThr : ℝ := 10 ^ 21

/-- **Lemma thr at T4U.** -/
theorem thrUW_holds : ThrUW cThr := by
  intro d n δ hd hn h0 h1
  have hD0 : (0 : ℝ) < δ := by exact_mod_cast h0
  have hD1 : (δ : ℝ) < 1 := by exact_mod_cast h1
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hl0 := lam0_ge hd hn
  have hl0' := lam0_le hd hn
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hl2 := log2_le hd hn
  have hlδ : Real.log 2 ≤ Real.log (2 / δ) :=
    Real.log_le_log (by norm_num) (by rw [le_div_iff₀ hD0]; linarith)
  set a := Real.sqrt (lam0 d n) with ha_def
  set b := Real.sqrt (d : ℝ) with hb_def
  set c := Real.sqrt (n : ℝ) with hc_def
  set e := Real.sqrt (Real.log (2 / δ)) with he_def
  set f := Real.sqrt (Real.log (2 * d * n)) with hf_def
  have ha2 : a ^ 2 = lam0 d n := Real.sq_sqrt (by linarith)
  have hb2 : b ^ 2 = d := Real.sq_sqrt (by linarith)
  have hc2 : c ^ 2 = n := Real.sq_sqrt (by linarith)
  have he2 : e ^ 2 = Real.log (2 / δ) := Real.sq_sqrt (by linarith)
  have hf2 : f ^ 2 = Real.log (2 * d * n) := Real.sq_sqrt (by linarith)
  have ha : 0 < a := Real.sqrt_pos.2 (by linarith)
  have hb1 : 1 ≤ b := by rw [hb_def, Real.one_le_sqrt]; exact hd1
  have hc1 : 1 ≤ c := by rw [hc_def, Real.one_le_sqrt]; exact hn1
  have he0 : 0 ≤ e := Real.sqrt_nonneg _
  have hf0 : 0 ≤ f := Real.sqrt_nonneg _
  have hf83 : 83 / 100 ≤ f := by
    rw [hf_def, Real.le_sqrt (by norm_num) (by linarith)]; linarith
  have haf : a ≤ 5 * f := by
    have : a ^ 2 ≤ (5 * f) ^ 2 := by rw [mul_pow, hf2, ha2]; linarith
    exact (pow_le_pow_iff_left₀ ha.le (by positivity) (by norm_num)).1 this
  set T1 := b ^ 3 * c * f ^ 10 with hT1
  set T2 := b ^ 2 * c * e * f ^ 9 with hT2
  have hT10 : 0 ≤ T1 := by positivity
  have hT20 : 0 ≤ T2 := by positivity
  have hthr : thrUW cThr d n δ = cThr * (T1 + T2) := thrUW_eq cThr hd hn δ
  have hmain : ∀ s : ℝ, 0 ≤ s → s ≤ 1 + e / (b * a) →
      (36 * a ^ 2) ^ 5 * (b ^ 3 * c * s) ≤ 36 ^ 5 * 5 ^ 10 * (T1 + T2) :=
    fun s hs0 hs => thr_main a b c e f ha hb1 (by linarith) he0 hf0 haf s hs0 hs
  obtain ⟨hcf, hce, hone⟩ := thr_T b c e f hb1 hc1 he0 hf83
  replace hcf : c * f ≤ 6 * T1 := hcf
  replace hce : c * e ≤ 6 * T2 := hce
  replace hone : 1 ≤ 7 * T1 := hone
  -- `u(k_δ) ≤ u(k_δ + 1)` and `1 ≤ u(k_δ)`
  have hl0pos : 0 < 7 * (d : ℝ) * lam0 d n := by positivity
  have huF1 : 1 ≤ uF d n (kDel δ) := by
    unfold uF; have : 0 ≤ (kDel δ : ℝ) * Real.log 2 / (7 * d * lam0 d n) := by positivity
    linarith
  have huF2 : uF d n (kDel δ) ≤ uF d n (kDel δ + 1) := by
    unfold uF; push_cast
    have : (kDel δ : ℝ) * Real.log 2 ≤ ((kDel δ : ℝ) + 1) * Real.log 2 := by linarith
    have := div_le_div_of_nonneg_right this hl0pos.le
    linarith
  refine ⟨by rw [hthr]; unfold cThr; positivity, deltaRefW_le hd hn h0 h1, ?_, ?_⟩
  · intro _ u hu1 hu2
    have hu0 : 1 ≤ u := huF1.trans hu1
    have hs := sqrt_u_le hd hn h0 h1 (by linarith) hu2
    have hreg := bRegW_le hd hn (by linarith : 0 < u) (deltaC d n (kDel δ))
    have hL : (parW d n u).Le = 36 * a ^ 2 := by rw [parW_Le_lam0, ha2]
    rw [hL] at hreg
    have hm := hmain (Real.sqrt u) (Real.sqrt_nonneg _) hs
    -- the Azuma term
    obtain ⟨-, hk⟩ := kDel_bounds h0 h1
    have hk2 : (kDel δ : ℝ) * Real.log 2 ≤ 2 * Real.log (2 / δ) := by
      have h : (kDel δ : ℝ) * Real.log 2 = Real.log ((2 : ℝ) ^ kDel δ) := by rw [Real.log_pow]
      rw [h]
      calc Real.log ((2 : ℝ) ^ kDel δ) ≤ Real.log (4 / δ) := Real.log_le_log (by positivity) hk
        _ = Real.log 2 + Real.log (2 / δ) := by
            rw [← Real.log_mul (by norm_num) (by positivity)]; congr 1; ring
        _ ≤ 2 * Real.log (2 / δ) := by linarith
    have hlogc : Real.log (7 / deltaC d n (kDel δ)) = Real.log 7 + (kDel δ : ℝ) * Real.log 2 + lam0 d n := by
      obtain ⟨hN, -, -, -⟩ := n0W_bounds hd hn
      have hN0 : (0 : ℝ) < n0W d n := by linarith
      have hK0 : (0 : ℝ) < 2 ^ kDel δ := by positivity
      rw [deltaC_eq, one_div, div_inv_eq_mul, Real.log_mul (by norm_num) (by positivity),
        Real.log_mul hK0.ne' hN0.ne', Real.log_pow]
      unfold lam0
      ring
    have hl7 := log_seven_le
    have hlc : Real.log (7 / deltaC d n (kDel δ)) ≤ 28 * f ^ 2 + 2 * e ^ 2 := by
      rw [hlogc, hf2, he2]; linarith
    have haz := thr_az (n : ℝ) (Real.log (7 / deltaC d n (kDel δ))) c e f hc2 (by linarith) he0 hf0 hlc
    rw [hthr]
    have hX : 20000 * (36 * a ^ 2) ^ 5 * (b ^ 3 * c * Real.sqrt u) ≤ 20000 * (36 ^ 5 * 5 ^ 10 * (T1 + T2)) := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hm (by norm_num)
    rw [← hb_def, ← hc_def] at hreg
    unfold cThr
    linarith
  · intro hnc
    -- `ε(u_δ) > 1/8` gives `n < 116000 b³ L⁵ √u_δ c`
    have hε : 1 / 8 < (parW d n (uF d n (kDel δ))).eps := lt_of_not_ge hnc
    have hs := sqrt_u_le hd hn h0 h1 (by linarith) huF2
    have hm := hmain (Real.sqrt (uF d n (kDel δ))) (Real.sqrt_nonneg _) hs
    have hεv : (parW d n (uF d n (kDel δ))).eps =
        14500 * (b ^ 3) * (36 * a ^ 2) ^ 5 * Real.sqrt (uF d n (kDel δ)) / c := by
      have hL : (parW d n (uF d n (kDel δ))).Le = 36 * a ^ 2 := by rw [parW_Le_lam0, ha2]
      show 20 * df2oClam * ((d : ℝ) * Real.sqrt d) * (parW d n (uF d n (kDel δ))).Le ^ 5 *
        Real.sqrt (uF d n (kDel δ)) / Real.sqrt n = _
      rw [hL, df2oClam, ← hb_def, ← hc_def, ← hb2]
      ring
    rw [hεv, lt_div_iff₀ (by linarith)] at hε
    rw [hthr, ← hc2]
    have hc0 : 0 ≤ c := by linarith
    have h1 : c ^ 2 ≤ 8 * (14500 * b ^ 3 * (36 * a ^ 2) ^ 5 * Real.sqrt (uF d n (kDel δ))) * c := by
      have := mul_le_mul_of_nonneg_right hε.le hc0
      linarith
    have h2 : 8 * (14500 * b ^ 3 * (36 * a ^ 2) ^ 5 * Real.sqrt (uF d n (kDel δ))) * c =
        116000 * ((36 * a ^ 2) ^ 5 * (b ^ 3 * c * Real.sqrt (uF d n (kDel δ)))) := by ring
    unfold cThr
    linarith

end AdversarialBco.UW
