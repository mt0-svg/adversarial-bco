/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import Mathlib

@[expose] public section

/-!
# The arithmetic of `Df2SIFacts`

Inequalities between reals that the items of `Df2SIFacts` read at the parameters of `df2oPar`
: the Lipschitz constant of the extension (X1), the exponent and the constant of
the shift under the split (X4), the lower bound of the surrogate (X2), the tail of prop:lower (X3), the facts of `δ_e`.
-/

namespace AdversarialBco.Poly.SIF

/-- X1: `1/ε + (2 + 2/ε)/(1 - ε) ≤ 8/ε` for `0 < ε ≤ 1/2`. -/
theorem ext_lip_arith (ε : ℝ) (h0 : 0 < ε) (h1 : ε ≤ 1 / 2) : 1 / ε + (2 + 2 / ε) / (1 - ε) ≤ 8 / ε := by
  have h1e : 0 < 1 - ε := by linarith
  have key : 8 / ε - (1 / ε + (2 + 2 / ε) / (1 - ε)) = (5 - 9 * ε) / (ε * (1 - ε)) := by
    field_simp
    ring
  have : 0 ≤ (5 - 9 * ε) / (ε * (1 - ε)) := div_nonneg (by linarith) (by positivity)
  linarith

/-- X4, the exponent: for `t L ≤ 21/10`, `L ≥ 504`, `log 2 - t/2 ≥ 0` and `(log 2 - t/2)²/(2t) ≥ L/10`. -/
theorem tail_exponent_arith (L t : ℝ) (hL : 504 ≤ L) (ht0 : 0 < t) (ht : t * L ≤ 21 / 10) :
    0 ≤ Real.log 2 - t / 2 ∧ L / 10 ≤ (Real.log 2 - t / 2) ^ 2 / (2 * t) := by
  have hlog2 := Real.log_two_gt_d9
  have htL : t * 504 ≤ t * L := mul_le_mul_of_nonneg_left hL ht0.le
  have hb : (69 / 100 : ℝ) ≤ Real.log 2 - t / 2 := by linarith
  refine ⟨by linarith, ?_⟩
  rw [le_div_iff₀ (by positivity)]
  nlinarith [mul_le_mul hb hb (by norm_num) (by linarith)]

/-- `e^{-L/10} ≤ δ³` for `L = 36 log(1/δ)`, `0 < δ ≤ 1`. -/
theorem exp_Le_arith (δ L : ℝ) (h0 : 0 < δ) (h1 : δ ≤ 1) (hL : L = 36 * Real.log (1 / δ)) :
    Real.exp (-(L / 10)) ≤ δ ^ 3 := by
  have hlog : Real.log δ ≤ 0 := Real.log_nonpos h0.le h1
  have hL' : L = -(36 * Real.log δ) := by rw [hL, one_div, Real.log_inv]; ring
  calc Real.exp (-(L / 10)) ≤ Real.exp ((3 : ℕ) * Real.log δ) := by
        refine Real.exp_le_exp.mpr ?_
        rw [hL']; push_cast; linarith
    _ = δ ^ 3 := by rw [Real.exp_nat_mul, Real.exp_log h0]

/-- X4, the constant: with `a ≤ (2σ²)^{1/2} b`, `q ≤ δ³/2`, `1/ε ≤ n`, `n δ ≤ 1`, `4 δ ≤ 1`:
`λ (8/ε) a b q/((1 - λ) (1/2)^{1/2}) ≤ δ b²`. -/
theorem x4_const_arith (lam eps σ2 de n a b q : ℝ) (hl0 : 0 < lam) (hl : lam ≤ 1 / 2) (he : 0 < eps)
    (hen : 1 / eps ≤ n) (hnd : n * de ≤ 1) (hd0 : 0 < de) (hd4 : 4 * de ≤ 1) (_hσ0 : 0 ≤ σ2) (hσ : σ2 ≤ 1 / 4)
    (ha0 : 0 ≤ a) (ha : a ≤ Real.sqrt (2 * σ2) * b) (hb : 0 ≤ b) (hq0 : 0 ≤ q) (hq : q ≤ de ^ 3 / 2) :
    lam * (8 / eps) * (a * b) / ((1 - lam) * Real.sqrt (1 / 2)) * q ≤ de * b ^ 2 := by
  have h1l : 0 < 1 - lam := by linarith
  have hn0 : 0 < n := lt_of_lt_of_le (by positivity) hen
  have hr : 0 < Real.sqrt (1 / 2) := Real.sqrt_pos.mpr (by norm_num)
  have hs : Real.sqrt (2 * σ2) ≤ Real.sqrt (1 / 2) := Real.sqrt_le_sqrt (by linarith)
  have ha' : a ≤ Real.sqrt (1 / 2) * b := ha.trans (mul_le_mul_of_nonneg_right hs hb)
  have hab : a * b / Real.sqrt (1 / 2) ≤ b ^ 2 := by
    rw [div_le_iff₀ hr]; nlinarith
  have hab0 : 0 ≤ a * b / Real.sqrt (1 / 2) := div_nonneg (mul_nonneg ha0 hb) hr.le
  have hlr : lam / (1 - lam) ≤ 1 := by rw [div_le_one h1l]; linarith
  have h8 : 8 / eps ≤ 8 * n := by
    have : 8 / eps = 8 * (1 / eps) := by ring
    rw [this]; linarith
  have heq : lam * (8 / eps) * (a * b) / ((1 - lam) * Real.sqrt (1 / 2)) * q =
      lam / (1 - lam) * (8 / eps) * (a * b / Real.sqrt (1 / 2)) * q := by
    field_simp
  rw [heq]
  have hAB : lam / (1 - lam) * (8 / eps) ≤ 1 * (8 * n) :=
    mul_le_mul hlr h8 (by positivity) zero_le_one
  have hABC : lam / (1 - lam) * (8 / eps) * (a * b / Real.sqrt (1 / 2)) ≤ 1 * (8 * n) * b ^ 2 :=
    mul_le_mul hAB hab hab0 (by nlinarith)
  calc lam / (1 - lam) * (8 / eps) * (a * b / Real.sqrt (1 / 2)) * q ≤ 1 * (8 * n) * b ^ 2 * (de ^ 3 / 2) :=
        mul_le_mul hABC hq hq0 (by nlinarith [sq_nonneg b])
    _ = 4 * (n * de) * (de ^ 2 * b ^ 2) := by ring
    _ ≤ 4 * 1 * (de ^ 2 * b ^ 2) := by gcongr
    _ ≤ de * b ^ 2 := by nlinarith [sq_nonneg b, mul_nonneg (sq_nonneg de) (sq_nonneg b)]

/-- X2, the constant: `(8/ε)(2R + I) ≤ 10/(λ ε)` at `λ = 1/(725 d L²)`, `R = 134 d (log(2d + 2))^{1/2}`,
`log(2d + 2) ≤ L/36`, `I ≤ d`. -/
theorem x2_arith (d L R eps lam I : ℝ) (hd : 1 ≤ d) (hL : 504 ≤ L) (hlam : lam = 1 / (725 * d * L ^ 2))
    (hR : R = 134 * d * Real.sqrt (Real.log (2 * d + 2))) (hlog : Real.log (2 * d + 2) ≤ L / 36) (he : 0 < eps)
    (hI : I ≤ d) : 8 / eps * (2 * R + I) ≤ 10 / (lam * eps) := by
  have hL1 : 1 ≤ L := by linarith
  have hlog0 : 0 ≤ Real.log (2 * d + 2) := Real.log_nonneg (by linarith)
  have hsq : Real.sqrt (Real.log (2 * d + 2)) ≤ L := by
    rw [Real.sqrt_le_left (by linarith)]; nlinarith
  have hR' : R ≤ 134 * d * L := by
    rw [hR]; exact mul_le_mul_of_nonneg_left hsq (by linarith)
  have heq : 10 / (lam * eps) = 7250 * d * L ^ 2 / eps := by
    rw [hlam]; field_simp; ring
  rw [heq, div_mul_eq_mul_div, div_le_div_iff_of_pos_right he]
  have hdL : d * L * 504 ≤ d * L ^ 2 := by
    have := mul_le_mul_of_nonneg_left hL (mul_nonneg (by linarith : (0 : ℝ) ≤ d) (by linarith : (0 : ℝ) ≤ L))
    nlinarith
  have hdL2 : d ≤ d * L := by nlinarith
  nlinarith

/-- X3, the tail term: with `M = λ (8/ε) (2σ²)^{1/2}/(1 - λ)`, `ρ² = (2 - λ)/λ`, `T = 1/(L λ² ρ²)`:
`(M/2) ρ² · 8 · 2^{d/2} e^{-T/8} ≤ δ d/λ`. -/
theorem x3_tail_arith (d : ℕ) (hd : 1 ≤ d) (L lam eps σ2 de n : ℝ) (hL : 504 ≤ L)
    (hlam : lam = 1 / (725 * d * L ^ 2)) (hσ : σ2 = 1 / (8 * L)) (he : 0 < eps) (hen : 1 / eps ≤ n)
    (hnd : n * de ≤ 1) (hd0 : 0 < de) (hd1 : 128 * de ≤ 1) (hLde : L = 36 * Real.log (1 / de)) :
    lam * (8 / eps) * Real.sqrt (2 * σ2) / (1 - lam) / 2 * ((2 - lam) / lam) *
        (8 * Real.sqrt 2 ^ d * Real.exp (-(1 / (L * lam ^ 2 * ((2 - lam) / lam)) / 8))) ≤
      de * d / lam := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hL0 : 0 < L := by linarith
  have hlam0 : 0 < lam := by rw [hlam]; positivity
  have hlam1 : lam ≤ 1 / 100 := by
    rw [hlam, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have h1l : 0 < 1 - lam := by linarith
  have hn0 : 0 < n := lt_of_lt_of_le (by positivity) hen
  have hde1 : de ≤ 1 := by linarith
  -- the prefactor
  have hs : Real.sqrt (2 * σ2) ≤ 1 := by
    rw [Real.sqrt_le_one, hσ, mul_one_div, div_le_one (by positivity)]; linarith
  have hP : lam * (8 / eps) * Real.sqrt (2 * σ2) / (1 - lam) / 2 * ((2 - lam) / lam) ≤ 16 * n := by
    have heq : lam * (8 / eps) * Real.sqrt (2 * σ2) / (1 - lam) / 2 * ((2 - lam) / lam) =
        8 / eps * Real.sqrt (2 * σ2) * ((2 - lam) / (2 * (1 - lam))) := by
      field_simp
    rw [heq]
    have h2 : (2 - lam) / (2 * (1 - lam)) ≤ 2 := by rw [div_le_iff₀ (by positivity)]; linarith
    have h8 : 8 / eps ≤ 8 * n := by
      have : 8 / eps = 8 * (1 / eps) := by ring
      rw [this]; linarith
    calc 8 / eps * Real.sqrt (2 * σ2) * ((2 - lam) / (2 * (1 - lam))) ≤ 8 * n * 1 * 2 :=
          mul_le_mul (mul_le_mul h8 hs (Real.sqrt_nonneg _) (by linarith)) h2
            (div_nonneg (by linarith) (by positivity)) (by linarith)
      _ = 16 * n := by ring
  -- the exponent
  have hX : 725 / 2 * (d * L) ≤ 1 / (L * lam ^ 2 * ((2 - lam) / lam)) := by
    have hq : L * lam ^ 2 * ((2 - lam) / lam) = L * lam * (2 - lam) := by field_simp
    rw [hq, le_div_iff₀ (mul_pos (mul_pos hL0 hlam0) (by linarith))]
    have key : 725 / 2 * (d * L) * (L * lam * (2 - lam)) = (2 - lam) / 2 := by
      rw [hlam]; field_simp
    rw [key]; linarith
  have hdL : L ≤ d * L := by nlinarith
  have hdL2 : (d : ℝ) ≤ d * L := by nlinarith
  have hsq : Real.sqrt 2 ^ d ≤ Real.exp d := by
    have h1 : Real.sqrt 2 ≤ Real.exp 1 := by
      have h1 : Real.sqrt 2 ≤ 2 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
      have h2 : (2 : ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp 1; linarith
      linarith
    calc Real.sqrt 2 ^ d ≤ Real.exp 1 ^ d := pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 d
      _ = Real.exp d := by rw [← Real.exp_nat_mul, mul_one]
  have hE := exp_Le_arith de L hd0 hde1 hLde
  have hQ : 8 * Real.sqrt 2 ^ d * Real.exp (-(1 / (L * lam ^ 2 * ((2 - lam) / lam)) / 8)) ≤ 8 * de ^ 3 := by
    have h1 : Real.exp (-(1 / (L * lam ^ 2 * ((2 - lam) / lam)) / 8)) ≤ Real.exp (-(45 * (d * L))) :=
      Real.exp_le_exp.mpr (by linarith)
    have h2 : Real.exp d * Real.exp (-(45 * (d * L))) ≤ Real.exp (-(L / 10)) := by
      rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith)
    calc 8 * Real.sqrt 2 ^ d * Real.exp (-(1 / (L * lam ^ 2 * ((2 - lam) / lam)) / 8)) ≤
        8 * Real.exp d * Real.exp (-(45 * (d * L))) := by gcongr
      _ = 8 * (Real.exp d * Real.exp (-(45 * (d * L)))) := by ring
      _ ≤ 8 * de ^ 3 := by linarith
  have hQ0 : 0 ≤ 8 * Real.sqrt 2 ^ d * Real.exp (-(1 / (L * lam ^ 2 * ((2 - lam) / lam)) / 8)) := by positivity
  have hdl : 1 ≤ d / lam := by
    rw [hlam, div_div_eq_mul_div, div_one]
    nlinarith
  calc _ ≤ 16 * n * (8 * de ^ 3) := mul_le_mul hP hQ hQ0 (by linarith)
    _ = 128 * (n * de) * de ^ 2 := by ring
    _ ≤ 128 * 1 * de ^ 2 := by gcongr
    _ ≤ de := by nlinarith
    _ ≤ de * (d / lam) := le_mul_of_one_le_right hd0.le hdl
    _ = de * d / lam := by ring

/-- The facts of `δ_e = 4 δ₁/(5 n)` for `δ₁ ≤ e^{-14}/(d n)³`: `(2d + 2) δ_e ≤ 1`, `128 δ_e ≤ 1`, `n δ_e ≤ 1`. -/
theorem de_arith (d n δ1 : ℝ) (hd : 1 ≤ d) (hn : 1 ≤ n) (h0 : 0 < δ1) (h1 : δ1 ≤ Real.exp (-14) / (d * n) ^ 3) :
    (2 * d + 2) * (4 * δ1 / (5 * n)) ≤ 1 ∧ 128 * (4 * δ1 / (5 * n)) ≤ 1 ∧ n * (4 * δ1 / (5 * n)) ≤ 1 := by
  have h14 : (2 : ℝ) ^ 14 ≤ Real.exp 14 := by
    have h := Real.add_one_le_exp 1
    calc (2 : ℝ) ^ 14 ≤ Real.exp 1 ^ 14 := pow_le_pow_left₀ (by norm_num) (by linarith) 14
      _ = Real.exp 14 := by rw [← Real.exp_nat_mul]; norm_num
  have hEE : Real.exp (-14) * Real.exp 14 = 1 := by rw [← Real.exp_add]; norm_num
  have hE0 : 0 < Real.exp (-14) := Real.exp_pos _
  have hE : Real.exp (-14) ≤ 1 / 16384 := by nlinarith
  have hdn : 1 ≤ d * n := by nlinarith
  have hdn3 : d ≤ (d * n) ^ 3 := by nlinarith [pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ 1) hdn 2]
  have hd3 : δ1 * (d * n) ^ 3 ≤ Real.exp (-14) := by rwa [le_div_iff₀ (by positivity)] at h1
  have hδE : δ1 ≤ Real.exp (-14) := by nlinarith
  have hq : 4 * δ1 / (5 * n) ≤ 4 * δ1 / 5 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hq0 : 0 ≤ 4 * δ1 / (5 * n) := by positivity
  refine ⟨?_, ?_, ?_⟩
  · calc (2 * d + 2) * (4 * δ1 / (5 * n)) ≤ (4 * d) * (4 * δ1 / 5) :=
          mul_le_mul (by linarith) hq hq0 (by linarith)
      _ = 16 / 5 * (d * δ1) := by ring
      _ ≤ 16 / 5 * (δ1 * (d * n) ^ 3) := by nlinarith
      _ ≤ 1 := by nlinarith
  · nlinarith
  · rw [mul_div_assoc', div_le_one (by positivity)]; nlinarith

end AdversarialBco.Poly.SIF
