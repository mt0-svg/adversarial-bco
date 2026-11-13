/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.Df2EvSIRound
public import AdversarialBco.Poly.CoverProof
public import AdversarialBco.Poly.Df2SIFactsProof

@[expose] public section

/-!
# The event S-DF: the parts

The parts of Lemma S-DF (with `P̄`): on every instance of setting (E), the event G holds and S-DF fails with
probability at most `δ_e/7`.

On a path with the hypotheses of DET without the events (`DetBase`), at a round `t ≤ τ`, with
`A_t = ∑_{u ≤ t} (ŝ''_u - s''_u(μ_u))`:

* `P' - P̄_{t+1} = η κ A_t` (`Pn_sub_PBar`);
* `q_t(v) = 2 vᵀ P̄_t v` dominates `vᵀ P_s v` for `s ≤ t` and `4 δ |v|² ≤ q_t(v) ≤ |v|²/δ`;
* on G, `|vᵀ ŝ''_s v| + |vᵀ s''_s(μ_s) v| ≤ Rc vᵀ P_s v` (`round_le`).

Lemma U (`lemmaU_setE`) runs over a net `C` of the unit ball at scale `δ⁴` with the directions
`phiH (fun _ => c)`, `κ = δ⁻²`, `δ' = δ/7`, the variance cap `(λ κ₀)² q² Xv` (Lemma TR with `√T = 16 x`, the sum of
the second moments, the fourth moment) and the range cap `Rc q + δ²`. On G and not S-DF, a unit direction `u` and a
round `t ≤ τ` break the bound; the net point next to `u` lies in the bad event of Lemma U (`sdf_final`).
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal NNReal Matrix

namespace AdversarialBco.Poly.EvSI.SDF

open Layer2

variable {d : ℕ}

/-! ## Arithmetic -/

theorem log_level_le (d : ℕ) (hd : 1 ≤ d) (δ n Cc Rc q lk Xv : ℝ) (hδ0 : 0 < δ)
    (hx : 14 ≤ Real.log (1 / δ)) (hn0 : 1 ≤ n) (hn : n * δ ≤ 1) (hC0 : 1 ≤ Cc) (hC : Cc ≤ (1 + 2 * 1 / δ ^ 4) ^ d)
    (hRc0 : 0 ≤ Rc) (hRc : Rc * δ ≤ 1) (hq0 : 0 ≤ q) (hq : q * δ ≤ 1) (hlk : 0 ≤ lk) (hXv : 0 ≤ Xv)
    (hlX : lk * Real.sqrt Xv * δ ≤ 1) :
    0 ≤ Real.log (4 * (n * Cc) * max ((δ ^ 2)⁻¹ * (Rc * q + δ ^ 2)) ((δ ^ 2)⁻¹ * Real.sqrt (lk ^ 2 * q ^ 2 * Xv)) /
        (δ / 7)) ∧
      Real.log (4 * (n * Cc) * max ((δ ^ 2)⁻¹ * (Rc * q + δ ^ 2)) ((δ ^ 2)⁻¹ * Real.sqrt (lk ^ 2 * q ^ 2 * Xv)) /
        (δ / 7)) ≤ 12 * d * Real.log (1 / δ) := by
  set Y := 1 / δ with hYdef
  have hY0 : 0 < Y := by positivity
  have hδY : δ * Y = 1 := by rw [hYdef]; field_simp
  have hYe : Real.exp 14 ≤ Y := by
    have h := Real.exp_le_exp.2 hx
    rwa [Real.exp_log hY0] at h
  have hY56 : 56 ≤ Y := by
    have h := Real.quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 14)
    linarith
  have hY1 : 1 ≤ Y := by linarith
  have hinv2 : (δ ^ 2)⁻¹ = Y ^ 2 := by rw [hYdef]; field_simp
  have hYδ2 : Y ^ 2 * δ ^ 2 = 1 := by rw [← mul_pow, mul_comm, hδY, one_pow]
  have hle (z : ℝ) (hz : z * δ ≤ 1) : z ≤ Y := by
    rw [hYdef, le_div_iff₀ hδ0]; exact hz
  have hnY : n ≤ Y := hle n hn
  have hRcY : Rc ≤ Y := hle Rc hRc
  have hqY : q ≤ Y := hle q hq
  have hlkY : lk * Real.sqrt Xv ≤ Y := hle _ hlX
  have hY4 : 1 ≤ Y ^ 4 := one_le_pow₀ hY1
  set M := max ((δ ^ 2)⁻¹ * (Rc * q + δ ^ 2)) ((δ ^ 2)⁻¹ * Real.sqrt (lk ^ 2 * q ^ 2 * Xv)) with hM
  have hM1 : 1 ≤ M := by
    refine le_trans ?_ (le_max_left _ _)
    rw [hinv2]
    nlinarith [mul_nonneg hRc0 hq0, sq_nonneg Y]
  have hM2 : M ≤ 2 * Y ^ 4 := by
    apply max_le
    · rw [hinv2]
      have hRq : Rc * q ≤ Y * Y := mul_le_mul hRcY hqY hq0 hY0.le
      nlinarith [sq_nonneg Y]
    · rw [hinv2]
      have hs : Real.sqrt (lk ^ 2 * q ^ 2 * Xv) = lk * q * Real.sqrt Xv := by
        rw [show lk ^ 2 * q ^ 2 * Xv = (lk * q) ^ 2 * Xv by ring, Real.sqrt_mul (sq_nonneg _),
          Real.sqrt_sq (mul_nonneg hlk hq0)]
      rw [hs]
      have h1 : lk * q * Real.sqrt Xv ≤ Y * Y := by
        calc lk * q * Real.sqrt Xv = (lk * Real.sqrt Xv) * q := by ring
          _ ≤ Y * Y := mul_le_mul hlkY hqY hq0 hY0.le
      nlinarith [sq_nonneg Y]
  have hArg : 4 * (n * Cc) * M / (δ / 7) = 28 * n * Cc * M * Y := by
    rw [hYdef]; field_simp; ring
  have hCcY : Cc ≤ Y ^ (5 * d) := by
    have h1 : (1 : ℝ) + 2 * 1 / δ ^ 4 = 1 + 2 * Y ^ 4 := by rw [hYdef]; field_simp
    have h2 : 1 + 2 * Y ^ 4 ≤ Y ^ 5 := by
      have : Y ^ 5 = Y * Y ^ 4 := by ring
      nlinarith
    calc Cc ≤ (1 + 2 * 1 / δ ^ 4) ^ d := hC
      _ = (1 + 2 * Y ^ 4) ^ d := by rw [h1]
      _ ≤ (Y ^ 5) ^ d := pow_le_pow_left₀ (by positivity) h2 d
      _ = Y ^ (5 * d) := by rw [← pow_mul]
  have hn0' : 0 < n := by linarith
  have hC0' : 0 < Cc := by linarith
  have hM0 : 0 < M := by linarith
  have hpos : 0 < 28 * n * Cc * M * Y := by positivity
  rw [hArg]
  constructor
  · apply Real.log_nonneg
    have h1 : 1 ≤ n * Cc := one_le_mul_of_one_le_of_one_le hn0 hC0
    have h2 : 1 ≤ n * Cc * M := one_le_mul_of_one_le_of_one_le h1 hM1
    have h3 : 1 ≤ n * Cc * M * Y := one_le_mul_of_one_le_of_one_le h2 hY1
    nlinarith
  · have hup : 28 * n * Cc * M * Y ≤ Y ^ (12 * d) := by
      calc 28 * n * Cc * M * Y ≤ 28 * Y * Y ^ (5 * d) * (2 * Y ^ 4) * Y := by
            gcongr
        _ = 56 * Y ^ (5 * d + 6) := by ring
        _ ≤ Y * Y ^ (5 * d + 6) := by gcongr
        _ = Y ^ (5 * d + 7) := by ring
        _ ≤ Y ^ (12 * d) := pow_le_pow_right₀ hY1 (by omega)
    calc Real.log (28 * n * Cc * M * Y) ≤ Real.log (Y ^ (12 * d)) := Real.log_le_log hpos hup
      _ = 12 * d * Real.log (1 / δ) := by rw [Real.log_pow]; push_cast; ring

theorem xv_le (d n δ R eps : ℝ) (hd : 1 ≤ d) (hn : 1 ≤ n) (hδ0 : 0 < δ)
    (hcx : 14 + 3 * Real.log (d * n) ≤ Real.log (1 / δ)) (hR0 : 0 ≤ R) (hR : R ≤ 268 * d ^ 2) (heps0 : 0 < eps)
    (heps : 1 / Real.sqrt n ≤ eps) :
    (16 * Real.log (1 / δ)) ^ 2 * (9 * n) +
        n * (Real.sqrt (72 + 25600 * (R ^ 4 + 3 * d ^ 2) / eps ^ 4) *
          Real.sqrt (Real.sqrt 2027025 * Real.exp (-Real.sqrt ((16 * Real.log (1 / δ)) ^ 2) / 4))) ≤
      2305 * n * Real.log (1 / δ) ^ 2 := by
  set x := Real.log (1 / δ) with hxdef
  have hdn : 1 ≤ d * n := one_le_mul_of_one_le_of_one_le hd hn
  have hl0 : 0 ≤ Real.log (d * n) := Real.log_nonneg hdn
  have hx14 : 14 ≤ x := by linarith
  have hsq : Real.sqrt ((16 * x) ^ 2) = 16 * x := Real.sqrt_sq (by linarith)
  rw [hsq, show -(16 * x) / 4 = -(4 * x) by ring]
  set W := 72 + 25600 * (R ^ 4 + 3 * d ^ 2) / eps ^ 4 with hW
  have hW0 : 0 ≤ W := by positivity
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 (by linarith)
  have hepsn : 1 ≤ eps * Real.sqrt n := by
    rw [div_le_iff₀ hsn] at heps; linarith
  have he4 : 1 ≤ eps ^ 4 * n ^ 2 := by
    have h : (eps * Real.sqrt n) ^ 4 = eps ^ 4 * n ^ 2 := by
      rw [mul_pow, show Real.sqrt n ^ 4 = (Real.sqrt n ^ 2) ^ 2 by ring, Real.sq_sqrt (by linarith)]
    rw [← h]; exact one_le_pow₀ hepsn
  have hR4 : R ^ 4 ≤ 268 ^ 4 * d ^ 8 := by
    calc R ^ 4 ≤ (268 * d ^ 2) ^ 4 := pow_le_pow_left₀ hR0 hR 4
      _ = 268 ^ 4 * d ^ 8 := by ring
  have hd2 : d ^ 2 ≤ d ^ 8 := pow_le_pow_right₀ hd (by norm_num)
  have hd8 : 1 ≤ d ^ 8 := one_le_pow₀ hd
  have hn2 : 1 ≤ n ^ 2 := one_le_pow₀ hn
  have hdn82 : 1 ≤ d ^ 8 * n ^ 2 := one_le_mul_of_one_le_of_one_le hd8 hn2
  have hWle : W ≤ 132062386662472 * (d ^ 8 * n ^ 2) := by
    have hA0 : 0 ≤ 25600 * (R ^ 4 + 3 * d ^ 2) := by positivity
    have h1 : 25600 * (R ^ 4 + 3 * d ^ 2) / eps ^ 4 ≤ 25600 * (R ^ 4 + 3 * d ^ 2) * n ^ 2 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    have h2 : R ^ 4 + 3 * d ^ 2 ≤ (268 ^ 4 + 3) * d ^ 8 := by nlinarith
    have h3 : 25600 * (R ^ 4 + 3 * d ^ 2) * n ^ 2 ≤ 25600 * ((268 ^ 4 + 3) * d ^ 8) * n ^ 2 := by
      have hn20 : 0 ≤ n ^ 2 := by positivity
      gcongr
    rw [hW]; nlinarith
  have hpow : d ^ 8 * n ^ 2 ≤ (d * n) ^ 12 := by
    rw [mul_pow]
    exact mul_le_mul (pow_le_pow_right₀ hd (by norm_num)) (pow_le_pow_right₀ hn (by norm_num))
      (by positivity) (by positivity)
  have hexp56 : 1424 * 132062386662472 ≤ Real.exp 56 := by
    have h1 := Real.exp_one_gt_d9
    have h2 : (2.7 : ℝ) ^ 56 ≤ Real.exp 1 ^ 56 := pow_le_pow_left₀ (by norm_num) (by linarith) 56
    rw [Real.exp_one_pow] at h2
    have h3 : (1424 * 132062386662472 : ℝ) ≤ 2.7 ^ 56 := by norm_num
    push_cast at h2
    linarith
  have hexp : Real.exp 56 * (d * n) ^ 12 ≤ Real.exp (4 * x) := by
    have h1 : (d * n) ^ 12 = Real.exp (12 * Real.log (d * n)) := by
      rw [show (12 : ℝ) * Real.log (d * n) = ((12 : ℕ) : ℝ) * Real.log (d * n) by norm_num, ← Real.log_pow,
        Real.exp_log (by positivity)]
    rw [h1, ← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith)
  have hs2 : Real.sqrt 2027025 ≤ 1424 := by
    rw [show (1424 : ℝ) = Real.sqrt (1424 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hin : W * (Real.sqrt 2027025 * Real.exp (-(4 * x))) ≤ 1 := by
    have hE : 0 < Real.exp (-(4 * x)) := Real.exp_pos _
    have h1 : W * 1424 ≤ Real.exp (4 * x) := by
      have hdn12 : 0 ≤ (d * n) ^ 12 := by positivity
      calc W * 1424 ≤ 132062386662472 * (d ^ 8 * n ^ 2) * 1424 := by gcongr
        _ ≤ 132062386662472 * (d * n) ^ 12 * 1424 := by gcongr
        _ = (1424 * 132062386662472) * (d * n) ^ 12 := by ring
        _ ≤ Real.exp 56 * (d * n) ^ 12 := by gcongr
        _ ≤ Real.exp (4 * x) := hexp
    have h2 : Real.exp (4 * x) * Real.exp (-(4 * x)) = 1 := by rw [← Real.exp_add]; simp
    calc W * (Real.sqrt 2027025 * Real.exp (-(4 * x))) ≤ W * (1424 * Real.exp (-(4 * x))) := by gcongr
      _ = (W * 1424) * Real.exp (-(4 * x)) := by ring
      _ ≤ Real.exp (4 * x) * Real.exp (-(4 * x)) := by gcongr
      _ = 1 := h2
  have hP : Real.sqrt W * Real.sqrt (Real.sqrt 2027025 * Real.exp (-(4 * x))) ≤ x ^ 2 := by
    rw [← Real.sqrt_mul hW0]
    calc Real.sqrt (W * (Real.sqrt 2027025 * Real.exp (-(4 * x)))) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hin
      _ = 1 := Real.sqrt_one
      _ ≤ x ^ 2 := by nlinarith
  have hn0 : 0 ≤ n := by linarith
  have := mul_le_mul_of_nonneg_left hP hn0
  nlinarith

theorem vcoef_le (d n x lam k0 eps Le Xv l : ℝ) (hd : 1 ≤ d) (hn : 1 ≤ n)
    (hx : 14 ≤ x) (hLe : Le = 36 * x) (hlam : 0 < lam) (hk0 : 0 ≤ k0) (hk0' : k0 ≤ 21 / 20) (heps : 0 < eps)
    (hXv0 : 0 ≤ Xv) (hXv : Xv ≤ 2305 * n * x ^ 2) (hl0 : 0 ≤ l) (hl : l ≤ 12 * d * x) :
    3 * (lam * k0) * Real.sqrt (Xv * l) ≤ lam * Le ^ 2 * (1 + Real.sqrt (10 * d * n) + d ^ 2 * Le / eps) / 2 := by
  have hx_nonneg : 0 ≤ x := by linarith
  have hd_nonneg : 0 ≤ d := by linarith
  have hn_nonneg : 0 ≤ n := by linarith
  have h_dn_nonneg : 0 ≤ d * n := mul_nonneg hd_nonneg hn_nonneg
  have h_sqrt_dn_nonneg : 0 ≤ Real.sqrt (d * n) := Real.sqrt_nonneg _
  have hx_sq_nonneg : 0 ≤ x ^ 2 := pow_two_nonneg x
  have h_Le_nonneg : 0 ≤ Le := by
    rw [hLe]
    nlinarith
  have h_lam_nonneg : 0 ≤ lam := by linarith
  have h_eps_nonneg : 0 ≤ eps := by linarith
  have h_nonneg_sqrt_Xv_l : 0 ≤ Real.sqrt (Xv * l) := Real.sqrt_nonneg _
  -- Xv * l ≤ 27660 * d * n * x^3
  have hXv_mul_l : Xv * l ≤ 27660 * d * n * x ^ 3 := by
    nlinarith
  -- sqrt(27660) ≤ 167
  have h_sqrt_27660_le_167 : Real.sqrt (27660 : ℝ) ≤ 167 := by
    calc
      Real.sqrt (27660 : ℝ) ≤ Real.sqrt ((167 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = 167 := by norm_num
  -- sqrt(27660 * d * n * x^3) ≤ 167 * x * sqrt(x) * sqrt(d*n)
  have h_sqrt_bound : Real.sqrt (27660 * d * n * x ^ 3) ≤ 167 * x * Real.sqrt x * Real.sqrt (d * n) := by
    have h_expr : 27660 * d * n * x ^ 3 = ((27660 : ℝ) * (d * n)) * (x ^ 2) * x := by ring
    rw [h_expr]
    calc
      Real.sqrt (((27660 : ℝ) * (d * n)) * (x ^ 2) * x) = Real.sqrt (((27660 : ℝ) * (d * n)) * (x ^ 2)) * Real.sqrt x := by
        simpa [mul_assoc] using Real.sqrt_mul (by positivity : 0 ≤ ((27660 : ℝ) * (d * n)) * x ^ 2) x
      _ = (Real.sqrt ((27660 : ℝ) * (d * n)) * Real.sqrt (x ^ 2)) * Real.sqrt x := by
        rw [Real.sqrt_mul (by positivity : 0 ≤ (27660 : ℝ) * (d * n))]
      _ = (Real.sqrt (27660 : ℝ) * Real.sqrt (d * n) * Real.sqrt (x ^ 2)) * Real.sqrt x := by
        rw [Real.sqrt_mul (show 0 ≤ (27660 : ℝ) from by norm_num)]
      _ = (Real.sqrt (27660 : ℝ) * Real.sqrt (d * n) * x) * Real.sqrt x := by
        rw [Real.sqrt_sq hx_nonneg]
      _ = Real.sqrt (27660 : ℝ) * x * Real.sqrt x * Real.sqrt (d * n) := by ring
      _ ≤ 167 * x * Real.sqrt x * Real.sqrt (d * n) := by
        have h_nonneg_factors : 0 ≤ x * Real.sqrt x * Real.sqrt (d * n) := by positivity
        calc
          Real.sqrt (27660 : ℝ) * x * Real.sqrt x * Real.sqrt (d * n) = Real.sqrt (27660 : ℝ) * (x * Real.sqrt x * Real.sqrt (d * n)) := by ring
          _ ≤ 167 * (x * Real.sqrt x * Real.sqrt (d * n)) :=
            mul_le_mul_of_nonneg_right h_sqrt_27660_le_167 h_nonneg_factors
          _ = 167 * x * Real.sqrt x * Real.sqrt (d * n) := by ring
  -- sqrt(Xv * l) ≤ 167 * x * sqrt(x) * sqrt(d*n)
  have h_sqrt_Xv_l : Real.sqrt (Xv * l) ≤ 167 * x * Real.sqrt x * Real.sqrt (d * n) := by
    calc
      Real.sqrt (Xv * l) ≤ Real.sqrt (27660 * d * n * x ^ 3) := Real.sqrt_le_sqrt hXv_mul_l
      _ ≤ 167 * x * Real.sqrt x * Real.sqrt (d * n) := h_sqrt_bound
  -- 3 * lam * k0 ≤ 3 * lam * (21/20)
  have hk0_bound : 3 * (lam * k0) ≤ 3 * lam * (21 / 20) := by
    nlinarith
  -- Left side ≤ 527 * lam * x * sqrt(x) * sqrt(d*n)
  have h_left : 3 * (lam * k0) * Real.sqrt (Xv * l) ≤ 527 * lam * x * Real.sqrt x * Real.sqrt (d * n) := by
    calc
      3 * (lam * k0) * Real.sqrt (Xv * l) ≤ (3 * lam * (21 / 20)) * Real.sqrt (Xv * l) :=
        mul_le_mul_of_nonneg_right hk0_bound h_nonneg_sqrt_Xv_l
      _ ≤ (3 * lam * (21 / 20)) * (167 * x * Real.sqrt x * Real.sqrt (d * n)) := by
        have h_nonneg : 0 ≤ 3 * lam * (21 / 20) := by positivity
        apply mul_le_mul_of_nonneg_left h_sqrt_Xv_l h_nonneg
      _ = (3 * (21 / 20) * 167) * lam * x * Real.sqrt x * Real.sqrt (d * n) := by ring
      _ = (10521 / 20) * lam * x * Real.sqrt x * Real.sqrt (d * n) := by ring
      _ ≤ 527 * lam * x * Real.sqrt x * Real.sqrt (d * n) := by
        have h_coeff : (10521 / 20 : ℝ) ≤ 527 := by norm_num
        have h_nonneg_rest : 0 ≤ lam * x * Real.sqrt x * Real.sqrt (d * n) := by positivity
        nlinarith
  -- Right side ≥ lam * Le^2 * sqrt(10*d*n) / 2
  have h_right_lower : lam * Le ^ 2 * Real.sqrt (10 * d * n) / 2 ≤ lam * Le ^ 2 * (1 + Real.sqrt (10 * d * n) + d ^ 2 * Le / eps) / 2 := by
    have h_nonneg_extra : 0 ≤ lam * Le ^ 2 * (1 + d ^ 2 * Le / eps) / 2 := by
      have : 0 ≤ d ^ 2 * Le / eps := by positivity
      positivity
    nlinarith
  -- Le^2 = 1296 * x^2
  have h_Le_sq : Le ^ 2 = 1296 * x ^ 2 := by
    rw [hLe]
    ring
  -- sqrt(10*d*n) ≥ 3*sqrt(d*n)
  have h_sqrt_10dn_ge_3_sqrt_dn : 3 * Real.sqrt (d * n) ≤ Real.sqrt (10 * d * n) := by
    have h_nonneg_10dn : 0 ≤ 10 * d * n := by positivity
    have h_sq_ineq : (3 * Real.sqrt (d * n)) ^ 2 ≤ (Real.sqrt (10 * d * n)) ^ 2 := by
      have h1 : (3 * Real.sqrt (d * n)) ^ 2 = 9 * (d * n) := by
        rw [mul_pow]
        rw [Real.sq_sqrt h_dn_nonneg]; norm_num
      have h2 : (Real.sqrt (10 * d * n)) ^ 2 = 10 * d * n := Real.sq_sqrt h_nonneg_10dn
      rw [h1, h2]
      nlinarith
    have h_nonneg_sqrt : 0 ≤ Real.sqrt (10 * d * n) := Real.sqrt_nonneg _
    exact le_of_sq_le_sq h_sq_ineq h_nonneg_sqrt
  -- Right side ≥ 1944 * lam * x^2 * sqrt(d*n)
  have h_right : 1944 * lam * x ^ 2 * Real.sqrt (d * n) ≤ lam * Le ^ 2 * (1 + Real.sqrt (10 * d * n) + d ^ 2 * Le / eps) / 2 := by
    calc
      1944 * lam * x ^ 2 * Real.sqrt (d * n) = 648 * lam * x ^ 2 * (3 * Real.sqrt (d * n)) := by ring
      _ ≤ 648 * lam * x ^ 2 * Real.sqrt (10 * d * n) :=
        mul_le_mul_of_nonneg_left h_sqrt_10dn_ge_3_sqrt_dn (by positivity)
      _ = lam * (1296 * x ^ 2) * Real.sqrt (10 * d * n) / 2 := by ring
      _ = lam * Le ^ 2 * Real.sqrt (10 * d * n) / 2 := by rw [h_Le_sq]
      _ ≤ lam * Le ^ 2 * (1 + Real.sqrt (10 * d * n) + d ^ 2 * Le / eps) / 2 := h_right_lower
  -- Final chain: left ≤ 527*lam*x*sqrt(x)*sqrt(dn) ≤ 1944*lam*x^2*sqrt(dn) ≤ right
  have h_mid : 527 * lam * x * Real.sqrt x * Real.sqrt (d * n) ≤ 1944 * lam * x ^ 2 * Real.sqrt (d * n) := by
    have h_sqrt_x_le_x : Real.sqrt x ≤ x := by
      have hx1 : 1 ≤ x := by linarith
      have hx_sq_ge_x : x ≤ x ^ 2 := by nlinarith
      calc
        Real.sqrt x ≤ Real.sqrt (x ^ 2) := Real.sqrt_le_sqrt hx_sq_ge_x
        _ = x := Real.sqrt_sq hx_nonneg
    have h_ineq : 527 * Real.sqrt x ≤ 1944 * x := by
      calc
        527 * Real.sqrt x ≤ 527 * x := mul_le_mul_of_nonneg_left h_sqrt_x_le_x (by norm_num)
        _ ≤ 1944 * x := mul_le_mul_of_nonneg_right (by norm_num) hx_nonneg
    have h_nonneg_lam_sqrt_dn : 0 ≤ lam * Real.sqrt (d * n) := by positivity
    calc
      527 * lam * x * Real.sqrt x * Real.sqrt (d * n) = lam * Real.sqrt (d * n) * (527 * x * Real.sqrt x) := by ring
      _ ≤ lam * Real.sqrt (d * n) * (1944 * x * x) := by
        apply mul_le_mul_of_nonneg_left ?_ h_nonneg_lam_sqrt_dn
        calc
          527 * x * Real.sqrt x = x * (527 * Real.sqrt x) := by ring
          _ ≤ x * (1944 * x) := mul_le_mul_of_nonneg_left h_ineq hx_nonneg
          _ = 1944 * x * x := by ring
      _ = 1944 * lam * x ^ 2 * Real.sqrt (d * n) := by ring
  calc
    3 * (lam * k0) * Real.sqrt (Xv * l) ≤ 527 * lam * x * Real.sqrt x * Real.sqrt (d * n) := h_left
    _ ≤ 1944 * lam * x ^ 2 * Real.sqrt (d * n) := h_mid
    _ ≤ lam * Le ^ 2 * (1 + Real.sqrt (10 * d * n) + d ^ 2 * Le / eps) / 2 := h_right

theorem rcoef_le (d n x lam k0 eps Le sig2 l : ℝ) (hd : 1 ≤ d) (hn : 1 ≤ n)
    (hx : 14 ≤ x) (hLe : Le = 36 * x) (hlam : 0 < lam) (hlam2 : lam ≤ 1 / 2) (hk0 : 0 ≤ k0) (hk0' : k0 ≤ 21 / 20)
    (heps : 0 < eps) (hsig : sig2 = 1 / (8 * Le)) (hl0 : 0 ≤ l) (hl : l ≤ 12 * d * x) :
    2 * (lam * k0 * (Le / (2 * eps)) * (32 / 9 * d * x + 1) +
        lam * (8 / eps) / (1 - lam) * Real.sqrt (2 * d * sig2)) * l ≤
      lam * Le ^ 2 * (1 + Real.sqrt (10 * d * n) + d ^ 2 * Le / eps) / 2 := by
  have hx_pos : 0 < x := by linarith
  have hd_pos : 0 < d := by linarith
  have hLe_pos : 0 < Le := by rw [hLe]; nlinarith
  have h_one_minus_lam_pos : 0 < 1 - lam := by linarith
  have h_one_minus_lam_ge_half : (1/2 : ℝ) ≤ 1 - lam := by linarith
  have h_one_div_le_two : 1 / (1 - lam) ≤ (2 : ℝ) := by
    have h := (one_div_le_one_div h_one_minus_lam_pos (by norm_num : (0 : ℝ) < 1/2)).mpr h_one_minus_lam_ge_half
    have h_eq : (1 : ℝ) / (1/2 : ℝ) = (2 : ℝ) := by norm_num
    rwa [h_eq] at h
  have hx_sq_ge_16 : (16 : ℝ) ≤ x ^ 2 := by nlinarith
  -- bound sqrt(2*d*sig2) ≤ d
  have h_sqrt_bound : Real.sqrt (2 * d * sig2) ≤ d := by
    rw [hsig, hLe]
    have h_expr : 2 * d * (1 / (8 * (36 * x))) = d / (144 * x) := by ring
    rw [h_expr]
    have hpos_144x : 0 < 144 * x := by nlinarith
    have h_le : d / (144 * x) ≤ d := by
      field_simp [hpos_144x.ne.symm]
      nlinarith
    have h_sqrt_d_le_d : Real.sqrt d ≤ d := by
      have hd_nonneg : 0 ≤ d := by linarith
      have hd_sq_ge_d : d ≤ d ^ 2 := by
        nlinarith
      calc
        Real.sqrt d ≤ Real.sqrt (d ^ 2) := Real.sqrt_le_sqrt hd_sq_ge_d
        _ = d := Real.sqrt_sq hd_nonneg
    calc
      Real.sqrt (d / (144 * x)) ≤ Real.sqrt d := Real.sqrt_le_sqrt h_le
      _ ≤ d := h_sqrt_d_le_d
  -- First term bound
  have h_first_term : lam * k0 * (Le / (2 * eps)) * (32 / 9 * d * x + 1) ≤ 70 * lam * d * x ^ 2 / eps := by
    rw [le_div_iff₀ heps]
    rw [hLe]
    -- Goal: (lam * k0 * (36*x / (2*eps)) * (32/9*d*x+1)) * eps ≤ 70 * lam * d * x^2
    -- Simplify LHS: (36*x/(2*eps))*eps = 18*x
    have h_simplify : (lam * k0 * (36*x / (2*eps)) * (32/9*d*x+1)) * eps = lam * k0 * (18*x) * (32/9*d*x+1) := by
      field_simp [heps.ne.symm]
      ring
    rw [h_simplify]
    -- Goal: lam * k0 * (18*x) * (32/9*d*x+1) ≤ 70 * lam * d * x^2
    have hlam_nonneg : 0 ≤ lam := by linarith
    -- Bound k0
    have h1 : lam * k0 * (18 * x) * (32/9 * d * x + 1) ≤ lam * (21/20) * (18 * x) * (32/9 * d * x + 1) := by
      gcongr
    -- Now compute the RHS
    have h2 : lam * (21/20) * (18 * x) * (32/9 * d * x + 1) ≤ 70 * lam * d * x ^ 2 := by
      have h_expanded : lam * (21/20) * (18 * x) * (32/9 * d * x + 1) = lam * (((336 : ℝ)/5) * d * x ^ 2 + ((189 : ℝ)/10) * x) := by ring
      have h_RHS : 70 * lam * d * x ^ 2 = lam * (70 * d * x ^ 2) := by ring
      rw [h_expanded, h_RHS]
      have h_nonneg_lam : 0 ≤ lam := by linarith
      have h_goal : ((336 : ℝ)/5) * d * x ^ 2 + ((189 : ℝ)/10) * x ≤ 70 * d * x ^ 2 := by
        have h_ineq : (189 : ℝ) ≤ 28 * d * x := by nlinarith
        have hx_pos' : 0 < x := by linarith
        have h_mul : (10 : ℝ) * (((336 : ℝ)/5) * d * x ^ 2 + ((189 : ℝ)/10) * x) ≤ (10 : ℝ) * (70 * d * x ^ 2) := by
          ring_nf
          have h_temp : (189 : ℝ) * x ≤ 28 * d * x ^ 2 := by nlinarith
          nlinarith
        nlinarith
      exact mul_le_mul_of_nonneg_left h_goal h_nonneg_lam
    exact le_trans h1 h2
  -- Second term bound
  have h_second_term : lam * (8 / eps) / (1 - lam) * Real.sqrt (2 * d * sig2) ≤ lam * d * x ^ 2 / eps := by
    calc
      lam * (8 / eps) / (1 - lam) * Real.sqrt (2 * d * sig2)
          ≤ lam * (8 / eps) / (1 - lam) * d := by
        gcongr
      _ = lam * (8 / eps) * d * (1 / (1 - lam)) := by ring
      _ ≤ lam * (8 / eps) * d * (2 : ℝ) := by
        gcongr
      _ = 16 * lam * d / eps := by ring
      _ ≤ lam * d * x ^ 2 / eps := by
        field_simp [heps.ne.symm]
        nlinarith
  -- Combine
  have hRc : lam * k0 * (Le / (2 * eps)) * (32 / 9 * d * x + 1) + lam * (8 / eps) / (1 - lam) * Real.sqrt (2 * d * sig2) ≤
      71 * lam * d * x ^ 2 / eps := by
    have h := add_le_add h_first_term h_second_term
    have h_eq : 70 * lam * d * x ^ 2 / eps + lam * d * x ^ 2 / eps = 71 * lam * d * x ^ 2 / eps := by ring
    rw [h_eq] at h
    exact h
  -- Now use l ≤ 12*d*x
  have h_main : 2 * (lam * k0 * (Le / (2 * eps)) * (32 / 9 * d * x + 1) +
      lam * (8 / eps) / (1 - lam) * Real.sqrt (2 * d * sig2)) * l ≤
      2 * (71 * lam * d * x ^ 2 / eps) * (12 * d * x) := by
    have h_nonneg_l : 0 ≤ l := hl0
    have h_nonneg_2B : 0 ≤ 2 * (71 * lam * d * x ^ 2 / eps) := by positivity
    have h_2A_le_2B : 2 * (lam * k0 * (Le / (2 * eps)) * (32 / 9 * d * x + 1) +
        lam * (8 / eps) / (1 - lam) * Real.sqrt (2 * d * sig2)) ≤
        2 * (71 * lam * d * x ^ 2 / eps) := by nlinarith
    have h1 : 2 * (lam * k0 * (Le / (2 * eps)) * (32 / 9 * d * x + 1) +
        lam * (8 / eps) / (1 - lam) * Real.sqrt (2 * d * sig2)) * l ≤
        2 * (71 * lam * d * x ^ 2 / eps) * l :=
      mul_le_mul_of_nonneg_right h_2A_le_2B h_nonneg_l
    have h2 : 2 * (71 * lam * d * x ^ 2 / eps) * l ≤
        2 * (71 * lam * d * x ^ 2 / eps) * (12 * d * x) :=
      mul_le_mul_of_nonneg_left hl h_nonneg_2B
    exact le_trans h1 h2
  have h_simplify : 2 * (71 * lam * d * x ^ 2 / eps) * (12 * d * x) = 1704 * lam * d ^ 2 * x ^ 3 / eps := by ring
  rw [h_simplify] at h_main
  -- Lower bound for RHS
  have h_RHS_lower : 23328 * lam * d ^ 2 * x ^ 3 / eps ≤ lam * Le ^ 2 * (1 + Real.sqrt (10 * d * n) + d ^ 2 * Le / eps) / 2 := by
    rw [hLe]
    have h_nonneg_sqrt : 0 ≤ Real.sqrt (10 * d * n) := Real.sqrt_nonneg _
    have h_sum_ge : d ^ 2 * (36 * x) / eps ≤ 1 + Real.sqrt (10 * d * n) + d ^ 2 * (36 * x) / eps := by
      nlinarith
    have h_nonneg_factor : 0 ≤ lam * ((36 * x) ^ 2) / 2 := by positivity
    calc
      23328 * lam * d ^ 2 * x ^ 3 / eps
          = lam * ((36 * x) ^ 2) / 2 * (d ^ 2 * (36 * x) / eps) := by ring
      _ ≤ lam * ((36 * x) ^ 2) / 2 * (1 + Real.sqrt (10 * d * n) + d ^ 2 * (36 * x) / eps) := by
        gcongr
      _ = lam * ((36 * x) ^ 2) * (1 + Real.sqrt (10 * d * n) + d ^ 2 * (36 * x) / eps) / 2 := by ring
  have h_1704_le_23328 : (1704 : ℝ) ≤ 23328 := by norm_num
  calc
    2 * (lam * k0 * (Le / (2 * eps)) * (32 / 9 * d * x + 1) +
        lam * (8 / eps) / (1 - lam) * Real.sqrt (2 * d * sig2)) * l
        ≤ 1704 * lam * d ^ 2 * x ^ 3 / eps := h_main
    _ ≤ 23328 * lam * d ^ 2 * x ^ 3 / eps := by
      gcongr
    _ ≤ lam * Le ^ 2 * (1 + Real.sqrt (10 * d * n) + d ^ 2 * Le / eps) / 2 := h_RHS_lower

theorem small_R1 (d x lam k0 eps Le : ℝ) (hd : 1 ≤ d) (hx : 14 ≤ x) (hLe : Le = 36 * x) (hlam : 0 < lam)
    (hk0 : 0 ≤ k0) (hk0' : k0 ≤ 21 / 20) (heps : 0 < eps) :
    lam * k0 * (Le / (2 * eps)) * (32 / 9 * d * x + 1) ≤ lam * Le ^ 2 * (d ^ 2 * Le / eps) / 2 := by
  have hLe0 : 0 < Le := by rw [hLe]; linarith
  have hdx : 1 ≤ d * x := by nlinarith
  have h1 : k0 * (32 / 9 * d * x + 1) ≤ Le ^ 2 * d ^ 2 := by
    have h2 : k0 * (32 / 9 * d * x + 1) ≤ 21 / 20 * (41 / 9 * (d * x)) := by nlinarith
    have h3 : Le ^ 2 * d ^ 2 = 1296 * x * (d * (d * x)) := by rw [hLe]; ring
    have h4 : d * x ≤ d * (d * x) := le_mul_of_one_le_left (by linarith) hd
    have h5 : 41 / 9 * (d * x) ≤ 1296 * x * (d * (d * x)) := by nlinarith
    nlinarith
  have hE : lam * k0 * (Le / (2 * eps)) * (32 / 9 * d * x + 1) =
      (lam * Le / (2 * eps)) * (k0 * (32 / 9 * d * x + 1)) := by ring
  have hF : lam * Le ^ 2 * (d ^ 2 * Le / eps) / 2 = (lam * Le / (2 * eps)) * (Le ^ 2 * d ^ 2) := by
    field_simp
  rw [hE, hF]
  exact mul_le_mul_of_nonneg_left h1 (by positivity)

theorem small_R2 (d x lam eps Le sig2 : ℝ) (hd : 1 ≤ d) (hx : 14 ≤ x) (hLe : Le = 36 * x) (hlam : 0 < lam)
    (hlam2 : lam ≤ 1 / 2) (heps : 0 < eps) (hsig : sig2 = 1 / (8 * Le)) :
    lam * (8 / eps) / (1 - lam) * Real.sqrt (2 * d * sig2) ≤ lam * Le ^ 2 * (d ^ 2 * Le / eps) / 2 := by
  have hLe0 : 0 < Le := by rw [hLe]; linarith
  have hlam1 : 0 < 1 - lam := by linarith
  have hinv : 1 / (1 - lam) ≤ 2 := by rw [div_le_iff₀ hlam1]; linarith
  have hsq : Real.sqrt (2 * d * sig2) ≤ d := by
    have h1 : 2 * d * sig2 ≤ d ^ 2 := by
      rw [hsig]
      have h2 : 2 * d * (1 / (8 * Le)) = d / (4 * Le) := by field_simp; ring
      rw [h2, div_le_iff₀ (by positivity)]
      have h3 : d ≤ d ^ 2 := by rw [sq]; exact le_mul_of_one_le_left (by linarith) hd
      have h4 : d ^ 2 ≤ d ^ 2 * (4 * Le) := le_mul_of_one_le_right (by positivity) (by linarith)
      linarith
    calc Real.sqrt (2 * d * sig2) ≤ Real.sqrt (d ^ 2) := Real.sqrt_le_sqrt h1
      _ = d := Real.sqrt_sq (by linarith)
  have hs0 : 0 ≤ Real.sqrt (2 * d * sig2) := Real.sqrt_nonneg _
  have h2 : 8 * (1 / (1 - lam) * Real.sqrt (2 * d * sig2)) ≤ 16 * d := by
    have h5 : 1 / (1 - lam) * Real.sqrt (2 * d * sig2) ≤ 2 * d := mul_le_mul hinv hsq hs0 (by norm_num)
    linarith
  have h3 : 16 * d ≤ Le ^ 3 * d ^ 2 / 2 := by
    have hL3 : 504 ≤ Le := by rw [hLe]; linarith
    have hL3' : (504 : ℝ) ^ 3 ≤ Le ^ 3 := pow_le_pow_left₀ (by norm_num) hL3 3
    have hdd : d ≤ d ^ 2 := by rw [sq]; exact le_mul_of_one_le_left (by linarith) hd
    have h6 : 504 ^ 3 * d ≤ Le ^ 3 * d ^ 2 := mul_le_mul hL3' hdd (by linarith) (by positivity)
    linarith only [h6, hd]
  have hE : lam * (8 / eps) / (1 - lam) * Real.sqrt (2 * d * sig2) =
      (lam / eps) * (8 * (1 / (1 - lam) * Real.sqrt (2 * d * sig2))) := by
    field_simp
  have hF : lam * Le ^ 2 * (d ^ 2 * Le / eps) / 2 = (lam / eps) * (Le ^ 3 * d ^ 2 / 2) := by
    field_simp
  rw [hE, hF]
  exact mul_le_mul_of_nonneg_left (h2.trans h3) (by positivity)

theorem small_le (d n x δ lam k0 eps Le sig2 l : ℝ) (hd : 1 ≤ d) (hn : 1 ≤ n)
    (hx : 14 ≤ x) (hLe : Le = 36 * x) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 2) (hlam : 0 < lam) (hlam2 : lam ≤ 1 / 2)
    (hk0 : 0 ≤ k0) (hk0' : k0 ≤ 21 / 20) (heps : 0 < eps) (hsig : sig2 = 1 / (8 * Le))
    (hc2dl : 2 * δ * d * n / lam ≤ 1) (hnδ : n * δ ≤ 1) (hl0 : 0 ≤ l) (hl : l ≤ 12 * d * x) :
    lam * Le ^ 2 * (1 + Real.sqrt (10 * d * n) + d ^ 2 * Le / eps) * (2 * δ ^ 3) + 2 * δ ^ 2 * l +
        2 * n * (lam * k0 * (Le / (2 * eps)) * (32 / 9 * d * x + 1) +
          lam * (8 / eps) / (1 - lam) * Real.sqrt (2 * d * sig2)) * δ ^ 3 ≤
      4 * δ * (lam * Le ^ 2 * (1 + Real.sqrt (10 * d * n) + d ^ 2 * Le / eps)) := by
  have hR1 := small_R1 d x lam k0 eps Le hd hx hLe hlam hk0 hk0' heps
  have hR2 := small_R2 d x lam eps Le sig2 hd hx hLe hlam hlam2 heps hsig
  have hLe0 : 0 < Le := by rw [hLe]; linarith
  have hs0 : 0 ≤ Real.sqrt (10 * d * n) := Real.sqrt_nonneg _
  have hq0 : 0 ≤ d ^ 2 * Le / eps := by positivity
  have hL2 : 0 ≤ lam * Le ^ 2 := by positivity
  have hRc0 : 0 ≤ lam * k0 * (Le / (2 * eps)) * (32 / 9 * d * x + 1) +
      lam * (8 / eps) / (1 - lam) * Real.sqrt (2 * d * sig2) := by
    have : 0 < 1 - lam := by linarith
    positivity
  generalize hB : lam * Le ^ 2 * (1 + Real.sqrt (10 * d * n) + d ^ 2 * Le / eps) = B
  generalize hRc : lam * k0 * (Le / (2 * eps)) * (32 / 9 * d * x + 1) +
      lam * (8 / eps) / (1 - lam) * Real.sqrt (2 * d * sig2) = Rc at hRc0
  have hB1 : lam * Le ^ 2 ≤ B := by
    rw [← hB]
    have := mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ 1 + Real.sqrt (10 * d * n) + d ^ 2 * Le / eps by linarith) hL2
    linarith
  have hRcB : Rc ≤ B := by
    rw [← hRc, ← hB]
    have := mul_le_mul_of_nonneg_left
      (show d ^ 2 * Le / eps ≤ 1 + Real.sqrt (10 * d * n) + d ^ 2 * Le / eps by linarith) hL2
    linarith
  have hB0 : 0 ≤ B := le_trans hL2 hB1
  have hδ2 : δ ^ 2 ≤ 1 / 4 := by
    calc δ ^ 2 = δ * δ := sq δ
      _ ≤ (1 / 2) * (1 / 2) := mul_le_mul hδ1 hδ1 hδ0.le (by norm_num)
      _ = 1 / 4 := by norm_num
  have hT1 : B * (2 * δ ^ 3) ≤ δ * B := by
    have h1 : 2 * δ ^ 3 ≤ δ := by
      calc 2 * δ ^ 3 = δ * (2 * δ ^ 2) := by ring
        _ ≤ δ * 1 := mul_le_mul_of_nonneg_left (by linarith) hδ0.le
        _ = δ := mul_one δ
    calc B * (2 * δ ^ 3) ≤ B * δ := mul_le_mul_of_nonneg_left h1 hB0
      _ = δ * B := mul_comm B δ
  have hT2 : 2 * δ ^ 2 * l ≤ 2 * (δ * B) := by
    have hdn : 2 * δ * d * n ≤ lam := by rwa [div_le_one hlam] at hc2dl
    have hδd : 2 * δ * d ≤ lam := by
      have : 2 * δ * d ≤ 2 * δ * d * n := le_mul_of_one_le_right (by positivity) hn
      linarith
    have h2 : δ * l ≤ δ * (12 * d * x) := mul_le_mul_of_nonneg_left hl hδ0.le
    have h3 : δ * (12 * d * x) ≤ 6 * lam * x := by
      calc δ * (12 * d * x) = 6 * x * (2 * δ * d) := by ring
        _ ≤ 6 * x * lam := mul_le_mul_of_nonneg_left hδd (by linarith)
        _ = 6 * lam * x := by ring
    have h4 : 6 * lam * x ≤ lam * Le ^ 2 := by
      have h5 : 0 ≤ lam * x * (1296 * x - 6) := mul_nonneg (mul_nonneg hlam.le (by linarith)) (by linarith)
      rw [hLe]; nlinarith [h5]
    have h1 : δ * l ≤ B := by linarith
    calc 2 * δ ^ 2 * l = 2 * δ * (δ * l) := by ring
      _ ≤ 2 * δ * B := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 2 * (δ * B) := by ring
  have hT3 : 2 * n * Rc * δ ^ 3 ≤ δ * B := by
    have h1 : 2 * n * Rc * δ ^ 3 = 2 * (n * δ) * (Rc * δ ^ 2) := by ring
    have h2 : 2 * (n * δ) * (Rc * δ ^ 2) ≤ 2 * (Rc * δ ^ 2) := by
      have h5 : 0 ≤ Rc * δ ^ 2 := by positivity
      have := mul_le_mul_of_nonneg_right (show 2 * (n * δ) ≤ 2 by linarith) h5
      linarith
    have h3 : 2 * (Rc * δ ^ 2) ≤ Rc * δ := by
      calc 2 * (Rc * δ ^ 2) = (Rc * δ) * (2 * δ) := by ring
        _ ≤ (Rc * δ) * 1 := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        _ = Rc * δ := mul_one _
    have h4 : Rc * δ ≤ B * δ := mul_le_mul_of_nonneg_right hRcB hδ0.le
    linarith
  linarith

theorem rc_le_inv (d n x δ lam k0 eps Le sig2 : ℝ) (hd : 1 ≤ d) (hn : 1 ≤ n)
    (hx : 14 ≤ x) (hLe : Le = 36 * x) (hδ0 : 0 < δ) (hlam : 0 < lam) (hlam2 : lam ≤ 1 / 2)
    (hr11 : lam ≤ 1 / (d * Le ^ 2)) (hk0 : 0 ≤ k0) (hk0' : k0 ≤ 21 / 20) (heps : 0 < eps)
    (heps' : 1 / Real.sqrt n ≤ eps) (hsig : sig2 = 1 / (8 * Le)) (hnδ : n * δ ≤ 1) :
    (lam * k0 * (Le / (2 * eps)) * (32 / 9 * d * x + 1) + lam * (8 / eps) / (1 - lam) * Real.sqrt (2 * d * sig2)) *
      δ ≤ 1 := by
  have hxpos : 0 < x := by linarith
  have hdpos : 0 < d := by linarith
  have hepspos : 0 < eps := heps
  have hlam_nonneg : 0 ≤ lam := by linarith
  have hd_nonneg : 0 ≤ d := by linarith
  have hx_nonneg : 0 ≤ x := by linarith
  have h_sqrt_n_pos : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by linarith)
  -- First term bound: lam * k0 * (Le/(2*eps)) * (32/9*d*x + 1) ≤ 70 * lam * d * x^2 / eps
  have h_first : lam * k0 * (Le / (2 * eps)) * (32 / 9 * d * x + 1) ≤ 70 * lam * d * x ^ 2 / eps := by
    rw [hLe]
    apply (le_div_iff₀ hepspos).mpr
    field_simp [hepspos.ne']
    ring_nf
    -- Goal: k0 * 36 * (x * 32 * d + 9) ≤ x * 2 * 9 * d * 70
    -- i.e., 36*k0*(32*x*d + 9) ≤ 1260*x*d
    -- Using k0 ≤ 21/20, x ≥ 14, d ≥ 1
    have h_bound : k0 * 36 * (x * 32 * d + 9) ≤ (21/20) * 36 * (x * 32 * d + 9) := by
      have h_nonneg : 0 ≤ 36 * (x * 32 * d + 9) := by positivity
      nlinarith
    have h_simp : (21/20) * 36 * (x * 32 * d + 9) ≤ x * 2 * 9 * d * 70 := by
      have hx_d_ge_14 : x * d ≥ 14 := by nlinarith
      nlinarith
    nlinarith
  -- Second term bound: lam * (8/eps) / (1-lam) * sqrt(2*d*sig2) ≤ lam * d * x^2 / eps
  have h_second : lam * (8 / eps) / (1 - lam) * Real.sqrt (2 * d * sig2) ≤ lam * d * x ^ 2 / eps := by
    rw [hsig, hLe]
    -- Simplify the expression inside sqrt: 2*d*(1/(8*(36*x))) = d/(144*x)
    have h_inner : 2 * d * (1 / (8 * (36 * x))) = d / (144 * x) := by ring
    have h_sqrt_term : Real.sqrt (d / (144 * x)) ≤ d := by
      have h_div_le : d / (144 * x) ≤ d := by
        calc
          d / (144 * x) ≤ d / 1 :=
            div_le_div_of_nonneg_left hd_nonneg (by norm_num : 0 < (1 : ℝ)) (by nlinarith : (1 : ℝ) ≤ 144 * x)
          _ = d := by simp
      calc
        Real.sqrt (d / (144 * x)) ≤ Real.sqrt d := Real.sqrt_le_sqrt h_div_le
        _ ≤ d := by
          calc
            Real.sqrt d ≤ Real.sqrt (d ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
            _ = d := Real.sqrt_sq hd_nonneg
    -- Bound the denominator: 1/(1-lam) ≤ 2 since 1-lam ≥ 1/2
    have h_denom : 1 / (1 - lam) ≤ 2 := by
      have h_half_pos : 0 < (1 : ℝ) / 2 := by norm_num
      have h_half_le : (1 : ℝ) / 2 ≤ 1 - lam := by linarith
      have h := one_div_le_one_div_of_le h_half_pos h_half_le
      simpa [div_div] using h
    -- Now chain the inequalities
    have h_mid : lam * (8 / eps) / (1 - lam) * Real.sqrt (d / (144 * x))
        ≤ lam * (8 / eps) * 2 * d := by
      have h_nonneg_sqrt : 0 ≤ Real.sqrt (d / (144 * x)) := Real.sqrt_nonneg _
      have h_nonneg_lam8eps : 0 ≤ lam * (8 / eps) := by positivity
      have h_temp : (lam * (8 / eps)) * (1 / (1 - lam)) ≤ (lam * (8 / eps)) * 2 :=
        mul_le_mul_of_nonneg_left h_denom h_nonneg_lam8eps
      calc
        lam * (8 / eps) / (1 - lam) * Real.sqrt (d / (144 * x))
            = (lam * (8 / eps)) * (1 / (1 - lam)) * Real.sqrt (d / (144 * x)) := by ring
        _ ≤ (lam * (8 / eps)) * 2 * Real.sqrt (d / (144 * x)) :=
          mul_le_mul_of_nonneg_right h_temp h_nonneg_sqrt
        _ ≤ (lam * (8 / eps)) * 2 * d :=
          mul_le_mul_of_nonneg_left h_sqrt_term (by positivity)
        _ = lam * (8 / eps) * 2 * d := by ring
    calc
      lam * (8 / eps) / (1 - lam) * Real.sqrt (2 * d * (1 / (8 * (36 * x))))
          = lam * (8 / eps) / (1 - lam) * Real.sqrt (d / (144 * x)) := by rw [h_inner]
      _ ≤ lam * (8 / eps) * 2 * d := h_mid
      _ = 16 * lam * d / eps := by ring
      _ ≤ lam * d * x ^ 2 / eps := by
        have h_nonneg_lam_d : 0 ≤ lam * d := mul_nonneg hlam_nonneg hd_nonneg
        have h_sq_ge_16 : (16 : ℝ) ≤ x ^ 2 := by nlinarith
        apply div_le_div_of_nonneg_right ?_ (by positivity)
        nlinarith
  -- Sum bound: h_first + h_second ≤ 71 * lam * d * x^2 / eps
  have h_sum : (lam * k0 * (Le / (2 * eps)) * (32 / 9 * d * x + 1) + lam * (8 / eps) / (1 - lam) * Real.sqrt (2 * d * sig2)) ≤ 71 * lam * d * x ^ 2 / eps := by
    have h_add := add_le_add h_first h_second
    have h_simp : 70 * lam * d * x ^ 2 / eps + lam * d * x ^ 2 / eps = 71 * lam * d * x ^ 2 / eps := by ring
    rw [h_simp] at h_add
    exact h_add
  -- Bound using lam ≤ 1/(d*Le^2)
  have h_Le_sq : Le ^ 2 = 1296 * x ^ 2 := by
    rw [hLe]
    ring
  have h_lam_bound' : lam ≤ 1 / (1296 * d * x ^ 2) := by
    rw [h_Le_sq] at hr11
    have h_eq : 1 / (d * (1296 * x ^ 2)) = 1 / (1296 * d * x ^ 2) := by ring
    rw [h_eq] at hr11
    exact hr11
  have h_Rc_bound : 71 * lam * d * x ^ 2 / eps ≤ 71 / (1296 * eps) := by
    have h_num : 71 * lam * d * x ^ 2 ≤ 71 / 1296 := by
      have hdx2_pos : 0 < d * x ^ 2 := by positivity
      have h_mul := mul_le_mul_of_nonneg_right h_lam_bound' (by positivity : 0 ≤ 71 * d * x ^ 2)
      have h_lhs : lam * (71 * d * x ^ 2) = 71 * lam * d * x ^ 2 := by ring
      have h_rhs : (1 / (1296 * d * x ^ 2)) * (71 * d * x ^ 2) = 71 / 1296 := by
        field_simp [hdx2_pos.ne']
      rw [h_lhs, h_rhs] at h_mul
      exact h_mul
    calc
      71 * lam * d * x ^ 2 / eps ≤ (71 / 1296) / eps :=
        div_le_div_of_nonneg_right h_num (by positivity)
      _ = 71 / (1296 * eps) := by ring
  have h_71_1296 : (71 : ℝ) / 1296 ≤ 1 := by norm_num
  have h_Rc_bound2 : 71 / (1296 * eps) ≤ 1 / eps := by
    calc
      71 / (1296 * eps) = (71 / 1296) * (1 / eps) := by ring
      _ ≤ 1 * (1 / eps) := mul_le_mul_of_nonneg_right h_71_1296 (by positivity)
      _ = 1 / eps := by simp
  -- From heps': 1/√n ≤ eps, so 1/eps ≤ √n
  have h_inv_eps_le_sqrt_n : 1 / eps ≤ Real.sqrt n := by
    have h_mul : 1 ≤ eps * Real.sqrt n := by
      calc
        1 = (1 / Real.sqrt n) * Real.sqrt n := by field_simp [h_sqrt_n_pos.ne']
        _ ≤ eps * Real.sqrt n := by
          apply mul_le_mul_of_nonneg_right heps' (by positivity)
    calc
      1 / eps ≤ (eps * Real.sqrt n) / eps :=
        div_le_div_of_nonneg_right h_mul (by positivity)
      _ = Real.sqrt n := by field_simp [hepspos.ne']
  -- √n ≤ n since n ≥ 1
  have h_sqrt_n_le_n : Real.sqrt n ≤ n := by
    calc
      Real.sqrt n ≤ Real.sqrt (n ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
      _ = n := Real.sqrt_sq (by linarith)
  -- Combine: bracket ≤ n
  have h_Rc_le_n : (lam * k0 * (Le / (2 * eps)) * (32 / 9 * d * x + 1) + lam * (8 / eps) / (1 - lam) * Real.sqrt (2 * d * sig2)) ≤ n := by
    linarith
  -- Final result
  calc
    (lam * k0 * (Le / (2 * eps)) * (32 / 9 * d * x + 1) + lam * (8 / eps) / (1 - lam) * Real.sqrt (2 * d * sig2)) * δ
        ≤ n * δ := by
      apply mul_le_mul_of_nonneg_right h_Rc_le_n
      linarith
    _ ≤ 1 := hnδ

theorem lkxv_le_inv (d n x δ lam k0 Le Xv : ℝ) (hd : 1 ≤ d) (hn : 1 ≤ n)
    (hx : 14 ≤ x) (hLe : Le = 36 * x) (hδ0 : 0 < δ) (hlam : 0 < lam) (hr11 : lam ≤ 1 / (d * Le ^ 2))
    (hk0 : 0 ≤ k0) (hk0' : k0 ≤ 21 / 20) (hXv0 : 0 ≤ Xv) (hXv : Xv ≤ 2305 * n * x ^ 2) (hnδ : n * δ ≤ 1) :
    lam * k0 * Real.sqrt Xv * δ ≤ 1 := by
  have hx_nonneg : 0 ≤ x := by linarith
  have hn_nonneg : 0 ≤ n := by linarith
  have hx_pos : 0 < x := by linarith
  have hn_pos : 0 < n := by linarith
  have hlam_nonneg : 0 ≤ lam := by linarith
  have hδ_nonneg : 0 ≤ δ := by linarith
  have hx_ge_one : 1 ≤ x := by linarith
  -- sqrt Xv ≤ 49 * n * x
  have h_sqrt_Xv : Real.sqrt Xv ≤ 49 * n * x := by
    calc
      Real.sqrt Xv ≤ Real.sqrt (2305 * n * x ^ 2) := Real.sqrt_le_sqrt hXv
      _ = Real.sqrt ((2305 * n) * x ^ 2) := by ring
      _ = Real.sqrt (2305 * n) * Real.sqrt (x ^ 2) := by
        rw [Real.sqrt_mul (by nlinarith : 0 ≤ 2305 * n)]
      _ = (Real.sqrt 2305 * Real.sqrt n) * Real.sqrt (x ^ 2) := by
        rw [Real.sqrt_mul (by norm_num : 0 ≤ (2305 : ℝ))]
      _ = Real.sqrt 2305 * Real.sqrt n * Real.sqrt (x ^ 2) := by ring
      _ = Real.sqrt 2305 * Real.sqrt n * |x| := by rw [Real.sqrt_sq_eq_abs]
      _ = Real.sqrt 2305 * Real.sqrt n * x := by rw [abs_of_nonneg hx_nonneg]
      _ ≤ 49 * Real.sqrt n * x := by
        have h_sqrt_2305 : Real.sqrt 2305 ≤ 49 := by
          calc
            Real.sqrt 2305 ≤ Real.sqrt (49 ^ 2) := Real.sqrt_le_sqrt (by norm_num)
            _ = 49 := by norm_num
        have h_nonneg_prod : 0 ≤ Real.sqrt n * x := mul_nonneg (Real.sqrt_nonneg _) hx_nonneg
        nlinarith
      _ ≤ 49 * n * x := by
        have h_sqrt_n_le_n : Real.sqrt n ≤ n := by
          have hn_sq : n ≤ n ^ 2 := by
            nlinarith
          calc
            Real.sqrt n ≤ Real.sqrt (n ^ 2) := Real.sqrt_le_sqrt hn_sq
            _ = n := Real.sqrt_sq hn_nonneg
        nlinarith
  -- lam ≤ 1/(1296*x^2)
  have h_lam_bound : lam ≤ 1 / (1296 * x ^ 2) := by
    have hLe_sq : Le ^ 2 = 1296 * x ^ 2 := by
      rw [hLe]
      ring
    have h_denom : d * Le ^ 2 ≥ 1296 * x ^ 2 := by
      rw [hLe_sq]
      nlinarith
    have hpos : 0 < 1296 * x ^ 2 := by nlinarith
    calc
      lam ≤ 1 / (d * Le ^ 2) := hr11
      _ ≤ 1 / (1296 * x ^ 2) := (one_div_le_one_div (by nlinarith) hpos).mpr h_denom
  -- main inequality: lam * k0 * sqrt Xv ≤ n
  have h_main : lam * k0 * Real.sqrt Xv ≤ n := by
    have h_prod : lam * k0 * Real.sqrt Xv ≤ (1 / (1296 * x ^ 2)) * (21/20 : ℝ) * (49 * n * x) := by
      have h_first_two : lam * k0 ≤ (1 / (1296 * x ^ 2)) * (21/20 : ℝ) :=
        mul_le_mul h_lam_bound hk0' hk0 (by positivity)
      have h_nonneg_sqrt : 0 ≤ Real.sqrt Xv := Real.sqrt_nonneg _
      exact mul_le_mul h_first_two h_sqrt_Xv h_nonneg_sqrt (by positivity)
    have h_bound : (1 / (1296 * x ^ 2)) * (21/20 : ℝ) * (49 * n * x) ≤ n := by
      calc
        (1 / (1296 * x ^ 2)) * (21/20 : ℝ) * (49 * n * x) = ((21 * 49 : ℝ) / (20 * 1296)) * (n / x) := by
          field_simp [hx_pos.ne.symm]
        _ ≤ 1 * (n / x) := by
          have hcoeff : (21 * 49 : ℝ) / (20 * 1296) ≤ 1 := by norm_num
          have h_nx_nonneg : 0 ≤ n / x := div_nonneg hn_nonneg hx_nonneg
          nlinarith
        _ = n / x := by ring
        _ ≤ n := div_le_self hn_nonneg hx_ge_one
    nlinarith
  calc
    lam * k0 * Real.sqrt Xv * δ ≤ n * δ := by
      nlinarith
    _ ≤ 1 := hnδ

theorem sdf_final (Bn Rc Xv lk q qu Au Ac l δ Dq DA : ℝ) (hBn : 0 ≤ Bn)
    (hlk : 0 ≤ lk) (hq : 0 ≤ q) (hXv : 0 ≤ Xv) (hl : 0 ≤ l) (hAu : 2 * Bn * qu < |Au|) (hA : |Au - Ac| ≤ DA)
    (hqq : |qu - q| ≤ Dq) (hqu : 4 * δ ≤ qu) (hV : 3 * lk * Real.sqrt (Xv * l) ≤ Bn / 2)
    (hR : 2 * Rc * l ≤ Bn / 2) (hsmall : Bn * Dq + 2 * δ ^ 2 * l + DA ≤ 4 * δ * Bn) :
    3 * Real.sqrt (lk ^ 2 * q ^ 2 * Xv * l) + 2 * (Rc * q + δ ^ 2) * l < |Ac| := by
  have hsqrt : Real.sqrt (lk ^ 2 * q ^ 2 * Xv * l) = lk * q * Real.sqrt (Xv * l) := by
    calc
      Real.sqrt (lk ^ 2 * q ^ 2 * Xv * l) = Real.sqrt ((lk * q) ^ 2 * (Xv * l)) := by congr 1; ring
      _ = Real.sqrt ((lk * q) ^ 2) * Real.sqrt (Xv * l) := by
        rw [Real.sqrt_mul (sq_nonneg (lk * q))]
      _ = (lk * q) * Real.sqrt (Xv * l) := by
        rw [Real.sqrt_sq (mul_nonneg hlk hq)]
      _ = lk * q * Real.sqrt (Xv * l) := by ring
  have h_sqrt_bound : 3 * Real.sqrt (lk ^ 2 * q ^ 2 * Xv * l) ≤ q * (Bn / 2) := by
    calc
      3 * Real.sqrt (lk ^ 2 * q ^ 2 * Xv * l) = 3 * (lk * q * Real.sqrt (Xv * l)) := by rw [hsqrt]
      _ = q * (3 * lk * Real.sqrt (Xv * l)) := by ring
      _ ≤ q * (Bn / 2) := by
        nlinarith
  have h_lin_bound : 2 * (Rc * q + δ ^ 2) * l ≤ q * (Bn / 2) + 2 * δ ^ 2 * l := by
    nlinarith
  have h_total : 3 * Real.sqrt (lk ^ 2 * q ^ 2 * Xv * l) + 2 * (Rc * q + δ ^ 2) * l ≤ Bn * q + 2 * δ ^ 2 * l := by
    nlinarith
  have h_q_bound : q ≤ qu + Dq := by
    have : q - qu ≤ Dq := by
      calc
        q - qu ≤ |q - qu| := le_abs_self _
        _ = |qu - q| := by rw [abs_sub_comm]
        _ ≤ Dq := hqq
    linarith
  have h_total2 : 3 * Real.sqrt (lk ^ 2 * q ^ 2 * Xv * l) + 2 * (Rc * q + δ ^ 2) * l ≤ Bn * qu + Bn * Dq + 2 * δ ^ 2 * l := by
    nlinarith
  have h_total3 : 3 * Real.sqrt (lk ^ 2 * q ^ 2 * Xv * l) + 2 * (Rc * q + δ ^ 2) * l < |Ac| := by
    have h_abs : |Au| - DA ≤ |Ac| := by
      have h := abs_sub_abs_le_abs_sub Au Ac
      have h' : |Au| - |Ac| ≤ DA := by linarith
      linarith
    nlinarith
  exact h_total3

/-! ## Matrices -/

theorem quad_growth {d : ℕ} (P A : Matrix (Fin d) (Fin d) ℝ) (M a : ℝ) (hM : 0 ≤ M)
    (hA : ∀ w, (A *ᵥ w) ⬝ᵥ (A *ᵥ w) ≤ M * (w ⬝ᵥ w)) (hP : ∀ w, (P *ᵥ w) ⬝ᵥ (P *ᵥ w) ≤ M * (w ⬝ᵥ w))
    (v z : Fin d → ℝ) :
    |a * (((P *ᵥ (A *ᵥ z)) ⬝ᵥ v) ^ 2 - v ⬝ᵥ (P *ᵥ v))| ≤ |a| * (v ⬝ᵥ v) * (M ^ 2 * d + Real.sqrt M) * (1 + ‖z‖) ^ 2 := by
  have h_dot_nonneg : ∀ (x : Fin d → ℝ), 0 ≤ x ⬝ᵥ x := by
    intro x
    have hsum : x ⬝ᵥ x = ∑ i : Fin d, x i * x i := rfl
    rw [hsum]
    refine Finset.sum_nonneg (fun i _ => ?_)
    have : 0 ≤ x i * x i := by
      nlinarith [sq_nonneg (x i)]
    exact this
  have h_sq_nonneg : ∀ (x : ℝ), 0 ≤ x ^ 2 := by
    intro x; nlinarith [sq_nonneg x]
  set w := P *ᵥ (A *ᵥ z) with hw
  set X := (w ⬝ᵥ v) ^ 2 with hX
  set Y := v ⬝ᵥ (P *ᵥ v) with hY
  have hX_nonneg : 0 ≤ X := h_sq_nonneg _
  have hY_sq_le : Y ^ 2 ≤ M * ((v ⬝ᵥ v) ^ 2) := by
    calc
      Y ^ 2 = (v ⬝ᵥ (P *ᵥ v)) ^ 2 := rfl
      _ ≤ (v ⬝ᵥ v) * ((P *ᵥ v) ⬝ᵥ (P *ᵥ v)) := by
        -- Cauchy-Schwarz
        have := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin d)) v (P *ᵥ v)
        simpa [dotProduct, sq] using this
      _ ≤ (v ⬝ᵥ v) * (M * (v ⬝ᵥ v)) := by
        refine mul_le_mul_of_nonneg_left (hP v) (h_dot_nonneg _)
      _ = M * ((v ⬝ᵥ v) ^ 2) := by ring
  have hY_abs_le : |Y| ≤ Real.sqrt M * (v ⬝ᵥ v) := by
    have h_nonneg_sqrtM : 0 ≤ Real.sqrt M := Real.sqrt_nonneg _
    have h_nonneg_dotvv : 0 ≤ v ⬝ᵥ v := h_dot_nonneg _
    have h_sq : |Y| ^ 2 ≤ (Real.sqrt M * (v ⬝ᵥ v)) ^ 2 := by
      calc
        |Y| ^ 2 = Y ^ 2 := by rw [sq_abs]
        _ ≤ M * ((v ⬝ᵥ v) ^ 2) := hY_sq_le
        _ = (Real.sqrt M) ^ 2 * ((v ⬝ᵥ v) ^ 2) := by rw [Real.sq_sqrt hM]
        _ = (Real.sqrt M * (v ⬝ᵥ v)) ^ 2 := by ring
    have h_nonneg_absY : 0 ≤ |Y| := abs_nonneg _
    have h_nonneg_rhs : 0 ≤ Real.sqrt M * (v ⬝ᵥ v) :=
      mul_nonneg h_nonneg_sqrtM h_nonneg_dotvv
    nlinarith
  have hX_sq_le : X ≤ M ^ 2 * ((z ⬝ᵥ z) * (v ⬝ᵥ v)) := by
    calc
      X = (w ⬝ᵥ v) ^ 2 := rfl
      _ ≤ (w ⬝ᵥ w) * (v ⬝ᵥ v) := by
        have := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin d)) w v
        simpa [dotProduct, sq] using this
      _ ≤ (M * ((A *ᵥ z) ⬝ᵥ (A *ᵥ z))) * (v ⬝ᵥ v) := by
        refine mul_le_mul_of_nonneg_right (hP (A *ᵥ z)) (h_dot_nonneg _)
      _ ≤ (M * (M * (z ⬝ᵥ z))) * (v ⬝ᵥ v) := by
        have htemp := mul_le_mul_of_nonneg_right (hA z) (h_dot_nonneg v)
        -- htemp: (A*z)⬝(A*z) * (v⬝v) ≤ (M * (z⬝z)) * (v⬝v)
        have hM_nonneg : 0 ≤ M := hM
        have hprod_nonneg : 0 ≤ M * (v ⬝ᵥ v) := mul_nonneg hM_nonneg (h_dot_nonneg _)
        nlinarith
      _ = M ^ 2 * ((z ⬝ᵥ z) * (v ⬝ᵥ v)) := by ring
  have h_dotzz_le : z ⬝ᵥ z ≤ (d : ℝ) * (‖z‖ ^ 2) := by
    have hsum : z ⬝ᵥ z = ∑ i : Fin d, z i * z i := rfl
    rw [hsum]
    calc
      ∑ i : Fin d, z i * z i = ∑ i : Fin d, (z i) ^ 2 := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        ring
      _ ≤ ∑ i : Fin d, (‖z‖ ^ 2) := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        have hzi_sq : (z i) ^ 2 ≤ ‖z‖ ^ 2 := by
          have h_abs_zi : |z i| ≤ ‖z‖ := norm_le_pi_norm z i
          have h_nonneg_norm : 0 ≤ ‖z‖ := norm_nonneg _
          have h_nonneg_abs : 0 ≤ |z i| := abs_nonneg _
          have h_sq_abs : |z i| ^ 2 = (z i) ^ 2 := sq_abs _
          have h_sq_le : |z i| ^ 2 ≤ ‖z‖ ^ 2 := by
            nlinarith
          rw [← h_sq_abs]
          exact h_sq_le
        exact hzi_sq
      _ = (Finset.card (Finset.univ : Finset (Fin d))) • (‖z‖ ^ 2) := by simp
      _ = (d : ℝ) * (‖z‖ ^ 2) := by simp
  have h_dotzz_le' : z ⬝ᵥ z ≤ (d : ℝ) * ((1 + ‖z‖) ^ 2) := by
    calc
      z ⬝ᵥ z ≤ (d : ℝ) * (‖z‖ ^ 2) := h_dotzz_le
      _ ≤ (d : ℝ) * ((1 + ‖z‖) ^ 2) := by
        refine mul_le_mul_of_nonneg_left ?_ (by simp)
        have h_nonneg_norm : 0 ≤ ‖z‖ := norm_nonneg _
        nlinarith
  calc
    |a * (X - Y)| = |a| * |X - Y| := by rw [abs_mul]
    _ ≤ |a| * (|X| + |Y|) := by
      refine mul_le_mul_of_nonneg_left (abs_sub _ _) (abs_nonneg _)
    _ = |a| * (X + |Y|) := by rw [abs_of_nonneg hX_nonneg]
    _ = |a| * X + |a| * |Y| := by ring
    _ ≤ |a| * (M ^ 2 * ((z ⬝ᵥ z) * (v ⬝ᵥ v))) + |a| * (Real.sqrt M * (v ⬝ᵥ v)) := by
      refine add_le_add ?_ ?_
      · refine mul_le_mul_of_nonneg_left hX_sq_le (abs_nonneg _)
      · refine mul_le_mul_of_nonneg_left hY_abs_le (abs_nonneg _)
    _ = |a| * (v ⬝ᵥ v) * (M ^ 2 * (z ⬝ᵥ z) + Real.sqrt M) := by ring
    _ ≤ |a| * (v ⬝ᵥ v) * (M ^ 2 * ((d : ℝ) * ((1 + ‖z‖) ^ 2)) + Real.sqrt M) := by
      refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (abs_nonneg _) (h_dot_nonneg _))
      have htemp : M ^ 2 * (z ⬝ᵥ z) ≤ M ^ 2 * ((d : ℝ) * ((1 + ‖z‖) ^ 2)) := by
        have hM_sq_nonneg : 0 ≤ M ^ 2 := by nlinarith
        refine mul_le_mul_of_nonneg_left h_dotzz_le' hM_sq_nonneg
      nlinarith
    _ = |a| * (v ⬝ᵥ v) * ((M ^ 2 * (d : ℝ)) * ((1 + ‖z‖) ^ 2) + Real.sqrt M) := by ring
    _ ≤ |a| * (v ⬝ᵥ v) * ((M ^ 2 * (d : ℝ)) * ((1 + ‖z‖) ^ 2) + Real.sqrt M * ((1 + ‖z‖) ^ 2)) := by
      refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (abs_nonneg _) (h_dot_nonneg _))
      have h_one_le : 1 ≤ (1 + ‖z‖) ^ 2 := by
        have h_nonneg_norm : 0 ≤ ‖z‖ := norm_nonneg _
        nlinarith
      nlinarith [Real.sqrt_nonneg M]
    _ = |a| * (v ⬝ᵥ v) * ((M ^ 2 * (d : ℝ) + Real.sqrt M) * ((1 + ‖z‖) ^ 2)) := by ring
    _ = |a| * (v ⬝ᵥ v) * (M ^ 2 * d + Real.sqrt M) * (1 + ‖z‖) ^ 2 := by ring

theorem shh_quad_generic {d : ℕ} (P A S : Matrix (Fin d) (Fin d) ℝ) (hP : P.PosSemidef)
    (hAA : A * Aᵀ = S) (hSP : S * P = 1) (a : ℝ) (ξ w : Fin d → ℝ) :
    |a * (((P *ᵥ (A *ᵥ ξ)) ⬝ᵥ w) ^ 2 - w ⬝ᵥ (P *ᵥ w))| ≤ |a| * (ξ ⬝ᵥ ξ + 1) * (w ⬝ᵥ (P *ᵥ w)) := by
  have hPt : Pᵀ = P := by
    have h := hP.isHermitian
    rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at h
  set b := Aᵀ *ᵥ (P *ᵥ w) with hb
  have h1 : (P *ᵥ (A *ᵥ ξ)) ⬝ᵥ w = ξ ⬝ᵥ b := by
    rw [hb, dotProduct_comm, dotProduct_mulVec, dotProduct_mulVec, dotProduct_comm, Matrix.mulVec_transpose,
      ← hPt, Matrix.vecMul_transpose, hPt]
  have h2 : b ⬝ᵥ b = w ⬝ᵥ (P *ᵥ w) := by
    rw [hb, dotProduct_mulVec, Matrix.vecMul_transpose, Matrix.mulVec_mulVec, hAA, Matrix.mulVec_mulVec, hSP,
      Matrix.one_mulVec, dotProduct_comm]
  have hCS : (ξ ⬝ᵥ b) ^ 2 ≤ (ξ ⬝ᵥ ξ) * (b ⬝ᵥ b) := by
    have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ ξ b
    simpa only [dotProduct, pow_two] using this
  have hY : 0 ≤ w ⬝ᵥ (P *ᵥ w) := by
    have := hP.dotProduct_mulVec_nonneg w
    simpa using this
  have hξ : 0 ≤ ξ ⬝ᵥ ξ := by
    simp only [dotProduct]; exact Finset.sum_nonneg fun i _ => mul_self_nonneg (ξ i)
  rw [h1, abs_mul, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg a)
  rw [h2] at hCS
  have hX : 0 ≤ (ξ ⬝ᵥ b) ^ 2 := sq_nonneg _
  rw [abs_le]; constructor <;> nlinarith

/-- `uᵀ M u - cᵀ M c = (u - c)ᵀ M (u + c)` for a symmetric `M`. -/
theorem quad_sub_eq (M : Matrix (Fin d) (Fin d) ℝ) (hM : Mᵀ = M) (u c : Fin d → ℝ) :
    df2Sq M u - df2Sq M c = (u - c) ⬝ᵥ (M *ᵥ (u + c)) := by
  unfold df2Sq
  have h : c ⬝ᵥ (M *ᵥ u) = u ⬝ᵥ (M *ᵥ c) := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hM, dotProduct_comm]
  rw [sub_dotProduct, mulVec_add, dotProduct_add, dotProduct_add, h]; ring

theorem quad_sub_le (M : Matrix (Fin d) (Fin d) ℝ) (hM : Mᵀ = M) (K : ℝ)
    (hK : ∀ v, |df2Sq M v| ≤ K * (v ⬝ᵥ v)) (u c : Fin d → ℝ) :
    |df2Sq M u - df2Sq M c| ≤ K * (Real.sqrt ((u - c) ⬝ᵥ (u - c)) * Real.sqrt ((u + c) ⬝ᵥ (u + c))) := by
  rw [quad_sub_eq M hM]; exact bilin_le_of_quad M hM K hK _ _

theorem df2Sq_vecMulVec (u v : Fin d → ℝ) : df2Sq (vecMulVec u u) v = (u ⬝ᵥ v) ^ 2 := by
  simp only [df2Sq, vecMulVec_mulVec]
  rw [op_smul_eq_smul, dotProduct_smul, smul_eq_mul, dotProduct_comm v u]; ring


/-! ## The path up to the stopping time -/

/-- The range coefficient: `λ κ₀ (L/(2ε)) ((32/9) d x + 1) + λ (8/ε)/(1 - λ) (2 d σ²)^{1/2}`, `x = log (1/δ)`. -/
noncomputable def rcS (p : Df2OPar) (d : ℕ) : ℝ :=
  p.lam * p.k0 * (p.Le / (2 * p.eps)) * (32 / 9 * d * Real.log (1 / p.δe) + 1) +
    p.lam * (8 / p.eps) / (1 - p.lam) * Real.sqrt (2 * d * p.sig2)

/-- `A_t = ∑_{u ≤ t} (ŝ''_u - s''_u(μ_u))`. -/
noncomputable def At (c : Df2Ctx d) (π : Df2Path d) (t : ℕ) : Matrix (Fin d) (Fin d) ℝ :=
  ∑ u ∈ Finset.range (t + 1), (c.shh π u - c.sHess π u)

/-- `vᵀ ŝ''_s v = λ κ₀ Y_s (⟨P_s A_s ξ_s, v⟩² - vᵀ P_s v)`. -/
theorem shh_quad (c : Df2Ctx d) (π : Df2Path d) (s : ℕ) (w : Fin d → ℝ) :
    df2Sq (c.shh π s) w = c.p.lam * c.p.k0 * c.Y π s *
      ((((c.st π s).P *ᵥ ((c.st π s).A *ᵥ π.xi s)) ⬝ᵥ w) ^ 2 - w ⬝ᵥ ((c.st π s).P *ᵥ w)) := by
  unfold Df2Ctx.shh
  rw [sq_smul, sq_sub, df2Sq_vecMulVec]
  rfl

section path

variable {c : Df2Ctx d} {δ : ℝ} {π : Df2Path d} {m : ℕ}

theorem rcS_nonneg (H : DetBase c δ π m) : 0 ≤ rcS c.p d := by
  have hl := H.rows.pos_lam
  have hl2 := H.rows.lam_le
  have hk := H.k0_pos
  have he := H.rows.pos_eps
  have hL := H.one_le_Le
  have hx := H.x_ge
  unfold rcS
  have h1 : 0 < 1 - c.p.lam := by linarith
  positivity

theorem Pn_sub_PBar (H : DetBase c δ π m) {t : ℕ} (ht : t ≤ c.tau π m) :
    c.Pn π t - c.PBar π (t + 1) = (c.p.eta * c.p.kap) • At c π t := by
  have hI := H.stInv_le_tau t ht
  have h0 : c.PBar π 0 = (c.st π 0).P := rfl
  rw [Df2Ctx.Pn_eq, hI.Pf, Df2Ctx.PBar_eq_sum, h0, At, Finset.sum_sub_distrib,
    Finset.sum_range_succ (fun u => c.shh π u)]
  module

theorem PBar_quad_mono (H : DetBase c δ π m) {s t : ℕ} (hst : s ≤ t) (ht : t ≤ c.tau π m) (v : Fin d → ℝ) :
    df2Sq (c.PBar π s) v ≤ df2Sq (c.PBar π t) v := by
  induction t with
  | zero => rw [Nat.le_zero.1 hst]
  | succ k ih =>
    rcases Nat.lt_or_ge s (k + 1) with h | h
    · have hk : k ≤ c.tau π m := by omega
      have h1 := ih (by omega) hk
      rw [Df2Ctx.PBar_succ, sq_add, sq_smul]
      have h2 := sq_nonneg_of_psd (H.sHess_psd hk) v
      have h3 := H.kap_pos
      nlinarith
    · rw [show s = k + 1 by omega]

/-- `vᵀ P_s v ≤ q_t(v) = 2 vᵀ P̄_t v` for `s ≤ t ≤ τ`. -/
theorem P_quad_le (H : DetBase c δ π m) {s t : ℕ} (hst : s ≤ t) (ht : t ≤ c.tau π m) (v : Fin d → ℝ) :
    df2Sq (c.st π s).P v ≤ 2 * df2Sq (c.PBar π t) v := by
  have hI := H.stInv_le_tau s (hst.trans ht)
  have h1 := sq_le_of_psd hI.pbh v
  rw [sq_smul] at h1
  linarith [PBar_quad_mono H hst ht v]

theorem PBar_quad_lower (H : DetBase c δ π m) {t : ℕ} (ht : t ≤ c.tau π m) (v : Fin d → ℝ) :
    2 * c.p.δe * (v ⬝ᵥ v) ≤ df2Sq (c.PBar π t) v := by
  have h := sq_le_of_psd (H.stInv_le_tau t ht).pbd v
  rw [sq_smul, sq_smul, sq_one] at h
  linarith

theorem PBar_quad_upper (H : DetBase c δ π m) {t : ℕ} (ht : t ≤ c.tau π m) (v : Fin d → ℝ) :
    2 * df2Sq (c.PBar π t) v ≤ c.p.δe⁻¹ * (v ⬝ᵥ v) := by
  have h := sq_le_of_psd (H.stInv_le_tau t ht).pb2 v
  rw [sq_smul, sq_smul, sq_one] at h
  linarith

theorem PBar_symm (H : DetBase c δ π m) {t : ℕ} (ht : t ≤ c.tau π m) : (c.PBar π t)ᵀ = c.PBar π t :=
  transpose_of_psd (H.PBar_psd ht)

theorem At_symm (H : DetBase c δ π m) {t : ℕ} (ht : t ≤ c.tau π m) : (At c π t)ᵀ = At c π t := by
  unfold At
  rw [transpose_sum]
  refine Finset.sum_congr rfl fun u hu => ?_
  have hut : u ≤ c.tau π m := (Nat.lt_succ_iff.1 (Finset.mem_range.1 hu)).trans ht
  have hI := H.stInv_le_tau u hut
  have hs2 : (c.sHess π u)ᵀ = c.sHess π u := hessM_transpose _ (H.si_at hut).c2 _
  rw [transpose_sub, hs2]
  congr 1
  unfold Df2Ctx.shh
  rw [transpose_smul, transpose_sub, transpose_vecMulVec, P_symm hI]

/-- On G: `|vᵀ ŝ''_s v| ≤ λ κ₀ (L/(2ε)) ((32/9) d x + 1) vᵀ P_s v`. -/
theorem shh_quad_le (H : DetBase c δ π m) (hG : c.EvG π m) {s : ℕ} (hs : s ≤ c.tau π m) (w : Fin d → ℝ) :
    |df2Sq (c.shh π s) w| ≤ c.p.lam * c.p.k0 * (c.p.Le / (2 * c.p.eps)) *
      (32 / 9 * d * Real.log (1 / c.p.δe) + 1) * df2Sq (c.st π s).P w := by
  have hI := H.stInv_le_tau s hs
  have g := shh_quad_generic (c.st π s).P (c.st π s).A (c.st π s).S hI.pd.posSemidef hI.AA hI.SP
    (c.p.lam * c.p.k0 * c.Y π s) (π.xi s) w
  rw [shh_quad]
  refine g.trans ?_
  have hY := ybd_G H hG hs
  have hξ := xibd_G H hG hs
  have hl := H.rows.pos_lam
  have hk := H.k0_pos
  have hP0 := sq_nonneg_of_psd hI.pd.posSemidef w
  have hP0' : 0 ≤ w ⬝ᵥ ((c.st π s).P *ᵥ w) := hP0
  have ha : |c.p.lam * c.p.k0 * c.Y π s| ≤ c.p.lam * c.p.k0 * (c.p.Le / (2 * c.p.eps)) := by
    rw [abs_mul, abs_of_pos (mul_pos hl hk)]
    exact mul_le_mul_of_nonneg_left hY (mul_pos hl hk).le
  have hξ0 := dot_self_nonneg' (π.xi s)
  have hb : π.xi s ⬝ᵥ π.xi s + 1 ≤ 32 / 9 * d * Real.log (1 / c.p.δe) + 1 := by linarith
  calc |c.p.lam * c.p.k0 * c.Y π s| * (π.xi s ⬝ᵥ π.xi s + 1) * (w ⬝ᵥ ((c.st π s).P *ᵥ w))
      ≤ c.p.lam * c.p.k0 * (c.p.Le / (2 * c.p.eps)) * (32 / 9 * d * Real.log (1 / c.p.δe) + 1) *
          (w ⬝ᵥ ((c.st π s).P *ᵥ w)) := by
        apply mul_le_mul_of_nonneg_right _ hP0'
        exact mul_le_mul ha hb (by linarith) (by have := H.rows.pos_eps; have := H.one_le_Le; positivity)
    _ = _ := rfl

/-- X6 at `μ_s`: `|vᵀ s''_s(μ_s) v| ≤ λ (8/ε)/(1 - λ) (2 d σ²)^{1/2} vᵀ P_s v`. -/
theorem sHess_quad_le (H : DetBase c δ π m) {s : ℕ} (hs : s ≤ c.tau π m) (w : Fin d → ℝ) :
    |df2Sq (c.sHess π s) w| ≤
      c.p.lam * (8 / c.p.eps) / (1 - c.p.lam) * Real.sqrt (2 * d * c.p.sig2) * df2Sq (c.st π s).P w := by
  have h := (H.si_at hs).hess2 (WithLp.toLp 2 (c.st π s).mu) w
  rwa [H.AAinv hs] at h

/-- On G: `|vᵀ ŝ''_s v| + |vᵀ s''_s(μ_s) v| ≤ Rc vᵀ P_s v`. -/
theorem round_le (H : DetBase c δ π m) (hG : c.EvG π m) {s : ℕ} (hs : s ≤ c.tau π m) (w : Fin d → ℝ) :
    |df2Sq (c.shh π s) w| + |df2Sq (c.sHess π s) w| ≤ rcS c.p d * df2Sq (c.st π s).P w := by
  have h1 := shh_quad_le H hG hs w
  have h2 := sHess_quad_le H hs w
  unfold rcS
  linarith

/-- On G: `|vᵀ A_t v| ≤ (n Rc/δ) |v|²` for `t ≤ τ`. -/
theorem At_quad_le (H : DetBase c δ π m) (hG : c.EvG π m) {t : ℕ} (ht : t ≤ c.tau π m) (w : Fin d → ℝ) :
    |df2Sq (At c π t) w| ≤ c.n * rcS c.p d / c.p.δe * (w ⬝ᵥ w) := by
  have hR := rcS_nonneg H
  have hde := H.rows.pos_de
  have hw := dot_self_nonneg' w
  unfold At
  rw [sq_sum]
  have hpt : ∀ u ∈ Finset.range (t + 1), |df2Sq (c.shh π u - c.sHess π u) w| ≤ rcS c.p d * (c.p.δe⁻¹ * (w ⬝ᵥ w)) := by
    intro u hu
    have hut : u ≤ c.tau π m := (Nat.lt_succ_iff.1 (Finset.mem_range.1 hu)).trans ht
    have hI := H.stInv_le_tau u hut
    rw [sq_sub]
    have h1 := round_le H hG hut w
    have h2 := quad_le_of_psd (P_upper H hI) w
    calc |df2Sq (c.shh π u) w - df2Sq (c.sHess π u) w| ≤ |df2Sq (c.shh π u) w| + |df2Sq (c.sHess π u) w| :=
          abs_sub _ _
      _ ≤ rcS c.p d * df2Sq (c.st π u).P w := h1
      _ ≤ rcS c.p d * (c.p.δe⁻¹ * (w ⬝ᵥ w)) := mul_le_mul_of_nonneg_left h2 hR
  have htn : ((t + 1 : ℕ) : ℝ) ≤ c.n := by
    have := H.le_tau_lt ht; have := H.hmn; exact_mod_cast (by omega : t + 1 ≤ c.n)
  calc |∑ u ∈ Finset.range (t + 1), df2Sq (c.shh π u - c.sHess π u) w|
      ≤ ∑ u ∈ Finset.range (t + 1), |df2Sq (c.shh π u - c.sHess π u) w| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _u ∈ Finset.range (t + 1), rcS c.p d * (c.p.δe⁻¹ * (w ⬝ᵥ w)) := Finset.sum_le_sum hpt
    _ = ((t + 1 : ℕ) : ℝ) * (rcS c.p d * (c.p.δe⁻¹ * (w ⬝ᵥ w))) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ c.n * (rcS c.p d * (c.p.δe⁻¹ * (w ⬝ᵥ w))) := by
        apply mul_le_mul_of_nonneg_right htn; positivity
    _ = c.n * rcS c.p d / c.p.δe * (w ⬝ᵥ w) := by rw [div_eq_mul_inv]; ring

end path


/-! ## One round of the context at the parameters -/

/-- The variance factor `Xv = T · 9 n + n (Wb)^{1/2} c_T` with `√T = 16 x`. -/
noncomputable def xvS (p : Df2OPar) (d n : ℕ) : ℝ :=
  (16 * Real.log (1 / p.δe)) ^ 2 * (9 * n) +
    n * (Real.sqrt (72 + 25600 * (p.R ^ 4 + 3 * (d : ℝ) ^ 2) / p.eps ^ 4) *
      Real.sqrt (Real.sqrt 2027025 * Real.exp (-Real.sqrt ((16 * Real.log (1 / p.δe)) ^ 2) / 4)))

theorem xvS_nonneg (p : Df2OPar) (d n : ℕ) : 0 ≤ xvS p d n := by
  unfold xvS; positivity

/-- The bound of the direction `phiH (fun _ => v)` on the bound condition. -/
noncomputable def kPhi (p : Df2OPar) (d : ℕ) (M : ℝ) (v : Fin d → ℝ) : ℝ :=
  |p.lam * p.k0| * (v ⬝ᵥ v) * (M ^ 2 * d + Real.sqrt M)

theorem kPhi_nonneg (p : Df2OPar) (d : ℕ) (M : ℝ) (v : Fin d → ℝ) : 0 ≤ kPhi p d M v := by
  unfold kPhi; have := dot_self_nonneg' v; positivity

theorem phiH_le (n : ℕ) (δ M : ℝ) (hM : 0 ≤ M) (v : Fin d → ℝ) (st : Df2St d) (hst : stB M st) (z : Fin d → ℝ) :
    |phiH n δ (fun _ => v) st z| ≤ kPhi (df2oPar d n δ) d M v * (1 + ‖z‖) ^ 2 :=
  quad_growth st.P st.A M _ hM hst.2.1 hst.2.2 v z

theorem continuous_phiH (n : ℕ) (δ : ℝ) (v : Fin d → ℝ) (st : Df2St d) :
    Continuous fun z => phiH n δ (fun _ => v) st z := by
  unfold phiH lin
  have h : Continuous fun z : Fin d → ℝ => st.P *ᵥ (st.A *ᵥ z) :=
    (Matrix.mulVecLin st.P).continuous_of_finiteDimensional.comp
      (Matrix.mulVecLin st.A).continuous_of_finiteDimensional
  exact continuous_const.mul (((h.dotProduct continuous_const).pow 2).sub continuous_const)

/-! ## The increments on the path -/

section incr

variable (n : ℕ) (δ : ℝ) {Θ : Type} (Kθ : Θ → Set (E d)) (gθ : ℕ → Θ → E d → ℝ) (ap : ApFun d) {Ω : Type}
  (θ : Ω → Θ) (ξ : ℕ → Ω → Fin d → ℝ) (e : ℕ → Ω → ℝ)

/-- The directions of the net. -/
noncomputable def phiC (c : E d) : Df2St d → (Fin d → ℝ) → ℝ := phiH n δ (fun _ => WithLp.ofLp c)

end incr


end AdversarialBco.Poly.EvSI.SDF
