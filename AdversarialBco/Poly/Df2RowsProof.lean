/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.Df2Layer2

@[expose] public section

/-!
# The rows at the parameters of the learner

`df2RowsHold : Df2RowsHold`. `RowHyp p d n` lists what the rows read of `p = df2oPar d n δ` in the regime
`ε ≤ 1/2`: the closed forms of the parameters, `L ≥ 504`, the condition `x ≥ 14 + 3 log(d n)` on
`x = log(1/δ_e)`, `δ_e (d n)³ n ≤ e^{-14}`, and the regime in the form `29000 d^{3/2} L⁵ ≤ n^{1/2}`
(the paper's rows lemma of the epoch). Each row is then a lemma on `RowHyp`; the rows
main, margin, negative, bonus and ball follow from bounds of their terms against `ρ` (the trace term `d L/λ` is
`ρ/2`, the others are below `ρ/300`).
-/

namespace AdversarialBco.Poly

namespace Layer2

/-- The parameters of `df2oPar d n δ` in the regime, as the rows read them. -/
structure RowHyp (p : Df2OPar) (d n : ℕ) : Prop where
  hd : 1 ≤ d
  hn : 1 ≤ n
  de_pos : 0 < p.δe
  de_lt : p.δe < 1
  Le : p.Le = 36 * Real.log (1 / p.δe)
  L504 : 504 ≤ p.Le
  cx : 14 + 3 * Real.log ((d : ℝ) * n) ≤ Real.log (1 / p.δe)
  dsmall : p.δe * ((d : ℝ) * n) ^ 3 * n ≤ Real.exp (-14)
  lam : p.lam = 1 / (725 * d * p.Le ^ 2)
  eta : p.eta = Real.sqrt d / (p.Le * Real.sqrt n)
  sig2 : p.sig2 = 1 / (8 * p.Le)
  rho : p.rho = 2 * 725 * (d : ℝ) ^ 2 * p.Le ^ 3
  eps : p.eps = 20 * 725 * (d * Real.sqrt d) * p.Le ^ 5 / Real.sqrt n
  eps_le : p.eps ≤ 1 / 2
  reg : 29000 * (d * Real.sqrt d) * p.Le ^ 5 ≤ Real.sqrt n
  kap : p.kap = 1 / 4
  theta : p.theta = 1
  alpha : p.alpha = 1 / 4
  c1 : p.c1 = 8
  gam : p.gam = 1 / 100
  k0 : p.k0 = ((1 - p.lam) ^ 2)⁻¹
  R : p.R = 134 * d * Real.sqrt (Real.log (2 * d + 2))
  hlog : Real.log (2 * d + 2) ≤ Real.log (1 / p.δe)

/-! ### Rows read directly -/

theorem row_eta_le (p : Df2OPar) (d n : ℕ) (H : RowHyp p d n) : p.eta ≤ 1 := by
  rw [H.eta]
  have hd_nonneg : 0 ≤ (d : ℝ) := by exact_mod_cast Nat.zero_le d
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast H.hd
  have hsqrt_d_nonneg : 0 ≤ Real.sqrt (d : ℝ) := Real.sqrt_nonneg _
  have hsqrt_n_nonneg : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  have hsqrt_n_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast H.hn)
  have hLe_ge_one : (1 : ℝ) ≤ p.Le := by
    have h504 : (504 : ℝ) ≤ p.Le := H.L504
    linarith
  have hLe_pos : 0 < p.Le := by linarith
  have hdenom_pos : 0 < p.Le * Real.sqrt (n : ℝ) := mul_pos hLe_pos hsqrt_n_pos
  refine (div_le_one hdenom_pos).mpr ?_
  have h_sqrt_d_le_d : Real.sqrt (d : ℝ) ≤ (d : ℝ) := by
    have hsq : (d : ℝ) ≤ (d : ℝ) ^ 2 := by
      nlinarith
    calc
      Real.sqrt (d : ℝ) ≤ Real.sqrt ((d : ℝ) ^ 2) := Real.sqrt_le_sqrt hsq
      _ = d := Real.sqrt_sq hd_nonneg
  have h_d_le_sqrt_n : (d : ℝ) ≤ Real.sqrt (n : ℝ) := by
    have htemp := H.reg
    have hsqrt_d_ge_one : (1 : ℝ) ≤ Real.sqrt (d : ℝ) := by
      calc
        (1 : ℝ) = Real.sqrt ((1 : ℝ) ^ 2) := by norm_num
        _ ≤ Real.sqrt (d : ℝ) := Real.sqrt_le_sqrt (by exact_mod_cast H.hd)
    have hLe5_ge_one : (1 : ℝ) ≤ p.Le ^ 5 := by
      have hsq : (1 : ℝ) ≤ p.Le ^ 2 := by nlinarith
      have hcube : (1 : ℝ) ≤ p.Le ^ 3 := by nlinarith
      have hquad : (1 : ℝ) ≤ p.Le ^ 4 := by nlinarith
      nlinarith
    have h_mid : (d : ℝ) ≤ 29000 * ((d : ℝ) * Real.sqrt (d : ℝ)) * (p.Le ^ 5) := by
      have h29000_ge_one : (1 : ℝ) ≤ 29000 := by norm_num
      have h_nonneg : 0 ≤ (d : ℝ) * Real.sqrt (d : ℝ) * (p.Le ^ 5) := by positivity
      calc
        (d : ℝ) = (d : ℝ) * 1 := by ring
        _ ≤ (d : ℝ) * Real.sqrt (d : ℝ) :=
          mul_le_mul_of_nonneg_left hsqrt_d_ge_one hd_nonneg
        _ = (d : ℝ) * Real.sqrt (d : ℝ) * 1 := by ring
        _ ≤ (d : ℝ) * Real.sqrt (d : ℝ) * (p.Le ^ 5) :=
          mul_le_mul_of_nonneg_left hLe5_ge_one (mul_nonneg hd_nonneg hsqrt_d_nonneg)
        _ ≤ 29000 * ((d : ℝ) * Real.sqrt (d : ℝ)) * (p.Le ^ 5) := by
          calc
            (d : ℝ) * Real.sqrt (d : ℝ) * (p.Le ^ 5) = ((d : ℝ) * Real.sqrt (d : ℝ) * (p.Le ^ 5)) * 1 := by ring
            _ ≤ ((d : ℝ) * Real.sqrt (d : ℝ) * (p.Le ^ 5)) * 29000 :=
              mul_le_mul_of_nonneg_left h29000_ge_one h_nonneg
            _ = 29000 * ((d : ℝ) * Real.sqrt (d : ℝ)) * (p.Le ^ 5) := by ring
    linarith
  calc
    Real.sqrt (d : ℝ) ≤ (d : ℝ) := h_sqrt_d_le_d
    _ ≤ Real.sqrt (n : ℝ) := h_d_le_sqrt_n
    _ = 1 * Real.sqrt (n : ℝ) := by ring
    _ ≤ p.Le * Real.sqrt (n : ℝ) := mul_le_mul_of_nonneg_right hLe_ge_one hsqrt_n_nonneg

theorem row_one_le_R (p : Df2OPar) (d n : ℕ) (H : RowHyp p d n) : 1 ≤ p.R := by
  have hd' : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast H.hd
  have h_exp_lt : Real.exp 1 < 2 * (d : ℝ) + 2 := by
    have h : Real.exp 1 < 3 := Real.exp_one_lt_three
    have h3 : (3 : ℝ) ≤ 2 * (d : ℝ) + 2 := by nlinarith
    linarith
  have h_log_one_le : 1 ≤ Real.log (2 * (d : ℝ) + 2) := by
    calc
      1 = Real.log (Real.exp 1) := by rw [Real.log_exp 1]
      _ ≤ Real.log (2 * (d : ℝ) + 2) := Real.log_le_log (Real.exp_pos 1) (le_of_lt h_exp_lt)
  have h_sqrt_one_le : 1 ≤ Real.sqrt (Real.log (2 * (d : ℝ) + 2)) :=
    (Real.one_le_sqrt).mpr h_log_one_le
  rw [H.R]
  nlinarith

theorem row_k0_le (p : Df2OPar) (d n : ℕ) (H : RowHyp p d n) : p.k0 ≤ 21 / 20 := by
  rw [H.k0, H.lam]
  have hd' : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast H.hd
  have hL504 : (504 : ℝ) ≤ p.Le := H.L504
  have hpos_denom1 : 0 < 725 * (d : ℝ) * p.Le ^ 2 := by
    positivity
  have hpos_denom2 : 0 < 725 * (504 : ℝ) ^ 2 := by
    norm_num
  have h_denom_le : 725 * (504 : ℝ) ^ 2 ≤ 725 * (d : ℝ) * p.Le ^ 2 := by
    nlinarith
  have h_lam_le_tenth : 1 / (725 * (d : ℝ) * p.Le ^ 2) ≤ 1 / 100 := by
    calc
      1 / (725 * (d : ℝ) * p.Le ^ 2) ≤ 1 / (725 * (504 : ℝ) ^ 2) :=
        (one_div_le_one_div hpos_denom1 hpos_denom2).mpr h_denom_le
      _ ≤ 1 / 100 := by norm_num
  have h_one_minus : (99 : ℝ) / 100 ≤ 1 - 1 / (725 * (d : ℝ) * p.Le ^ 2) := by
    linarith
  have h_sq_le : ((99 : ℝ) / 100) ^ 2 ≤ (1 - 1 / (725 * (d : ℝ) * p.Le ^ 2)) ^ 2 := by
    nlinarith
  have h_inv_le : ((1 - 1 / (725 * (d : ℝ) * p.Le ^ 2)) ^ 2)⁻¹ ≤ (((99 : ℝ) / 100) ^ 2)⁻¹ := by
    have hpos_sq1 : 0 < (1 - 1 / (725 * (d : ℝ) * p.Le ^ 2)) ^ 2 := by positivity
    have hpos_sq2 : 0 < ((99 : ℝ) / 100) ^ 2 := by norm_num
    -- Use one_div_le_one_div: 1/a ≤ 1/b ↔ b ≤ a
    -- We have h_sq_le: ((99/100)^2) ≤ ((1-lam)^2)
    -- So 1/((1-lam)^2) ≤ 1/((99/100)^2)
    -- i.e. ((1-lam)^2)⁻¹ ≤ ((99/100)^2)⁻¹
    simpa [div_eq_inv_mul] using
      (one_div_le_one_div hpos_sq1 hpos_sq2).mpr h_sq_le
  have h_final : (((99 : ℝ) / 100) ^ 2)⁻¹ ≤ 21 / 20 := by
    norm_num
  linarith

theorem row_r1 (p : Df2OPar) (d n : ℕ) (H : RowHyp p d n) : 2 * d * p.sig2 * df2Mw d ^ 2 ≤ 1 := by
  have hd : 1 ≤ d := H.hd
  have hn : 1 ≤ n := H.hn
  have hLe : 504 ≤ p.Le := H.L504
  have hsig2 : p.sig2 = 1 / (8 * p.Le) := H.sig2
  have hd' : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hLe' : (504 : ℝ) ≤ p.Le := by exact_mod_cast hLe
  rw [hsig2, df2Mw]
  have hd_pos : (0 : ℝ) < d := by
    have : (1 : ℕ) ≤ d := hd
    exact_mod_cast Nat.one_pos.trans_le this
  have hd_ne_zero : (d : ℝ) ≠ 0 := by linarith
  have hLe_pos : 0 < p.Le := by linarith
  have hLe_ne_zero : p.Le ≠ 0 := by linarith
  field_simp [hd_ne_zero, hLe_ne_zero]
  have hsq : (Real.sqrt ((d : ℝ) + 1)) ^ 2 = (d : ℝ) + 1 := Real.sq_sqrt (by linarith)
  rw [hsq]
  nlinarith

theorem row_r4 (p : Df2OPar) (d n : ℕ) (H : RowHyp p d n) :
    10 * Real.sqrt p.Le + Real.sqrt (8 / df2C0) * p.Le ≤ p.Le := by
  have hLe : 0 ≤ p.Le := le_trans (by norm_num) H.L504
  have hsqrt8 : Real.sqrt (8 / df2C0) ≤ 12/25 := by
    have hsq : (8/36 : ℝ) ≤ ((12/25 : ℝ)) ^ 2 := by nlinarith
    calc
      Real.sqrt (8 / df2C0) = Real.sqrt (8/36) := rfl
      _ ≤ Real.sqrt ((12/25)^2) := Real.sqrt_le_sqrt hsq
      _ = 12/25 := Real.sqrt_sq (by norm_num)
  have hsq : 22 ≤ Real.sqrt p.Le := by
    have hsq' : (22 : ℝ)^2 ≤ p.Le := by
      have h484 : (22 : ℝ)^2 = 484 := by norm_num
      rw [h484]
      exact le_trans (by norm_num) H.L504
    exact ((Real.le_sqrt (by norm_num) hLe).2 hsq')
  have h10s : 10 * Real.sqrt p.Le ≤ (10/22 : ℝ) * p.Le := by
    have h : 22 * Real.sqrt p.Le ≤ p.Le := by
      calc
        22 * Real.sqrt p.Le ≤ Real.sqrt p.Le * Real.sqrt p.Le := by
          nlinarith
        _ = p.Le := Real.mul_self_sqrt hLe
    nlinarith
  have hsqrtL : Real.sqrt (8 / df2C0) * p.Le ≤ (12/25 : ℝ) * p.Le := by
    nlinarith
  calc
    10 * Real.sqrt p.Le + Real.sqrt (8 / df2C0) * p.Le ≤ (10/22 : ℝ) * p.Le + (12/25 : ℝ) * p.Le := by
      nlinarith
    _ = ((10/22 : ℝ) + (12/25 : ℝ)) * p.Le := by ring
    _ ≤ 1 * p.Le := by
      nlinarith
    _ = p.Le := by ring

theorem row_r5p (p : Df2OPar) (d n : ℕ) (H : RowHyp p d n) :
    352 / df2C0 * d * p.Le ^ 2 / (p.lam * p.eta * p.eps) ≤ n := by
  rcases H with ⟨hd, hn, de_pos, de_lt, Le_eq, L504, cx, dsmall, lam_eq, eta_eq, sig2_eq, rho_eq, eps_eq, eps_le, reg, kap_eq, theta_eq, alpha_eq, c1_eq, gam_eq, k0_eq, R_eq, hlog⟩
  have hd_pos : 0 < (d : ℝ) := by
    have h : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  have hn_pos : 0 < (n : ℝ) := by
    have h : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hL_pos : 0 < p.Le := by linarith
  have hL_ne_zero : p.Le ≠ 0 := by linarith
  have hd_ne_zero : (d : ℝ) ≠ 0 := by linarith
  have hn_ne_zero : (n : ℝ) ≠ 0 := by linarith
  have hsqrt_d_pos : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr hd_pos
  have hsqrt_n_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn_pos
  have hsqrt_d_ne_zero : Real.sqrt (d : ℝ) ≠ 0 := by linarith
  have hsqrt_n_ne_zero : Real.sqrt (n : ℝ) ≠ 0 := by linarith
  have hprod_eq : p.lam * p.eta * p.eps = 20 * (d : ℝ) * p.Le ^ 2 / (n : ℝ) := by
    rw [lam_eq, eta_eq, eps_eq]
    field_simp [hL_ne_zero, hd_ne_zero, hsqrt_d_ne_zero, hsqrt_n_ne_zero]
    nlinarith [Real.sq_sqrt (by linarith : 0 ≤ (d : ℝ)), Real.sq_sqrt (by linarith : 0 ≤ (n : ℝ))]
  have hC0 : (df2C0 : ℝ) = 36 := rfl
  rw [hC0, hprod_eq]
  rw [div_div_eq_mul_div]
  field_simp [hd_ne_zero, hL_ne_zero, hn_ne_zero]
  nlinarith

theorem row_r6 (p : Df2OPar) (d n : ℕ) (H : RowHyp p d n) :
    8 * p.eta * p.lam * Real.sqrt (2 * d * p.sig2) / p.eps ≤ 1 := by
  rcases H with ⟨hd, hn, de_pos, de_lt, Le, L504, cx, dsmall, lam, eta, sig2, rho, eps, eps_le, reg, kap, theta, alpha, c1, gam, k0, R, hlog⟩
  have hd' : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hd0 : 0 ≤ (d : ℝ) := by exact_mod_cast Nat.zero_le d
  have hn0 : 0 ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
  have hLpos : 0 < p.Le := by linarith
  have hL1 : (1 : ℝ) ≤ p.Le := by linarith
  have hL_nonneg : 0 ≤ p.Le := by linarith
  have h_eps_pos : 0 < p.eps := by
    rw [eps]
    have hd0' : 0 < (d : ℝ) := by linarith
    have hs_pos : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr hd0'
    have hn0' : 0 < (n : ℝ) := by linarith
    have ht_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0'
    positivity
  have h_nonneg : 0 ≤ 8 * p.eta * p.lam := by
    rw [lam, eta]
    have hs_nonneg : 0 ≤ Real.sqrt (d : ℝ) := Real.sqrt_nonneg _
    have ht_nonneg : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
    positivity
  -- bound sqrt(2*d*sig2) ≤ sqrt(d)
  have h_sqrt_bound : Real.sqrt (2 * (d : ℝ) * p.sig2) ≤ Real.sqrt (d : ℝ) := by
    rw [sig2]
    have h_inner : 2 * (d : ℝ) * (1 / (8 * p.Le)) ≤ (d : ℝ) := by
      have hpos : 0 < 8 * p.Le := by positivity
      field_simp [hpos.ne']
      nlinarith
    exact Real.sqrt_le_sqrt h_inner
  have h_main : 8 * p.eta * p.lam * Real.sqrt (2 * (d : ℝ) * p.sig2) / p.eps ≤
      8 * p.eta * p.lam * Real.sqrt (d : ℝ) / p.eps := by
    gcongr
  -- compute η * λ / ε = 1/(725*14500*d²*L⁸)
  have h_eta_lam_div_eps : p.eta * p.lam / p.eps = 1 / (725 * 14500 * (d : ℝ) ^ 2 * p.Le ^ 8) := by
    rw [lam, eta, eps]
    field_simp [h_eps_pos.ne', show 725 * 14500 * (d : ℝ) ^ 2 * p.Le ^ 8 ≠ 0 from by positivity]
    ring
  -- now rewrite 8*η*λ*s/ε = 8*s*(η*λ/ε)
  have h_expr : 8 * p.eta * p.lam * Real.sqrt (d : ℝ) / p.eps =
      8 * Real.sqrt (d : ℝ) / (725 * 14500 * (d : ℝ) ^ 2 * p.Le ^ 8) := by
    calc
      8 * p.eta * p.lam * Real.sqrt (d : ℝ) / p.eps =
          8 * Real.sqrt (d : ℝ) * (p.eta * p.lam / p.eps) := by ring
      _ = 8 * Real.sqrt (d : ℝ) * (1 / (725 * 14500 * (d : ℝ) ^ 2 * p.Le ^ 8)) := by rw [h_eta_lam_div_eps]
      _ = 8 * Real.sqrt (d : ℝ) / (725 * 14500 * (d : ℝ) ^ 2 * p.Le ^ 8) := by ring
  rw [h_expr] at h_main
  -- now show 8*s/(725*14500*d²*L⁸) ≤ 1
  -- using s ≤ d (since d ≥ 1) and d ≥ 1, L ≥ 1
  have h_final : 8 * Real.sqrt (d : ℝ) / (725 * 14500 * (d : ℝ) ^ 2 * p.Le ^ 8) ≤ 1 := by
    have h_denom_pos : 0 < 725 * 14500 * (d : ℝ) ^ 2 * p.Le ^ 8 := by positivity
    rw [div_le_one h_denom_pos]
    have h_s_le_d : Real.sqrt (d : ℝ) ≤ (d : ℝ) := by
      have hsq : (Real.sqrt (d : ℝ)) ^ 2 = (d : ℝ) := Real.sq_sqrt hd0
      have hd_sq : (d : ℝ) ≤ (d : ℝ) ^ 2 := by
        calc
          (d : ℝ) = (d : ℝ) * 1 := by ring
          _ ≤ (d : ℝ) * (d : ℝ) := mul_le_mul_of_nonneg_left hd' hd0
          _ = (d : ℝ) ^ 2 := by ring
      have h_nonneg_sqrt : 0 ≤ Real.sqrt (d : ℝ) := Real.sqrt_nonneg _
      nlinarith
    have h_d_le_d_sq : (d : ℝ) ≤ (d : ℝ) ^ 2 := by
      calc
        (d : ℝ) = (d : ℝ) * 1 := by ring
        _ ≤ (d : ℝ) * (d : ℝ) := mul_le_mul_of_nonneg_left hd' hd0
        _ = (d : ℝ) ^ 2 := by ring
    have h_L_pow : (1 : ℝ) ≤ p.Le ^ 8 := by
      have hL_nonneg : 0 ≤ p.Le := by linarith
      have h2 : (1 : ℝ) ≤ p.Le ^ 2 := by
        calc
          (1 : ℝ) = (1 : ℝ) * (1 : ℝ) := by norm_num
          _ ≤ p.Le * p.Le := mul_le_mul hL1 hL1 (by norm_num) hL_nonneg
          _ = p.Le ^ 2 := by ring
      have h4 : (1 : ℝ) ≤ p.Le ^ 4 := by
        calc
          (1 : ℝ) = (1 : ℝ) * (1 : ℝ) := by norm_num
          _ ≤ p.Le ^ 2 * p.Le ^ 2 := mul_le_mul h2 h2 (by norm_num) (pow_nonneg hL_nonneg 2)
          _ = p.Le ^ 4 := by ring
      calc
        (1 : ℝ) = (1 : ℝ) * (1 : ℝ) := by norm_num
        _ ≤ p.Le ^ 4 * p.Le ^ 4 := mul_le_mul h4 h4 (by norm_num) (pow_nonneg hL_nonneg 4)
        _ = p.Le ^ 8 := by ring
    have hconst : (8 : ℝ) ≤ 725 * 14500 * p.Le ^ 8 := by
      have h725 : (8 : ℝ) ≤ 725 * 14500 := by norm_num
      calc
        (8 : ℝ) ≤ 725 * 14500 := h725
        _ = 725 * 14500 * 1 := by ring
        _ ≤ 725 * 14500 * p.Le ^ 8 := mul_le_mul_of_nonneg_left h_L_pow (by norm_num)
    have h3 : 8 * (d : ℝ) ^ 2 ≤ 725 * 14500 * (d : ℝ) ^ 2 * p.Le ^ 8 := by
      have hd_sq_nonneg : 0 ≤ (d : ℝ) ^ 2 := pow_nonneg hd0 2
      calc
        8 * (d : ℝ) ^ 2 ≤ (725 * 14500 * p.Le ^ 8) * (d : ℝ) ^ 2 := by
          gcongr
        _ = 725 * 14500 * (d : ℝ) ^ 2 * p.Le ^ 8 := by ring
    have h_goal : 8 * Real.sqrt (d : ℝ) ≤ 725 * 14500 * (d : ℝ) ^ 2 * p.Le ^ 8 := by
      linarith
    exact h_goal
  linarith

theorem row_r6a (p : Df2OPar) (d n : ℕ) (H : RowHyp p d n) : p.eta * p.lam * p.Le / (2 * p.eps) ≤ 1 := by
  rw [H.eta, H.lam, H.eps]
  have hLe_pos : 0 < p.Le := by
    rw [H.Le]
    have hlogpos : 0 < Real.log (1 / p.δe) := Real.log_pos ((one_lt_one_div H.de_pos H.de_lt))
    nlinarith
  have hd_pos_nat : 0 < d := Nat.zero_lt_one.trans_le H.hd
  have hn_pos_nat : 0 < n := Nat.zero_lt_one.trans_le H.hn
  have hsqrt_d_pos : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hd_pos_nat)
  have hsqrt_n_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hn_pos_nat)
  have hd_pos : 0 < (d : ℝ) := by exact_mod_cast hd_pos_nat
  have hd_ge_one : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast H.hd
  have hn_ge_one : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast H.hn
  have hdenom_pos : 0 < 2 * (20 * 725 * ((d : ℝ) * Real.sqrt (d : ℝ)) * p.Le ^ 5 / Real.sqrt (n : ℝ)) := by
    positivity
  apply (div_le_one hdenom_pos).mpr
  field_simp [hLe_pos.ne.symm, hsqrt_n_pos.ne.symm, hsqrt_d_pos.ne.symm, hd_pos.ne.symm]
  have hLe_ge_504 : (504 : ℝ) ≤ p.Le := H.L504
  have hLe_ge_one : (1 : ℝ) ≤ p.Le := by linarith
  have hp7 : (1 : ℝ) ≤ p.Le ^ 7 := one_le_pow₀ hLe_ge_one
  have hd2 : (1 : ℝ) ≤ (d : ℝ) ^ 2 := one_le_pow₀ hd_ge_one
  have h725sq : (1 : ℝ) ≤ 725 ^ 2 := by norm_num
  have h40 : (1 : ℝ) ≤ (2 : ℝ) * 20 := by norm_num
  have hprod : (1 : ℝ) ≤ p.Le ^ 7 * 725 ^ 2 * (d : ℝ) ^ 2 * 2 * 20 := by
    have hA : (1 : ℝ) ≤ p.Le ^ 7 := hp7
    have hB : (1 : ℝ) ≤ 725 ^ 2 := h725sq
    have hC : (1 : ℝ) ≤ (d : ℝ) ^ 2 := hd2
    have hD : (1 : ℝ) ≤ (2 : ℝ) := by norm_num
    have hE : (1 : ℝ) ≤ (20 : ℝ) := by norm_num
    have hAB : (1 : ℝ) ≤ p.Le ^ 7 * 725 ^ 2 := by
      calc
        (1 : ℝ) = (1 : ℝ) * (1 : ℝ) := by norm_num
        _ ≤ p.Le ^ 7 * 725 ^ 2 := mul_le_mul hA hB (by positivity) (by positivity)
    have hABC : (1 : ℝ) ≤ p.Le ^ 7 * 725 ^ 2 * (d : ℝ) ^ 2 := by
      calc
        (1 : ℝ) = (1 : ℝ) * (1 : ℝ) := by norm_num
        _ ≤ (p.Le ^ 7 * 725 ^ 2) * (d : ℝ) ^ 2 := mul_le_mul hAB hC (by positivity) (by positivity)
    have hABCD : (1 : ℝ) ≤ p.Le ^ 7 * 725 ^ 2 * (d : ℝ) ^ 2 * 2 := by
      calc
        (1 : ℝ) = (1 : ℝ) * (1 : ℝ) := by norm_num
        _ ≤ (p.Le ^ 7 * 725 ^ 2 * (d : ℝ) ^ 2) * 2 := mul_le_mul hABC hD (by positivity) (by positivity)
    simpa using calc
      (1 : ℝ) = (1 : ℝ) * (1 : ℝ) := by norm_num
      _ ≤ (p.Le ^ 7 * 725 ^ 2 * (d : ℝ) ^ 2 * 2) * 20 := mul_le_mul hABCD hE (by positivity) (by positivity)
  exact hprod

theorem row_r6b (p : Df2OPar) (d n : ℕ) (H : RowHyp p d n) :
    2 / df2C0 * p.eta * p.lam * d * p.Le ^ 2 / p.eps ≤ 1 := by
  have hdpos : 0 < (d : ℝ) := by
    have h : 1 ≤ (d : ℕ) := H.hd
    exact_mod_cast h
  have hnpos : 0 < (n : ℝ) := by
    have h : 1 ≤ (n : ℕ) := H.hn
    exact_mod_cast h
  have hLpos : 0 < p.Le := by linarith [H.L504]
  have heps_pos : 0 < p.eps := by
    rw [H.eps]
    positivity
  have hcalc : 2 / df2C0 * p.eta * p.lam * (d : ℝ) * p.Le ^ 2 / p.eps =
      1 / ((18 : ℝ) * 725 * 20 * 725 * (d : ℝ) * p.Le ^ 6) := by
    rw [H.lam, H.eta, H.eps, show df2C0 = (36 : ℝ) from rfl]
    have hsqrt_d_pos : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr hdpos
    have hsqrt_n_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnpos
    field_simp [hdpos.ne.symm, hnpos.ne.symm, hLpos.ne.symm,
      hsqrt_d_pos.ne.symm, hsqrt_n_pos.ne.symm]
    ring
  rw [hcalc]
  have h_denom_pos : 0 < (18 : ℝ) * 725 * 20 * 725 * (d : ℝ) * p.Le ^ 6 := by
    positivity
  apply (div_le_one h_denom_pos).mpr
  have hL_one : (1 : ℝ) ≤ p.Le := by linarith [H.L504]
  have hd' : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast H.hd
  have h_pow_one : (1 : ℝ) ≤ p.Le ^ 6 := one_le_pow₀ hL_one
  have h_const : (1 : ℝ) ≤ (18 : ℝ) * 725 * 20 * 725 := by norm_num
  nlinarith

theorem row_r7 (p : Df2OPar) (d n : ℕ) (H : RowHyp p d n) : p.Le ^ 3 / p.eps ^ 2 ≤ n := by
  have h_pow_ge_one {x : ℝ} (hx : 1 ≤ x) : ∀ n : ℕ, 1 ≤ x ^ n := by
    intro n
    induction' n with k ih
    · norm_num
    · rw [pow_succ]
      have hx_nonneg : 0 ≤ x := by linarith
      have h_pow_nonneg : 0 ≤ x ^ k := pow_nonneg hx_nonneg k
      calc
        (1 : ℝ) = 1 * 1 := by norm_num
        _ ≤ x ^ k * x := mul_le_mul ih hx (by linarith) h_pow_nonneg
  have hdpos' : (0 : ℝ) ≤ (d : ℝ) := by exact_mod_cast Nat.zero_le d
  have hnpos' : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
  have hsqrt_d_sq : Real.sqrt (d : ℝ) ^ 2 = (d : ℝ) := Real.sq_sqrt hdpos'
  have hsqrt_n_sq : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt hnpos'
  have hnpos'' : 0 < (n : ℝ) := by
    have hpos_nat : 0 < (n : ℕ) := Nat.lt_of_lt_of_le (by norm_num : 0 < 1) H.hn
    exact_mod_cast hpos_nat
  have hsqrt_n_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnpos''
  have hLpos : 0 < p.Le := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 504) H.L504
  have hdpos : 0 < (d : ℝ) := by
    have hpos_nat : 0 < (d : ℕ) := Nat.lt_of_lt_of_le (by norm_num : 0 < 1) H.hd
    exact_mod_cast hpos_nat
  have hcalc : p.Le ^ 3 / p.eps ^ 2 = (n : ℝ) / ((20 * 725) ^ 2 * (d : ℝ) ^ 3 * p.Le ^ 7) := by
    rw [H.eps]
    field_simp [hsqrt_n_pos.ne.symm]
    rw [hsqrt_d_sq, hsqrt_n_sq]
  rw [hcalc]
  refine div_le_self hnpos' ?_
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast H.hd
  have hL1 : (504 : ℝ) ≤ p.Le := H.L504
  have hL1' : (1 : ℝ) ≤ p.Le := by linarith
  have hL7 : (1 : ℝ) ≤ p.Le ^ 7 := h_pow_ge_one hL1' 7
  have hd3 : (1 : ℝ) ≤ (d : ℝ) ^ 3 := h_pow_ge_one hd1 3
  have hconst : (1 : ℝ) ≤ (20 * 725) ^ 2 := by norm_num
  have h_denom_ge_one : 1 ≤ (20 * 725) ^ 2 * (d : ℝ) ^ 3 * p.Le ^ 7 := by
    calc
      (1 : ℝ) = 1 * 1 * 1 := by norm_num
      _ ≤ (20 * 725) ^ 2 * (d : ℝ) ^ 3 * p.Le ^ 7 := by
        have h_first : 1 * 1 ≤ (20 * 725) ^ 2 * (d : ℝ) ^ 3 :=
          mul_le_mul hconst hd3 (by linarith) (by positivity)
        have h_second : (1 * 1) * 1 ≤ ((20 * 725) ^ 2 * (d : ℝ) ^ 3) * p.Le ^ 7 :=
          mul_le_mul h_first hL7 (by linarith) (by positivity)
        simpa [mul_assoc] using h_second
  simpa [mul_assoc, mul_comm, mul_left_comm] using h_denom_ge_one

theorem row_r8 (p : Df2OPar) (d n : ℕ) (H : RowHyp p d n) : (d : ℝ) ^ 2 * p.Le / p.eps ≤ Real.sqrt (d * n) := by
  have hd' : (0 : ℝ) ≤ d := by exact_mod_cast Nat.zero_le d
  have hn' : (0 : ℝ) ≤ n := by exact_mod_cast Nat.zero_le n
  have h_sqrt_mul : Real.sqrt ((d : ℝ) * (n : ℝ)) = Real.sqrt (d : ℝ) * Real.sqrt (n : ℝ) :=
    Real.sqrt_mul hd' (n : ℝ)
  rw [h_sqrt_mul, H.eps]
  set s := Real.sqrt (d : ℝ) with hs
  set t := Real.sqrt (n : ℝ) with ht
  set L := p.Le with hL
  have hd_eq_s_sq : (d : ℝ) = s ^ 2 := by
    rw [hs, Real.sq_sqrt hd']
  have hd_pos : 0 < (d : ℝ) := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast H.hd
    linarith
  have hs_pos : 0 < s := by
    rw [hs]
    exact Real.sqrt_pos.mpr hd_pos
  have ht_pos : 0 < t := by
    rw [ht]
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast H.hn
    exact Real.sqrt_pos.mpr (by linarith)
  have hL1 : 1 ≤ L := by
    rw [hL]
    linarith [H.L504]
  have hL_nonneg : 0 ≤ L := by linarith
  field_simp [ht_pos.ne.symm]
  rw [hd_eq_s_sq]
  have hL4 : 1 ≤ L ^ 4 := by
    have hL_sq : 1 ≤ L ^ 2 := by
      calc
        1 = 1 * 1 := by norm_num
        _ ≤ L * L := mul_le_mul hL1 hL1 (by linarith) (by linarith)
        _ = L ^ 2 := by ring
    calc
      1 = 1 * 1 := by norm_num
      _ ≤ L ^ 2 * L ^ 2 := mul_le_mul hL_sq hL_sq (by nlinarith) (by nlinarith)
      _ = L ^ 4 := by ring
  nlinarith

theorem row_r14 (p : Df2OPar) (d n : ℕ) (H : RowHyp p d n) : 1 / Real.sqrt n ≤ p.eps := by
  rw [H.eps]
  have hsqrtnpos : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  have hN : (1 : ℝ) ≤ 20 * 725 * ((d : ℝ) * Real.sqrt (d : ℝ)) * p.Le ^ 5 := by
    have hd' : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast H.hd
    have hsq : (1 : ℝ) ≤ Real.sqrt (d : ℝ) := by
      calc
        (1 : ℝ) = Real.sqrt ((1 : ℝ) ^ 2) := by norm_num
        _ ≤ Real.sqrt (d : ℝ) := Real.sqrt_le_sqrt (by nlinarith)
    have hLe : (504 : ℝ) ≤ p.Le := H.L504
    have hLe_one : (1 : ℝ) ≤ p.Le := by linarith
    have hLe_pos : 0 ≤ p.Le := by linarith
    have hLe5 : (1 : ℝ) ≤ p.Le ^ 5 := by
      have h1pos : (0 : ℝ) ≤ 1 := by norm_num
      calc
        (1 : ℝ) = (1 : ℝ) ^ 5 := by norm_num
        _ ≤ p.Le ^ 5 := pow_le_pow_left₀ h1pos hLe_one 5
    have hprod : (1 : ℝ) ≤ (d : ℝ) * Real.sqrt (d : ℝ) * p.Le ^ 5 := by
      have h1 : (1 : ℝ) ≤ (d : ℝ) * Real.sqrt (d : ℝ) := by
        nlinarith
      have h2 : (1 : ℝ) ≤ p.Le ^ 5 := hLe5
      nlinarith
    nlinarith
  exact div_le_div_of_nonneg_right hN hsqrtnpos

theorem row_c22 (p : Df2OPar) (d n : ℕ) (H : RowHyp p d n) : 22 * p.Le * p.δe / p.eps ^ 2 ≤ 1 := by
  rw [H.eps]
  have hdpos : (0 : ℝ) ≤ d := by exact_mod_cast Nat.zero_le d
  have hnpos : (0 : ℝ) ≤ n := by exact_mod_cast Nat.zero_le n
  have hLpos : 0 < p.Le := by
    have h504 : (504 : ℝ) ≤ p.Le := H.L504
    linarith
  have hdepos : 0 < p.δe := H.de_pos
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast H.hd
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast H.hn
  have hL1 : (1 : ℝ) ≤ p.Le := le_trans (by norm_num) H.L504
  field_simp
  rw [Real.sq_sqrt hnpos, Real.sq_sqrt hdpos]
  ring_nf
  -- Goal: p.δe * n * 22 ≤ p.Le ^ 9 * d ^ 2 * d * 210250000
  -- i.e., 22 * p.δe * n ≤ 14500^2 * d^3 * p.Le^9
  have h_dsmall : p.δe * ((d : ℝ) * (n : ℝ)) ^ 3 * (n : ℝ) ≤ Real.exp (-14) := H.dsmall
  -- Prove (d*n)^3 ≥ 1 using d ≥ 1, n ≥ 1
  have h_cube_ge_one : (1 : ℝ) ≤ ((d : ℝ) * (n : ℝ)) ^ 3 := by
    have h_prod : (1 : ℝ) ≤ (d : ℝ) * (n : ℝ) := by
      nlinarith
    have h_nonneg : 0 ≤ (d : ℝ) * (n : ℝ) := by positivity
    -- Since a ≥ 1 and a ≥ 0, a^3 ≥ 1^3 = 1
    -- Use: a^3 = a * a^2 ≥ 1 * 1^2 = 1
    have h_sq : (1 : ℝ) ≤ ((d : ℝ) * (n : ℝ)) ^ 2 := by
      nlinarith
    nlinarith
  -- From dsmall: p.δe * n ≤ p.δe * (d*n)^3 * n ≤ exp(-14)
  have h_deln_le_exp_neg14 : p.δe * (n : ℝ) ≤ Real.exp (-14) := by
    have h_mul : p.δe * (n : ℝ) ≤ p.δe * ((d : ℝ) * (n : ℝ)) ^ 3 * (n : ℝ) := by
      have h : (n : ℝ) ≤ ((d : ℝ) * (n : ℝ)) ^ 3 * (n : ℝ) := by
        calc
          (n : ℝ) = 1 * (n : ℝ) := by ring
          _ ≤ ((d : ℝ) * (n : ℝ)) ^ 3 * (n : ℝ) :=
            mul_le_mul_of_nonneg_right h_cube_ge_one hnpos
      nlinarith
    nlinarith
  -- exp(-14) ≤ 1 since -14 ≤ 0
  have h_exp_le_one : Real.exp (-14) ≤ 1 := by
    calc
      Real.exp (-14) ≤ Real.exp (0 : ℝ) := Real.exp_le_exp.mpr (by norm_num)
      _ = 1 := Real.exp_zero
  -- Now the main inequality: 22 * p.δe * n ≤ 14500^2 * d^3 * p.Le^9
  have h_main : (22 : ℝ) * p.δe * (n : ℝ) ≤ 14500 ^ 2 * (d : ℝ) ^ 3 * p.Le ^ 9 := by
    have h1 : (22 : ℝ) * p.δe * (n : ℝ) ≤ (22 : ℝ) * Real.exp (-14) := by
      nlinarith
    have h2 : (22 : ℝ) * Real.exp (-14) ≤ 22 := by
      nlinarith
    have h3 : (22 : ℝ) ≤ 14500 ^ 2 * (d : ℝ) ^ 3 * p.Le ^ 9 := by
      -- Since d ≥ 1, d^3 ≥ 1. Since p.Le ≥ 504 ≥ 1, p.Le^9 ≥ 1.
      -- So RHS ≥ 14500^2 * 1 * 1 = 210250000 > 22.
      have hd_cube : (1 : ℝ) ≤ (d : ℝ) ^ 3 := by
        have hd_sq : (1 : ℝ) ≤ (d : ℝ) ^ 2 := by nlinarith
        nlinarith
      have hL_pow : (1 : ℝ) ≤ p.Le ^ 9 := by
        have hL_sq : (1 : ℝ) ≤ p.Le ^ 2 := by nlinarith
        have hL_cu : (1 : ℝ) ≤ p.Le ^ 3 := by nlinarith
        have hL_4 : (1 : ℝ) ≤ p.Le ^ 4 := by nlinarith
        have hL_5 : (1 : ℝ) ≤ p.Le ^ 5 := by nlinarith
        have hL_6 : (1 : ℝ) ≤ p.Le ^ 6 := by nlinarith
        have hL_7 : (1 : ℝ) ≤ p.Le ^ 7 := by nlinarith
        have hL_8 : (1 : ℝ) ≤ p.Le ^ 8 := by nlinarith
        nlinarith
      nlinarith
    nlinarith
  -- Goal: p.δe * n * 22 ≤ p.Le ^ 9 * d ^ 3 * 210250000
  -- h_main: 22 * p.δe * n ≤ 14500 ^ 2 * d ^ 3 * p.Le ^ 9
  -- Note: 210250000 = 14500^2, and both sides are equal by commutativity
  simpa [mul_comm, mul_left_comm, mul_assoc, show (14500 : ℝ) ^ 2 = (210250000 : ℝ) by norm_num] using h_main

theorem row_c8 (p : Df2OPar) (d n : ℕ) (H : RowHyp p d n) : 8 * p.δe / p.eps ≤ 1 := by
  -- Extract basic facts from H
  have hd_pos : 0 < (d : ℝ) := by
    have : 1 ≤ (d : ℝ) := by exact_mod_cast H.hd
    linarith
  have hn_pos : 0 < (n : ℝ) := by
    have : 1 ≤ (n : ℝ) := by exact_mod_cast H.hn
    linarith
  have hd_ge_one : 1 ≤ (d : ℝ) := by exact_mod_cast H.hd
  have hn_ge_one : 1 ≤ (n : ℝ) := by exact_mod_cast H.hn
  have hL_pos : 0 < p.Le := by linarith [H.L504]
  have hL_ge_504 : 504 ≤ p.Le := H.L504
  have hde_pos : 0 < p.δe := H.de_pos
  have hs_pos : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr hd_pos
  have ht_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn_pos
  have hs_ge_one : 1 ≤ Real.sqrt (d : ℝ) := by
    calc
      1 = Real.sqrt (1 : ℝ) := by norm_num
      _ ≤ Real.sqrt (d : ℝ) := Real.sqrt_le_sqrt hd_ge_one
  have ht_nonneg : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  have hde_nonneg : 0 ≤ p.δe := by linarith

  -- Step 1: rewrite ε using H.eps
  have heps_eq : p.eps = (14500 : ℝ) * (d : ℝ) * Real.sqrt (d : ℝ) * p.Le ^ 5 / Real.sqrt (n : ℝ) := by
    rw [H.eps]
    ring
  rw [heps_eq]

  -- Goal: 8 * p.δe / ((14500 * d * √d * L⁵) / √n) ≤ 1

  -- Show denominator ≥ 1, so dividing by it reduces the value
  have h_denom_ge_one : 1 ≤ (14500 : ℝ) * (d : ℝ) * Real.sqrt (d : ℝ) * p.Le ^ 5 := by
    have h14500_ge_1 : 1 ≤ (14500 : ℝ) := by norm_num
    have hL5_ge_1 : 1 ≤ p.Le ^ 5 := by
      have hL_ge_1 : 1 ≤ p.Le := by linarith
      have h_gcongr : (1 : ℝ) ^ 5 ≤ p.Le ^ 5 := by gcongr
      simpa using h_gcongr
    have h_nonneg_14500 : 0 ≤ (14500 : ℝ) := by norm_num
    have h_nonneg_d : 0 ≤ (d : ℝ) := by linarith
    have h_nonneg_sqrt_d : 0 ≤ Real.sqrt (d : ℝ) := by linarith
    have h_nonneg_L5 : 0 ≤ p.Le ^ 5 := by positivity
    have h1 : 1 ≤ (14500 : ℝ) * (d : ℝ) := by
      calc
        1 = 1 * 1 := by norm_num
        _ ≤ (14500 : ℝ) * (d : ℝ) := mul_le_mul h14500_ge_1 hd_ge_one (by linarith) h_nonneg_14500
    have h2 : 1 ≤ (14500 : ℝ) * (d : ℝ) * Real.sqrt (d : ℝ) := by
      calc
        1 = 1 * 1 := by norm_num
        _ ≤ ((14500 : ℝ) * (d : ℝ)) * Real.sqrt (d : ℝ) :=
          mul_le_mul h1 hs_ge_one (by linarith) (by nlinarith)
    calc
      1 = 1 * 1 := by norm_num
      _ ≤ ((14500 : ℝ) * (d : ℝ) * Real.sqrt (d : ℝ)) * p.Le ^ 5 :=
        mul_le_mul h2 hL5_ge_1 (by linarith) (by nlinarith)

  have h_sqrtn_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn_pos
  have h_denom_pos : 0 < (14500 : ℝ) * (d : ℝ) * Real.sqrt (d : ℝ) * p.Le ^ 5 := by positivity

  -- Step 2: 8 * p.δe / (14500*d*√d*L⁵/√n) = 8 * p.δe * √n / (14500*d*√d*L⁵) ≤ 8 * p.δe * √n
  have h_step2 : 8 * p.δe / ((14500 : ℝ) * (d : ℝ) * Real.sqrt (d : ℝ) * p.Le ^ 5 / Real.sqrt (n : ℝ)) ≤
      8 * p.δe * Real.sqrt (n : ℝ) := by
    calc
      8 * p.δe / ((14500 : ℝ) * (d : ℝ) * Real.sqrt (d : ℝ) * p.Le ^ 5 / Real.sqrt (n : ℝ))
          = (8 * p.δe * Real.sqrt (n : ℝ)) / ((14500 : ℝ) * (d : ℝ) * Real.sqrt (d : ℝ) * p.Le ^ 5) := by
        field_simp [h_denom_pos.ne', h_sqrtn_pos.ne']
      _ ≤ (8 * p.δe * Real.sqrt (n : ℝ)) / 1 := by
        refine (div_le_div_of_nonneg_left ?_ (by norm_num : 0 < (1 : ℝ)) h_denom_ge_one)
        positivity
      _ = 8 * p.δe * Real.sqrt (n : ℝ) := by ring

  -- Step 3: √n ≤ n (since n ≥ 1)
  have h_sqrtn_le_n : Real.sqrt (n : ℝ) ≤ (n : ℝ) := by
    have h_n_sq_ge_n : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
      nlinarith
    have h_sqrt_n_sq : Real.sqrt ((n : ℝ) ^ 2) = (n : ℝ) := Real.sqrt_sq hn_pos.le
    calc
      Real.sqrt (n : ℝ) ≤ Real.sqrt ((n : ℝ) ^ 2) := Real.sqrt_le_sqrt h_n_sq_ge_n
      _ = (n : ℝ) := h_sqrt_n_sq

  -- Step 4: 8 * p.δe * √n ≤ 8 * p.δe * n
  have h_step4 : 8 * p.δe * Real.sqrt (n : ℝ) ≤ 8 * p.δe * (n : ℝ) := by
    nlinarith

  -- Step 5: p.δe * n ≤ exp(-14)
  have h_deln_le_exp : p.δe * (n : ℝ) ≤ Real.exp (-14) := by
    -- From H.dsmall: p.δe * ((d : ℝ) * n) ^ 3 * n ≤ exp(-14)
    have h_dn_ge_n : (d : ℝ) * (n : ℝ) ≥ (n : ℝ) := by
      nlinarith
    have hn_nonneg : 0 ≤ (n : ℝ) := by linarith
    have h_dn_cube_ge_n_cube : ((d : ℝ) * (n : ℝ)) ^ 3 ≥ (n : ℝ) ^ 3 := by
      gcongr
    have h_dsmall' : p.δe * ((n : ℝ) ^ 3 * (n : ℝ)) ≤ Real.exp (-14) := by
      have h_inner : (n : ℝ) ^ 3 * (n : ℝ) ≤ ((d : ℝ) * (n : ℝ)) ^ 3 * (n : ℝ) := by
        gcongr
      have h_mul : p.δe * ((n : ℝ) ^ 3 * (n : ℝ)) ≤ p.δe * (((d : ℝ) * (n : ℝ)) ^ 3 * (n : ℝ)) :=
        mul_le_mul_of_nonneg_left h_inner hde_nonneg
      have h_dsmall_eq : p.δe * (((d : ℝ) * (n : ℝ)) ^ 3 * (n : ℝ)) ≤ Real.exp (-14) := by
        simpa [mul_assoc] using H.dsmall
      linarith
    -- n^3 * n = n^4
    have h_n4 : (n : ℝ) ^ 3 * (n : ℝ) = (n : ℝ) ^ 4 := by ring
    rw [h_n4] at h_dsmall'
    -- Since n ≥ 1, n ≤ n^4
    have h_n_le_n4 : (n : ℝ) ≤ (n : ℝ) ^ 4 := by
      have h_n_sq_ge_n : (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
      have h_n4_ge_n2 : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 4 := by
        have h_n2_nonneg : 0 ≤ (n : ℝ) ^ 2 := by positivity
        nlinarith
      nlinarith
    have h_de_n_le_de_n4 : p.δe * (n : ℝ) ≤ p.δe * (n : ℝ) ^ 4 := by
      nlinarith
    nlinarith

  -- Step 6: 8 * p.δe * n ≤ 8 * exp(-14)
  have h_step6 : 8 * p.δe * (n : ℝ) ≤ 8 * Real.exp (-14) := by
    nlinarith

  -- Step 7: exp(-14) ≤ 1/8, so 8 * exp(-14) ≤ 1
  have h_exp_le_eighth : Real.exp (-14 : ℝ) ≤ 1/8 := by
    have h_exp_one_gt : 2.7182818283 < Real.exp (1 : ℝ) := Real.exp_one_gt_d9
    have h_exp_pow : Real.exp (1 : ℝ) ^ 14 = Real.exp (14 : ℝ) := by
      rw [← Real.exp_nat_mul, mul_comm]
      norm_num
    have h_base_gt : (8 : ℝ) < (2.7182818283 : ℝ) ^ 14 := by norm_num
    have h_exp_gt_8 : 8 < Real.exp (14 : ℝ) := by
      have h_pow_lt : (2.7182818283 : ℝ) ^ 14 < Real.exp (1 : ℝ) ^ 14 := by
        gcongr
      rw [h_exp_pow] at h_pow_lt
      linarith
    rw [Real.exp_neg (14 : ℝ)]
    -- Goal: (Real.exp 14)⁻¹ ≤ 1/8
    -- Using one_div_le_one_div
    have h_pos : 0 < Real.exp (14 : ℝ) := Real.exp_pos _
    have h8_pos : 0 < (8 : ℝ) := by norm_num
    have h_one_div : 1 / Real.exp (14 : ℝ) ≤ 1 / (8 : ℝ) :=
      (one_div_le_one_div h_pos h8_pos).mpr (by linarith)
    simpa [one_div] using h_one_div

  have h_step7 : 8 * Real.exp (-14) ≤ 1 := by
    nlinarith

  -- Chain everything together
  linarith

theorem row_c16 (p : Df2OPar) (d n : ℕ) (H : RowHyp p d n) :
    16 * p.eta * p.lam * n * Real.sqrt (d * p.δe) / p.eps ≤ 1 := by
  rcases H with ⟨hd, hn, de_pos, de_lt, Le, L504, cx, dsmall, lam, eta, sig2, rho, eps, eps_le, reg, kap, theta, alpha, c1, gam, k0, R, hlog⟩
  set L := p.Le with hL_def
  set s := Real.sqrt (d : ℝ) with hs_def
  set t := Real.sqrt (n : ℝ) with ht_def
  have hd0 : (0 : ℝ) ≤ d := by exact mod_cast (Nat.zero_le _)
  have hn0 : (0 : ℝ) ≤ n := by exact mod_cast (Nat.zero_le _)
  have hd_pos : 0 < (d : ℝ) := by
    exact mod_cast (Nat.one_pos.trans_le hd)
  have hn_pos : 0 < (n : ℝ) := by
    exact mod_cast (Nat.one_pos.trans_le hn)
  have hs_pos : 0 < s := Real.sqrt_pos.mpr hd_pos
  have ht_pos : 0 < t := Real.sqrt_pos.mpr hn_pos
  have hs_sq : s ^ 2 = (d : ℝ) := Real.sq_sqrt hd0
  have ht_sq : t ^ 2 = (n : ℝ) := Real.sq_sqrt hn0
  have hL_pos : 0 < L := by
    have : (0 : ℝ) < 504 := by norm_num
    linarith
  have hde0 : 0 ≤ p.δe := le_of_lt de_pos
  rw [lam, eta, eps]
  have h_sqrt_de : Real.sqrt ((d : ℝ) * p.δe) = s * Real.sqrt (p.δe) := by
    calc
      Real.sqrt ((d : ℝ) * p.δe) = Real.sqrt ((d : ℝ)) * Real.sqrt (p.δe) := Real.sqrt_mul hd0 _
      _ = s * Real.sqrt (p.δe) := by rw [hs_def]
  rw [h_sqrt_de]
  rw [← hs_sq, ← ht_sq]
  field_simp [hL_pos.ne.symm, hs_pos.ne.symm, ht_pos.ne.symm]
  -- Goal: 16 * t ^ 2 * √p.δe ≤ s ^ 3 * L ^ 8 * 725 ^ 2 * 20
  have hs_ge_one : 1 ≤ s := by
    calc
      1 = Real.sqrt (1 : ℝ) := by norm_num
      _ ≤ Real.sqrt (d : ℝ) := Real.sqrt_le_sqrt (by exact mod_cast hd)
      _ = s := by rw [hs_def]
  have ht_ge_one : 1 ≤ t := by
    calc
      1 = Real.sqrt (1 : ℝ) := by norm_num
      _ ≤ Real.sqrt (n : ℝ) := Real.sqrt_le_sqrt (by exact mod_cast hn)
      _ = t := by rw [ht_def]
  rw [← hs_sq, ← ht_sq] at dsmall
  -- dsmall: p.δe * (s^2 * t^2)^3 * t^2 ≤ Real.exp (-14)
  have h_dsmall_bound : p.δe * t^8 ≤ 1 := by
    have h_exp_le_one : Real.exp (-14) ≤ 1 := by
      calc
        Real.exp (-14) ≤ Real.exp (0 : ℝ) := Real.exp_le_exp.mpr (by norm_num)
        _ = 1 := Real.exp_zero
    -- Expand p.δe * (s^2 * t^2)^3 * t^2 = p.δe * s^6 * t^8
    have h_expand : p.δe * (s ^ 2 * t ^ 2) ^ 3 * t ^ 2 = p.δe * s ^ 6 * t ^ 8 := by ring
    rw [h_expand] at dsmall
    -- dsmall: p.δe * s^6 * t^8 ≤ Real.exp (-14)
    -- Since s ≥ 1, we have s^6 ≥ 1. Prove by repeated mul_le_mul.
    have hs6_ge_one : 1 ≤ s^6 := by
      -- s ≥ 1 → s^2 ≥ 1 → s^3 ≥ 1 → s^6 ≥ 1
      have hs_sq_ge_one : 1 ≤ s^2 := by
        have : 1*1 ≤ s*s := mul_le_mul hs_ge_one hs_ge_one (by positivity) (by positivity)
        linarith
      have hs_cu_ge_one : 1 ≤ s^3 := by
        have : 1*1*1 ≤ s*s*s := by
          -- 1*1 ≤ s*s, and multiply by 1 ≤ s again
          have h1 : 1*1 ≤ s*s := mul_le_mul hs_ge_one hs_ge_one (by positivity) (by positivity)
          have h2 : 1*1*1 ≤ s*s*s := mul_le_mul h1 hs_ge_one (by positivity) (by positivity)
          exact h2
        -- s*s*s = s^3
        simpa [pow_succ, pow_one, mul_comm, mul_left_comm, mul_assoc] using this
      -- Now s^6 = (s^3)^2 ≥ 1^2 = 1
      have h_sq : 1*1 ≤ s^3 * s^3 := mul_le_mul hs_cu_ge_one hs_cu_ge_one (by positivity) (by positivity)
      -- s^3 * s^3 = s^6
      simpa [mul_comm, mul_left_comm, mul_assoc, pow_succ, pow_one] using h_sq
    have h_nonneg : 0 ≤ p.δe * t^8 := by positivity
    have h_ineq : p.δe * t^8 ≤ p.δe * s^6 * t^8 := by
      calc
        p.δe * t^8 = p.δe * t^8 * 1 := by ring
        _ ≤ p.δe * t^8 * s^6 := mul_le_mul_of_nonneg_left hs6_ge_one h_nonneg
        _ = p.δe * s^6 * t^8 := by ring
    linarith
  have h_sqrt_bound : t^2 * Real.sqrt (p.δe) ≤ 1 := by
    -- First prove t^4 ≥ 1 from t ≥ 1
    have ht4_ge_one : 1 ≤ t^4 := by
      have ht_sq_ge_one : 1 ≤ t^2 := by
        have : 1*1 ≤ t*t := mul_le_mul ht_ge_one ht_ge_one (by positivity) (by positivity)
        linarith
      -- t^4 = (t^2)^2 ≥ 1^2 = 1
      have h_sq : 1*1 ≤ t^2 * t^2 := mul_le_mul ht_sq_ge_one ht_sq_ge_one (by positivity) (by positivity)
      simpa [pow_succ, pow_one, mul_comm, mul_left_comm, mul_assoc] using h_sq
    -- Now t^4 ≤ t^8 since t^4 ≥ 1
    have ht4_le_t8 : t^4 ≤ t^8 := by
      calc
        t^4 = t^4 * 1 := by ring
        _ ≤ t^4 * t^4 := mul_le_mul_of_nonneg_left ht4_ge_one (by positivity)
        _ = t^8 := by ring
    have h_temp : p.δe * t^4 ≤ 1 := by
      have h_mul : p.δe * t^4 ≤ p.δe * t^8 :=
        mul_le_mul_of_nonneg_left ht4_le_t8 hde0
      linarith
    have h_sq : (t^2 * Real.sqrt (p.δe))^2 ≤ 1 := by
      calc
        (t^2 * Real.sqrt (p.δe))^2 = t^4 * (Real.sqrt (p.δe))^2 := by ring
        _ = t^4 * p.δe := by rw [Real.sq_sqrt hde0]
        _ = p.δe * t^4 := mul_comm _ _
        _ ≤ 1 := h_temp
    have h_nonneg : 0 ≤ t^2 * Real.sqrt (p.δe) := by positivity
    -- From x ≥ 0 and x^2 ≤ 1, deduce x ≤ 1 using abs_le_of_sq_le_sq
    have h_sq' : (t^2 * Real.sqrt (p.δe))^2 ≤ (1 : ℝ)^2 := by simpa using h_sq
    have h_one_nonneg : 0 ≤ (1 : ℝ) := by norm_num
    have h_abs : |t^2 * Real.sqrt (p.δe)| ≤ 1 := abs_le_of_sq_le_sq h_sq' h_one_nonneg
    exact (abs_le.mp h_abs).right
  have h_main : 16 * t^2 * Real.sqrt (p.δe) ≤ s^3 * L^8 * 725^2 * 20 := by
    have h_lhs : 16 * t^2 * Real.sqrt (p.δe) ≤ 16 := by
      linarith
    have h_rhs : (16 : ℝ) ≤ s^3 * L^8 * 725^2 * 20 := by
      have hL_ge_504 : (504 : ℝ) ≤ L := by exact mod_cast L504
      -- Prove s^3 ≥ 1 from s ≥ 1
      have h_s3 : 1 ≤ s^3 := by
        have hs_sq_ge_one : 1 ≤ s^2 := by
          have : 1*1 ≤ s*s := mul_le_mul hs_ge_one hs_ge_one (by positivity) (by positivity)
          linarith
        have h_mul : 1*1*1 ≤ s*s*s := by
          have h1 : 1*1 ≤ s*s := mul_le_mul hs_ge_one hs_ge_one (by positivity) (by positivity)
          have h2 : 1*1*1 ≤ s*s*s := mul_le_mul h1 hs_ge_one (by positivity) (by positivity)
          exact h2
        simpa [pow_succ, pow_one, mul_comm, mul_left_comm, mul_assoc] using h_mul
      -- Prove 504^8 ≤ L^8 from 504 ≤ L
      have h_L8 : (504 : ℝ)^8 ≤ L^8 := by
        -- Use repeated mul_le_mul
        have h504_nonneg : 0 ≤ (504 : ℝ) := by norm_num
        have hL_nonneg : 0 ≤ L := hL_pos.le
        -- 504^8 ≤ L^8: prove by squaring repeatedly
        -- 504^2 ≤ L^2, then (504^2)^2 ≤ (L^2)^2, etc.
        have h_sq : (504 : ℝ)^2 ≤ L^2 := by
          have : (504 : ℝ)*504 ≤ L*L := mul_le_mul hL_ge_504 hL_ge_504 h504_nonneg hL_nonneg
          linarith
        have h_sq4 : ((504 : ℝ)^2)^2 ≤ (L^2)^2 := by
          have : (504^2)*(504^2) ≤ (L^2)*(L^2) := mul_le_mul h_sq h_sq (by positivity) (by positivity)
          linarith
        -- (504^2)^2 = 504^4, (L^2)^2 = L^4
        have h4 : (504 : ℝ)^4 ≤ L^4 := by
          simpa [pow_succ, pow_one, mul_comm, mul_left_comm, mul_assoc] using h_sq4
        -- Now square again to get 504^8 ≤ L^8
        have h_sq8 : ((504 : ℝ)^4)^2 ≤ (L^4)^2 := by
          have : (504^4)*(504^4) ≤ (L^4)*(L^4) := mul_le_mul h4 h4 (by positivity) (by positivity)
          linarith
        simpa [pow_succ, pow_one, mul_comm, mul_left_comm, mul_assoc] using h_sq8
      have h_num : (16 : ℝ) ≤ 725^2 * 20 * 504^8 := by norm_num
      have h_mid : (16 : ℝ) ≤ 725^2 * 20 * L^8 := by
        have h_pos : 0 ≤ (725 : ℝ)^2 * 20 := by norm_num
        calc
          (16 : ℝ) ≤ (725 : ℝ)^2 * 20 * (504 : ℝ)^8 := h_num
          _ ≤ (725 : ℝ)^2 * 20 * L^8 := mul_le_mul_of_nonneg_left h_L8 h_pos
      have h_final : 725^2 * 20 * L^8 ≤ 725^2 * 20 * L^8 * s^3 := by
        have h_pos' : 0 ≤ 725^2 * 20 * L^8 := by positivity
        calc
          725^2 * 20 * L^8 = (725^2 * 20 * L^8) * 1 := by ring
          _ ≤ (725^2 * 20 * L^8) * s^3 := mul_le_mul_of_nonneg_left h_s3 h_pos'
      linarith
    linarith
  exact h_main

theorem row_c4 (p : Df2OPar) (d n : ℕ) (H : RowHyp p d n) : 4 * p.δe / p.sig2 ≤ 1 := by
  rcases H with ⟨hd, hn, de_pos, de_lt, Le, L504, cx, dsmall, lam, eta, sig2, rho, eps, eps_le, reg, kap, theta, alpha, c1, gam, k0, R, hlog⟩
  have hLe_pos : 0 < p.Le := by linarith
  have hd_one : 1 ≤ (d : ℝ) := by exact_mod_cast hd
  have hn_one : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hn_nonneg : 0 ≤ (n : ℝ) := by exact mod_cast (Nat.zero_le n)
  have h_sqrt_d_ge_one : 1 ≤ Real.sqrt (d : ℝ) := by
    have h := Real.sqrt_le_sqrt hd_one
    rw [Real.sqrt_one] at h
    exact h
  have hd_mul_sqrt_ge_one : 1 ≤ (d : ℝ) * Real.sqrt (d : ℝ) := by
    have h := mul_le_mul hd_one h_sqrt_d_ge_one (by norm_num) (by linarith)
    simpa [one_mul] using h
  have hLe5_le_sqrt_n : p.Le ^ 5 ≤ Real.sqrt (n : ℝ) := by
    have h_nonneg : 0 ≤ p.Le ^ 5 := pow_nonneg (by linarith) 5
    have h_mul : 29000 * p.Le ^ 5 ≤ 29000 * ((d : ℝ) * Real.sqrt (d : ℝ)) * p.Le ^ 5 := by
      have h := mul_le_mul_of_nonneg_right hd_mul_sqrt_ge_one h_nonneg
      have h2 := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ (29000 : ℝ))
      simpa [mul_comm, mul_left_comm, mul_assoc] using h2
    linarith
  have hLe_ge_one : 1 ≤ p.Le := by linarith
  have hLe_le_hLe5 : p.Le ≤ p.Le ^ 5 := by
    have hx4_ge_one : 1 ≤ p.Le ^ 4 := by
      have h := pow_le_pow_left₀ (by linarith) hLe_ge_one 4
      rw [one_pow] at h
      exact h
    calc
      p.Le = p.Le * 1 := by ring
      _ ≤ p.Le * (p.Le ^ 4) := mul_le_mul_of_nonneg_left hx4_ge_one (by linarith)
      _ = p.Le ^ 5 := by ring
  have h_sqrt_n_le_n : Real.sqrt (n : ℝ) ≤ (n : ℝ) := by
    have hn_sq_ge_n : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
      calc
        (n : ℝ) = (n : ℝ) * 1 := by ring
        _ ≤ (n : ℝ) * (n : ℝ) := mul_le_mul_of_nonneg_left hn_one hn_nonneg
        _ = (n : ℝ) ^ 2 := by ring
    calc
      Real.sqrt (n : ℝ) ≤ Real.sqrt ((n : ℝ) ^ 2) := Real.sqrt_le_sqrt hn_sq_ge_n
      _ = (n : ℝ) := Real.sqrt_sq hn_nonneg
  have hLe_le_n : p.Le ≤ (n : ℝ) := by
    linarith
  have h_dn_ge_n : (n : ℝ) ≤ (d : ℝ) * (n : ℝ) := by
    calc
      (n : ℝ) = 1 * (n : ℝ) := by ring
      _ ≤ (d : ℝ) * (n : ℝ) := mul_le_mul_of_nonneg_right hd_one hn_nonneg
  have h_cube : (n : ℝ) ^ 3 ≤ ((d : ℝ) * (n : ℝ)) ^ 3 :=
    pow_le_pow_left₀ hn_nonneg h_dn_ge_n 3
  have h3 : p.δe * (n : ℝ) ^ 4 ≤ Real.exp (-14) := by
    have h_nonneg_de : 0 ≤ p.δe := by linarith
    have h_n3_nonneg : 0 ≤ (n : ℝ) ^ 3 := pow_nonneg hn_nonneg 3
    have h_mul_n : (n : ℝ) ^ 3 * (n : ℝ) ≤ ((d : ℝ) * (n : ℝ)) ^ 3 * (n : ℝ) :=
      mul_le_mul_of_nonneg_right h_cube hn_nonneg
    have h_mul_de : p.δe * ((n : ℝ) ^ 3 * (n : ℝ)) ≤ p.δe * (((d : ℝ) * (n : ℝ)) ^ 3 * (n : ℝ)) :=
      mul_le_mul_of_nonneg_left h_mul_n h_nonneg_de
    have h_simp : p.δe * ((n : ℝ) ^ 3 * (n : ℝ)) = p.δe * (n : ℝ) ^ 4 := by ring
    have h_simp2 : p.δe * (((d : ℝ) * (n : ℝ)) ^ 3 * (n : ℝ)) = p.δe * ((d : ℝ) * (n : ℝ)) ^ 3 * (n : ℝ) := by ring
    rw [h_simp, h_simp2] at h_mul_de
    linarith
  have h4 : p.δe * (n : ℝ) ≤ Real.exp (-14) := by
    have hn4_ge_n : (n : ℝ) ≤ (n : ℝ) ^ 4 := by
      have hn3_ge_one : 1 ≤ (n : ℝ) ^ 3 := by
        have h := pow_le_pow_left₀ (by norm_num : 0 ≤ (1 : ℝ)) hn_one 3
        rw [one_pow] at h
        exact h
      calc
        (n : ℝ) = (n : ℝ) * 1 := by ring
        _ ≤ (n : ℝ) * ((n : ℝ) ^ 3) := mul_le_mul_of_nonneg_left hn3_ge_one hn_nonneg
        _ = (n : ℝ) ^ 4 := by ring
    have h_nonneg_de : 0 ≤ p.δe := by linarith
    have h_mul : p.δe * (n : ℝ) ≤ p.δe * (n : ℝ) ^ 4 :=
      mul_le_mul_of_nonneg_left hn4_ge_n h_nonneg_de
    linarith
  have h_exp14_ge_32 : 32 ≤ Real.exp 14 := by
    have h7 : (8 : ℝ) ≤ Real.exp 7 := by
      have := Real.add_one_le_exp (7 : ℝ)
      linarith
    have h_exp14_eq : Real.exp 14 = (Real.exp 7) ^ 2 := by
      calc
        Real.exp 14 = Real.exp ((7 : ℝ) + (7 : ℝ)) := by norm_num
        _ = Real.exp 7 * Real.exp 7 := by rw [Real.exp_add]
        _ = (Real.exp 7) ^ 2 := by ring
    rw [h_exp14_eq]
    nlinarith
  have h32_exp_neg14_le_1 : 32 * Real.exp (-14) ≤ 1 := by
    rw [Real.exp_neg (14 : ℝ)]
    have hpos : 0 < Real.exp 14 := Real.exp_pos 14
    field_simp [hpos.ne']
    nlinarith
  have h_main : 32 * p.δe * (n : ℝ) ≤ 1 := by
    have h_nonneg_32_de : 0 ≤ 32 * p.δe := mul_nonneg (by norm_num) (by linarith)
    have h_mul : 32 * p.δe * (n : ℝ) ≤ 32 * Real.exp (-14) := by
      have h := mul_le_mul_of_nonneg_left h4 (by norm_num : 0 ≤ (32 : ℝ))
      simpa [mul_comm, mul_left_comm, mul_assoc] using h
    linarith
  calc
    4 * p.δe / p.sig2 = 4 * p.δe / (1 / (8 * p.Le)) := by rw [sig2]
    _ = 4 * p.δe * (8 * p.Le) := by field_simp [hLe_pos.ne']
    _ = 32 * p.δe * p.Le := by ring
    _ ≤ 32 * p.δe * (n : ℝ) :=
      mul_le_mul_of_nonneg_left hLe_le_n (mul_nonneg (by norm_num) (by linarith))
    _ ≤ 1 := h_main

theorem row_cnu_aux (L de lam d n : ℝ) (hd1 : 1 ≤ d) (hn1 : 1 ≤ n) (hde : 0 < de) (hL : 504 ≤ L)
    (dsmall : de * (d * n) ^ 3 * n ≤ Real.exp (-14))
    (hlam : lam = 1 / (725 * d * L ^ 2))
    (reg : 29000 * (d * Real.sqrt d) * L ^ 5 ≤ Real.sqrt n) : n * de / lam ^ 2 ≤ 1 := by
  have hs1 : 1 ≤ Real.sqrt d := Real.one_le_sqrt.mpr hd1
  have hn0 : 0 ≤ n := by linarith
  have ht : Real.sqrt n ≤ n := by
    have h := Real.sq_sqrt hn0
    have h1 : 1 ≤ Real.sqrt n := Real.one_le_sqrt.mpr hn1
    nlinarith
  have hL5 : 29000 * L ^ 5 ≤ Real.sqrt n := by
    have : 1 ≤ d * Real.sqrt d := by nlinarith
    have hp : 0 ≤ 29000 * L ^ 5 := by positivity
    nlinarith
  have hL4 : L ^ 4 ≤ n / 29000 := by
    have : L ^ 4 ≤ L ^ 5 := by
      have : (0:ℝ) ≤ L ^ 4 := by positivity
      nlinarith [pow_succ L 4]
    linarith
  have hexp : Real.exp (-14) ≤ 1 / 2187 := by
    have h2 : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
    have h14 : Real.exp 14 = Real.exp 2 ^ 7 := by rw [← Real.exp_nat_mul]; norm_num
    have h3 : (2187 : ℝ) ≤ Real.exp 14 := by
      rw [h14]; calc (2187 : ℝ) = 3 ^ 7 := by norm_num
        _ ≤ Real.exp 2 ^ 7 := pow_le_pow_left₀ (by norm_num) h2 7
    rw [Real.exp_neg]
    rw [inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) h3
  have hdn : d ^ 2 * n ^ 2 * de ≤ 1 / 2187 := by
    have h1 : d ^ 2 * n ^ 2 ≤ (d * n) ^ 3 * n := by
      have h2 : 1 ≤ d * n ^ 2 := by nlinarith
      have h0 : 0 ≤ d ^ 2 * n ^ 2 := by positivity
      calc d ^ 2 * n ^ 2 ≤ d ^ 2 * n ^ 2 * (d * n ^ 2) := le_mul_of_one_le_right h0 h2
        _ = (d * n) ^ 3 * n := by ring
    calc d ^ 2 * n ^ 2 * de ≤ (d * n) ^ 3 * n * de := mul_le_mul_of_nonneg_right h1 hde.le
      _ = de * (d * n) ^ 3 * n := by ring
      _ ≤ _ := dsmall.trans hexp
  have key : n * de / lam ^ 2 = 725 ^ 2 * (d ^ 2 * L ^ 4) * (n * de) := by
    rw [hlam]
    have : (0 : ℝ) < 725 * d * L ^ 2 := by positivity
    field_simp
  rw [key]
  have hA : 0 ≤ d ^ 2 * (n * de) := by positivity
  calc 725 ^ 2 * (d ^ 2 * L ^ 4) * (n * de) = 725 ^ 2 * (L ^ 4 * (d ^ 2 * (n * de))) := by ring
    _ ≤ 725 ^ 2 * (n / 29000 * (d ^ 2 * (n * de))) := by gcongr
    _ = 725 ^ 2 / 29000 * (d ^ 2 * n ^ 2 * de) := by ring
    _ ≤ 725 ^ 2 / 29000 * (1 / 2187) := by gcongr
    _ ≤ 1 := by norm_num

theorem row_cnu (p : Df2OPar) (d n : ℕ) (H : RowHyp p d n) : n * p.δe / p.lam ^ 2 ≤ 1 := by
  exact row_cnu_aux p.Le p.δe p.lam d n (by exact_mod_cast H.hd) (by exact_mod_cast H.hn) H.de_pos H.L504 H.dsmall
    H.lam H.reg

theorem row_c2dl (p : Df2OPar) (d n : ℕ) (H : RowHyp p d n) : 2 * p.δe * d * n / p.lam ≤ 1 := by
  have hL1 : (1 : ℝ) ≤ p.Le := by
    have : (504 : ℝ) ≤ p.Le := by exact_mod_cast H.L504
    linarith
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast H.hd
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast H.hn
  have hn_nonneg : 0 ≤ (n : ℝ) := by linarith
  have hde_pos : 0 ≤ p.δe := by linarith [H.de_pos]
  have hLe_sq_le_n_div_29000 : p.Le ^ 2 ≤ (n : ℝ) / 29000 := by
    have hreg' : 29000 * p.Le ^ 5 ≤ Real.sqrt (n : ℝ) := by
      have h := H.reg
      have h_one_le : (1 : ℝ) ≤ (d : ℝ) * Real.sqrt (d : ℝ) := by
        have hs1 : (1 : ℝ) ≤ Real.sqrt (d : ℝ) := by
          calc
            (1 : ℝ) = Real.sqrt (1 : ℝ) := by norm_num
            _ ≤ Real.sqrt (d : ℝ) := Real.sqrt_le_sqrt hd1
        nlinarith
      have h_mul : 29000 * (1 : ℝ) * p.Le ^ 5 ≤ 29000 * ((d : ℝ) * Real.sqrt (d : ℝ)) * p.Le ^ 5 := by
        have hpos : 0 ≤ 29000 * p.Le ^ 5 := by positivity
        nlinarith
      calc
        29000 * p.Le ^ 5 = 29000 * (1 : ℝ) * p.Le ^ 5 := by ring
        _ ≤ 29000 * ((d : ℝ) * Real.sqrt (d : ℝ)) * p.Le ^ 5 := h_mul
        _ ≤ Real.sqrt (n : ℝ) := h
    have hLe_sq_le_Le5 : p.Le ^ 2 ≤ p.Le ^ 5 := by
      have hLe_nonneg : 0 ≤ p.Le := by linarith
      have hLe3 : (1 : ℝ) ≤ p.Le ^ 3 := by
        have hsq : (1 : ℝ) ≤ p.Le ^ 2 := by
          calc
            (1 : ℝ) = 1 * 1 := by norm_num
            _ ≤ p.Le * p.Le := mul_le_mul hL1 hL1 (by linarith) (by linarith)
            _ = p.Le ^ 2 := by ring
        calc
          (1 : ℝ) = 1 * 1 := by norm_num
          _ ≤ p.Le ^ 2 * p.Le := mul_le_mul hsq hL1 (by linarith) (by linarith [hsq])
          _ = p.Le ^ 3 := by ring
      nlinarith
    have hsqrt_n_le_n : Real.sqrt (n : ℝ) ≤ (n : ℝ) := by
      have hsq : (Real.sqrt (n : ℝ)) ^ 2 = (n : ℝ) := Real.sq_sqrt hn_nonneg
      by_contra! hgt
      have hsq_gt : (Real.sqrt (n : ℝ)) ^ 2 > (n : ℝ) ^ 2 := by nlinarith
      rw [hsq] at hsq_gt
      nlinarith
    calc
      p.Le ^ 2 ≤ p.Le ^ 5 := hLe_sq_le_Le5
      _ ≤ Real.sqrt (n : ℝ) / 29000 := by linarith
      _ ≤ (n : ℝ) / 29000 := by linarith
  have hfactor_bound : (1450 : ℝ) / 29000 ≤ (d : ℝ) * (n : ℝ) ^ 2 := by
    have h_one_le_dnsq : (1 : ℝ) ≤ (d : ℝ) * (n : ℝ) ^ 2 := by
      have hn_sq_ge_1 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
      nlinarith
    nlinarith
  have h_dsmall' : p.δe * ((d : ℝ) ^ 3) * ((n : ℝ) ^ 4) ≤ Real.exp (-14) := by
    have h := H.dsmall
    have h_eq : p.δe * (((d : ℝ) * (n : ℝ)) ^ 3) * (n : ℝ) = p.δe * ((d : ℝ) ^ 3) * ((n : ℝ) ^ 4) := by ring
    rw [h_eq] at h
    exact h
  have hexp_le_one : Real.exp (-14) ≤ 1 := by
    have : -14 ≤ (0 : ℝ) := by norm_num
    have h := Real.exp_le_exp.mpr this
    rw [Real.exp_zero] at h
    exact h
  calc
    2 * p.δe * (d : ℝ) * (n : ℝ) / p.lam
        = 1450 * p.δe * ((d : ℝ) ^ 2) * (n : ℝ) * (p.Le ^ 2) := by
          rw [H.lam]
          field_simp
          ring
    _ ≤ 1450 * p.δe * ((d : ℝ) ^ 2) * (n : ℝ) * ((n : ℝ) / 29000) := by
      have hpos : 0 ≤ 1450 * p.δe * ((d : ℝ) ^ 2) * (n : ℝ) := by positivity
      nlinarith
    _ = ((1450 : ℝ) / 29000) * p.δe * ((d : ℝ) ^ 2) * ((n : ℝ) ^ 2) := by ring
    _ ≤ p.δe * ((d : ℝ) ^ 3) * ((n : ℝ) ^ 4) := by
      have hpos_prod : 0 ≤ p.δe * ((d : ℝ) ^ 2) * ((n : ℝ) ^ 2) := by positivity
      have h_ineq' : (1450 : ℝ) ≤ 29000 * ((d : ℝ) * ((n : ℝ) ^ 2)) := by
        linarith [hfactor_bound]
      nlinarith
    _ ≤ Real.exp (-14) := h_dsmall'
    _ ≤ 1 := hexp_le_one

theorem row_c500 (p : Df2OPar) (d n : ℕ) (H : RowHyp p d n) :
    500 * p.δe * (n : ℝ) ^ ((3 : ℝ) / 2) * d * p.Le ^ 2 ≤ 1 := by
  have hd' : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast H.hd
  have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast H.hn
  have hd_pos : 0 ≤ (d : ℝ) := by linarith
  have hn_pos : 0 ≤ (n : ℝ) := by linarith
  have hn_pos' : 0 < (n : ℝ) := by linarith
  have hde_pos : 0 < p.δe := H.de_pos
  have hL_ge_504 : 504 ≤ p.Le := H.L504
  -- rewrite (n : ℝ) ^ ((3 : ℝ) / 2) = n * √n
  have hn_pow_eq : (n : ℝ) ^ ((3 : ℝ) / 2) = (n : ℝ) * Real.sqrt (n : ℝ) := by
    calc
      (n : ℝ) ^ ((3 : ℝ) / 2) = (n : ℝ) ^ ((1 : ℝ) + (1/2 : ℝ)) := by ring_nf
      _ = (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (1/2 : ℝ) := by rw [Real.rpow_add hn_pos' (1 : ℝ) (1/2 : ℝ)]
      _ = (n : ℝ) * Real.sqrt (n : ℝ) := by rw [Real.rpow_one, Real.sqrt_eq_rpow]
  rw [hn_pow_eq]
  set s := Real.sqrt (d : ℝ) with hs_def
  set t := Real.sqrt (n : ℝ) with ht_def
  set L := p.Le with hL_def
  have hs_sq : s ^ 2 = (d : ℝ) := Real.sq_sqrt hd_pos
  have ht_sq : t ^ 2 = (n : ℝ) := Real.sq_sqrt hn_pos
  have hs_nonneg : 0 ≤ s := Real.sqrt_nonneg _
  have ht_nonneg : 0 ≤ t := Real.sqrt_nonneg _
  have hL_nonneg : 0 ≤ L := by linarith
  -- H.reg: 29000 * (d * Real.sqrt d) * p.Le ^ 5 ≤ Real.sqrt n
  have hreg : 29000 * (d : ℝ) * s * L ^ 5 ≤ t := by
    simpa [hs_def, ht_def, hL_def, mul_assoc] using H.reg
  have hs_ge_one : 1 ≤ s := by
    calc
      1 = Real.sqrt (1 : ℝ) := by norm_num
      _ ≤ Real.sqrt (d : ℝ) := Real.sqrt_le_sqrt hd'
      _ = s := rfl
  have hL_ge_one : 1 ≤ L := by linarith
  -- From hreg: 29000 * d * s * L^5 ≤ t, and d ≥ 1, s ≥ 1, L^5 ≥ 0
  -- So 29000 * L^5 ≤ t
  have hL5_le_t_div_29000 : L ^ 5 ≤ t / 29000 := by
    have htemp : 29000 * L ^ 5 ≤ t := by
      -- From hreg: 29000 * d * s * L^5 ≤ t
      -- Since d ≥ 1, s ≥ 1, L^5 ≥ 0, we have 29000 * 1 * 1 * L^5 ≤ 29000 * d * s * L^5
      have hL5_nonneg : 0 ≤ L ^ 5 := pow_nonneg hL_nonneg 5
      have h_one_one_le_d_s : (1 : ℝ) * (1 : ℝ) ≤ (d : ℝ) * s := by
        nlinarith
      have hineq : (1 : ℝ) * (1 : ℝ) * L ^ 5 ≤ (d : ℝ) * s * L ^ 5 := by
        nlinarith
      -- Multiply both sides by 29000
      have htemp2 : 29000 * ((1 : ℝ) * (1 : ℝ) * L ^ 5) ≤ 29000 * ((d : ℝ) * s * L ^ 5) := by
        nlinarith
      -- Simplify both sides
      have hleft : 29000 * ((1 : ℝ) * (1 : ℝ) * L ^ 5) = 29000 * L ^ 5 := by ring
      have hright : 29000 * ((d : ℝ) * s * L ^ 5) = 29000 * (d : ℝ) * s * L ^ 5 := by ring
      rw [hleft, hright] at htemp2
      linarith
    linarith
  -- Since L ≥ 1, L² ≤ L⁵
  have hL2_le_L5 : L ^ 2 ≤ L ^ 5 := by
    have hL3_ge_one : 1 ≤ L ^ 3 := by
      have hL_sq_ge_L : L ≤ L ^ 2 := by
        calc
          L = L * 1 := by ring
          _ ≤ L * L := mul_le_mul_of_nonneg_left hL_ge_one hL_nonneg
          _ = L ^ 2 := by ring
      have hL_cu_ge_L_sq : L ^ 2 ≤ L ^ 3 := by
        calc
          L ^ 2 = L ^ 2 * 1 := by ring
          _ ≤ L ^ 2 * L := mul_le_mul_of_nonneg_left hL_ge_one (pow_two_nonneg L)
          _ = L ^ 3 := by ring
      linarith
    -- L^5 = L^2 * L^3 ≥ L^2 * 1 = L^2
    calc
      L ^ 2 = L ^ 2 * 1 := by ring
      _ ≤ L ^ 2 * L ^ 3 := mul_le_mul_of_nonneg_left hL3_ge_one (by positivity)
      _ = L ^ 5 := by ring
  -- Therefore L² ≤ t / 29000
  have hL2_le_t_div_29000 : L ^ 2 ≤ t / 29000 := by
    linarith
  -- 500 * L² ≤ t / 58 (since 500/29000 = 1/58)
  have h500L2_le_t_div_58 : 500 * L ^ 2 ≤ t / 58 := by
    have : (500 : ℝ) / 29000 = (1 : ℝ) / 58 := by norm_num
    nlinarith
  -- H.dsmall: δ_e * ((d : ℝ) * n) ^ 3 * n ≤ exp(-14)
  -- Simplify: ((d : ℝ) * n) ^ 3 * n = d^3 * n^4
  have hdsmall_simp : p.δe * (d : ℝ)^3 * (n : ℝ)^4 ≤ Real.exp (-14) := by
    have h := H.dsmall
    -- h : p.δe * ((d : ℝ) * n) ^ 3 * n ≤ Real.exp (-14)
    -- h is (p.δe * ((d : ℝ) * n) ^ 3) * n ≤ Real.exp (-14)
    calc
      p.δe * (d : ℝ)^3 * (n : ℝ)^4 = p.δe * ((d : ℝ)^3 * (n : ℝ)^4) := by ring
      _ = p.δe * (((d : ℝ) * (n : ℝ)) ^ 3 * (n : ℝ)) := by ring
      _ = (p.δe * ((d : ℝ) * (n : ℝ)) ^ 3) * (n : ℝ) := by ring
      _ ≤ Real.exp (-14) := h
  -- Main inequality chain
  have h_main : 500 * p.δe * (n : ℝ) * t * (d : ℝ) * L ^ 2 ≤ 1 := by
    -- Step 1: 500 * L² ≤ t/58, so
    -- 500 * δ_e * n * t * d * L² ≤ (t/58) * δ_e * n * t * d
    have hstep1 : 500 * p.δe * (n : ℝ) * t * (d : ℝ) * L ^ 2 ≤
        (t / 58) * p.δe * (n : ℝ) * t * (d : ℝ) := by
      have hpos_factor : 0 ≤ p.δe * (n : ℝ) * t * (d : ℝ) := by positivity
      nlinarith
    -- Step 2: t² = n, so (t/58) * δ_e * n * t * d = (1/58) * δ_e * n² * d
    have hstep2 : (t / 58) * p.δe * (n : ℝ) * t * (d : ℝ) = (1/58 : ℝ) * p.δe * (n : ℝ)^2 * (d : ℝ) := by
      calc
        (t / 58) * p.δe * (n : ℝ) * t * (d : ℝ) = (1/58) * (t * t) * p.δe * (n : ℝ) * (d : ℝ) := by ring
        _ = (1/58) * (t^2) * p.δe * (n : ℝ) * (d : ℝ) := by ring
        _ = (1/58) * (n : ℝ) * p.δe * (n : ℝ) * (d : ℝ) := by rw [ht_sq]
        _ = (1/58 : ℝ) * p.δe * (n : ℝ)^2 * (d : ℝ) := by ring
    rw [hstep2] at hstep1
    -- Step 3: Since d ≥ 1, n ≥ 1: n² * d ≤ d³ * n⁴
    have hstep3 : (1/58 : ℝ) * p.δe * (n : ℝ)^2 * (d : ℝ) ≤
        (1/58 : ℝ) * p.δe * (d : ℝ)^3 * (n : ℝ)^4 := by
      have h_ineq : (n : ℝ)^2 * (d : ℝ) ≤ (d : ℝ)^3 * (n : ℝ)^4 := by
        have hd_sq_ge_one : 1 ≤ (d : ℝ)^2 := by nlinarith
        have hn_sq_ge_one : 1 ≤ (n : ℝ)^2 := by nlinarith
        have hprod_ge_one : 1 ≤ (d : ℝ)^2 * (n : ℝ)^2 := by nlinarith
        have h_nonneg : 0 ≤ (n : ℝ)^2 * (d : ℝ) := by positivity
        calc
          (n : ℝ)^2 * (d : ℝ) = ((n : ℝ)^2 * (d : ℝ)) * 1 := by ring
          _ ≤ ((n : ℝ)^2 * (d : ℝ)) * ((d : ℝ)^2 * (n : ℝ)^2) :=
            mul_le_mul_of_nonneg_left hprod_ge_one h_nonneg
          _ = (d : ℝ)^3 * (n : ℝ)^4 := by ring
      have h_nonneg_de : 0 ≤ p.δe := by linarith
      nlinarith
    -- Step 4: From hdsmall_simp: δ_e * d³ * n⁴ ≤ exp(-14)
    have hstep4 : (1/58 : ℝ) * p.δe * (d : ℝ)^3 * (n : ℝ)^4 ≤ (1/58 : ℝ) * Real.exp (-14) := by
      have h_nonneg : 0 ≤ (1/58 : ℝ) := by norm_num
      nlinarith
    -- Step 5: exp(-14) < exp(0) = 1, so (1/58) * exp(-14) ≤ 1
    have hstep5 : (1/58 : ℝ) * Real.exp (-14) ≤ 1 := by
      have h_exp_le_one : Real.exp (-14 : ℝ) ≤ 1 := by
        have h_lt : Real.exp (-14 : ℝ) < Real.exp (0 : ℝ) := by
          rw [Real.exp_lt_exp]
          linarith
        simpa [Real.exp_zero] using h_lt
      nlinarith
    -- Combine all steps
    linarith
  -- Reassemble: the goal is 500 * δ_e * (n * t) * d * L² ≤ 1
  simpa [hs_def, ht_def, hL_def, mul_comm, mul_left_comm, mul_assoc] using h_main

theorem row_clg (p : Df2OPar) (d n : ℕ) (H : RowHyp p d n) : df2Lg p n ≤ 4 / 3 * Real.log (1 / p.δe) := by
  rcases H with ⟨hd, hn, de_pos, de_lt, Le, L504, cx, dsmall, lam, eta, sig2, rho, eps, eps_le, reg, kap, theta, alpha, c1, gam, k0, R, hlog⟩
  have hd' : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hpos_n : (0 : ℝ) < (n : ℝ) := by linarith
  have hpos_14 : (0 : ℝ) < 14 := by norm_num
  have hpos_d : (0 : ℝ) < (d : ℝ) := by
    have : (0 : ℝ) ≤ (d : ℝ) := by exact_mod_cast Nat.zero_le d
    linarith
  have hlog_d_nonneg : 0 ≤ Real.log (d : ℝ) := Real.log_nonneg (by exact_mod_cast hd)
  have hlog_n_nonneg : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn'
  set x := Real.log (1 / p.δe) with hx_def
  have h_one_le_inv_de : 1 ≤ 1 / p.δe :=
    one_le_one_div de_pos de_lt.le
  have hx_pos : 0 ≤ x := by
    rw [hx_def]
    exact Real.log_nonneg h_one_le_inv_de
  -- From H.cx: x ≥ 14 + 3 * log(d * n)
  have h_cx' : 14 + 3 * Real.log ((d : ℝ) * (n : ℝ)) ≤ x := by
    rw [hx_def]
    exact cx
  -- log(d * n) = log d + log n ≥ log n (since log d ≥ 0)
  have h_log_dn_ge_log_n : Real.log (n : ℝ) ≤ Real.log ((d : ℝ) * (n : ℝ)) := by
    have h_log_mul : Real.log ((d : ℝ) * (n : ℝ)) = Real.log (d : ℝ) + Real.log (n : ℝ) :=
      Real.log_mul (by exact ne_of_gt hpos_d) (by exact ne_of_gt hpos_n)
    calc
      Real.log (n : ℝ) = (Real.log (d : ℝ) + Real.log (n : ℝ)) - Real.log (d : ℝ) := by ring
      _ = Real.log ((d : ℝ) * (n : ℝ)) - Real.log (d : ℝ) := by rw [h_log_mul]
      _ ≤ Real.log ((d : ℝ) * (n : ℝ)) := by nlinarith
  -- Therefore x ≥ 14 + 3 * log n
  have h_x_ge : 14 + 3 * Real.log (n : ℝ) ≤ x := by
    linarith
  -- So log n ≤ (x - 14) / 3
  have h_log_n_le : Real.log (n : ℝ) ≤ (x - 14) / 3 := by
    linarith
  -- Need: log 14 ≤ 14/3
  have h_log_14_le_9_div_2 : Real.log 14 ≤ 9/2 := by
    -- e^{9/2} ≥ 14
    have h_exp_ineq : (14 : ℝ) ≤ Real.exp (9/2) := by
      -- e^{3/2} ≥ 5/2 by Real.add_one_le_exp
      have h1 : (5/2 : ℝ) ≤ Real.exp (3/2) := by
        have := Real.add_one_le_exp (3/2)
        linarith
      -- e^{9/2} = (e^{3/2})^3 ≥ (5/2)^3 = 125/8 ≥ 14
      have h2 : Real.exp (9/2) = (Real.exp (3/2)) ^ 3 := by
        calc
          Real.exp (9/2) = Real.exp ((3/2) + (3/2) + (3/2)) := by ring
          _ = Real.exp ((3/2) + (3/2)) * Real.exp (3/2) := by rw [Real.exp_add]
          _ = (Real.exp (3/2) * Real.exp (3/2)) * Real.exp (3/2) := by rw [Real.exp_add]
          _ = (Real.exp (3/2)) ^ 3 := by ring
      have h3 : (5/2 : ℝ) ^ 3 ≤ (Real.exp (3/2)) ^ 3 := by
        have h_nonneg : (0 : ℝ) ≤ 5/2 := by norm_num
        have h_exp_nonneg : (0 : ℝ) ≤ Real.exp (3/2) := (Real.exp_pos _).le
        -- Use mul_le_mul three times
        have h_sq : (5/2 : ℝ) * (5/2 : ℝ) ≤ Real.exp (3/2) * Real.exp (3/2) :=
          mul_le_mul h1 h1 h_nonneg h_exp_nonneg
        have h_cube : (5/2 : ℝ) * ((5/2 : ℝ) * (5/2 : ℝ)) ≤ Real.exp (3/2) * (Real.exp (3/2) * Real.exp (3/2)) :=
          mul_le_mul h1 h_sq (by nlinarith) (by nlinarith)
        -- Rewrite both sides as ^3
        calc
          (5/2 : ℝ) ^ 3 = (5/2 : ℝ) * ((5/2 : ℝ) * (5/2 : ℝ)) := by ring
          _ ≤ Real.exp (3/2) * (Real.exp (3/2) * Real.exp (3/2)) := h_cube
          _ = (Real.exp (3/2)) ^ 3 := by ring
      have h4 : (14 : ℝ) ≤ (5/2 : ℝ) ^ 3 := by
        norm_num
      calc
        (14 : ℝ) ≤ (5/2 : ℝ) ^ 3 := h4
        _ ≤ (Real.exp (3/2)) ^ 3 := h3
        _ = Real.exp (9/2) := by symm; exact h2
    -- Now use Real.log_le_iff_le_exp
    rw [Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 14)]
    exact h_exp_ineq
  have h_9_div_2_le_14_div_3 : (9/2 : ℝ) ≤ 14/3 := by norm_num
  have h_log_14_le_14_div_3 : Real.log 14 ≤ 14/3 := by
    linarith
  -- Now compute df2Lg p n = log(14 * n / δ_e) = log 14 + log n + log(1/δ_e)
  have h_df2Lg_eq : df2Lg p n = Real.log 14 + Real.log (n : ℝ) + x := by
    dsimp [df2Lg]
    rw [hx_def]
    have h1 : (14 : ℝ) * (n : ℝ) / p.δe = ((14 : ℝ) * (n : ℝ)) * (1 / p.δe) := by ring
    rw [h1]
    have hpos_14n : (14 : ℝ) * (n : ℝ) ≠ 0 := by
      positivity
    have hpos_inv_de : 1 / p.δe ≠ 0 := by
      positivity
    rw [Real.log_mul hpos_14n hpos_inv_de]
    have hpos_n' : (n : ℝ) ≠ 0 := by exact ne_of_gt hpos_n
    have hpos_14' : (14 : ℝ) ≠ 0 := by norm_num
    rw [Real.log_mul hpos_14' hpos_n']
  rw [h_df2Lg_eq]
  -- Now: log 14 + log n + x ≤ 14/3 + (x - 14)/3 + x = (4/3) * x
  have h_sum : Real.log 14 + Real.log (n : ℝ) + x ≤ 14/3 + (x - 14)/3 + x := by
    linarith
  calc
    Real.log 14 + Real.log (n : ℝ) + x ≤ 14/3 + (x - 14)/3 + x := h_sum
    _ = (4/3 : ℝ) * x := by ring

theorem row_cz (p : Df2OPar) (d n : ℕ) (H : RowHyp p d n) :
    1 / 4 * Real.sqrt p.k0 * df2C0 * Real.sqrt (32 / 9) * p.δe ^ ((3 : ℝ) / 2) * (n : ℝ) ^ ((3 : ℝ) / 2) *
      Real.sqrt d * Real.log (1 / p.δe) ^ ((3 : ℝ) / 2) ≤ 3 / 4 := by
  -- Extract hypotheses
  have hd1 : 1 ≤ d := H.hd
  have hn1 : 1 ≤ n := H.hn
  have hde_pos : 0 < p.δe := H.de_pos
  have hde_lt_one : p.δe < 1 := H.de_lt
  have hLe : p.Le = 36 * Real.log (1 / p.δe) := H.Le
  have hL504 : 504 ≤ p.Le := H.L504
  have hdsmall : p.δe * ((d : ℝ) * (n : ℝ)) ^ 3 * (n : ℝ) ≤ Real.exp (-14) := H.dsmall
  have hlam : p.lam = 1 / (725 * (d : ℝ) * p.Le ^ 2) := H.lam
  have hreg : 29000 * ((d : ℝ) * Real.sqrt (d : ℝ)) * p.Le ^ 5 ≤ Real.sqrt (n : ℝ) := H.reg
  have hk0 : p.k0 = ((1 - p.lam) ^ 2)⁻¹ := H.k0
  have hd1' : 1 ≤ (d : ℝ) := by exact_mod_cast hd1
  have hn1' : 1 ≤ (n : ℝ) := by exact_mod_cast hn1
  have hd_pos' : 0 ≤ (d : ℝ) := by exact_mod_cast Nat.zero_le d
  have hn_pos' : 0 ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
  have hs_nonneg : 0 ≤ Real.sqrt (d : ℝ) := Real.sqrt_nonneg _
  have ht_nonneg : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  -- Abbreviations
  set x := Real.log (1 / p.δe) with hx_def
  set L := p.Le with hL_def
  set s := Real.sqrt (d : ℝ) with hs_def
  set t := Real.sqrt (n : ℝ) with ht_def
  set B := p.δe * (n : ℝ) * x with hB_def
  -- Positivity of x
  have hx_pos : 0 < x := by
    rw [hx_def]
    refine Real.log_pos ?_
    exact one_lt_one_div hde_pos hde_lt_one
  have hx_nonneg : 0 ≤ x := le_of_lt hx_pos
  -- L = 36 * x
  have hL_eq_36x : L = 36 * x := hLe
  have hL_pos : 0 < L := by linarith
  have hL_nonneg : 0 ≤ L := le_of_lt hL_pos
  -- L ≤ t (from regime)
  have hL_le_t : L ≤ t := by
    have hs_ge_one : 1 ≤ s := by
      rw [hs_def]
      calc
        1 = Real.sqrt 1 := by norm_num
        _ ≤ Real.sqrt (d : ℝ) := Real.sqrt_le_sqrt hd1'
        _ = s := rfl
    have hL5_le_t : L ^ 5 ≤ t := by
      have h_factor_ge_one : 1 ≤ 29000 * ((d : ℝ) * s) := by
        have hds_ge_one : 1 ≤ (d : ℝ) * s := by
          simpa using mul_le_mul hd1' hs_ge_one (by linarith) hd_pos'
        nlinarith
      have hreg' : 29000 * ((d : ℝ) * s) * L ^ 5 ≤ t := by
        simpa [hs_def, hL_def, ht_def] using hreg
      nlinarith
    have hL_ge_one : 1 ≤ L := by linarith
    have hL5_ge_L : L ≤ L ^ 5 := by
      have h_exp : (1 : ℕ) ≤ 5 := by norm_num
      simpa using pow_le_pow_right₀ hL_ge_one h_exp
    linarith
  -- t ≤ n (since n ≥ 1, sqrt(n) ≤ n)
  have ht_le_n : t ≤ (n : ℝ) := by
    rw [ht_def]
    -- sqrt(n) ≤ n for n ≥ 1
    -- Square both sides: n ≤ n^2, which holds for n ≥ 1
    have h_sq : (Real.sqrt (n : ℝ)) ^ 2 ≤ (n : ℝ) ^ 2 := by
      rw [Real.sq_sqrt hn_pos']
      nlinarith
    -- Since both sides are nonnegative, a^2 ≤ b^2 implies a ≤ b
    have h_sqrt_nonneg : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
    nlinarith
  -- x ≤ n
  have hx_le_n : x ≤ (n : ℝ) := by
    linarith
  -- B ≤ δe * n^2
  have hB_le_deln2 : B ≤ p.δe * ((n : ℝ) ^ 2) := by
    rw [hB_def]
    have h_nonneg : 0 ≤ p.δe * (n : ℝ) := by positivity
    have h_mul : p.δe * (n : ℝ) * x ≤ p.δe * (n : ℝ) * (n : ℝ) :=
      mul_le_mul_of_nonneg_left hx_le_n h_nonneg
    simpa [pow_two, mul_assoc] using h_mul
  -- δe * n^2 ≤ exp(-14) / d^3
  have h_deln2_le_exp_div_d3 : p.δe * ((n : ℝ) ^ 2) ≤ Real.exp (-14) / ((d : ℝ) ^ 3) := by
    have h_dsmall' : p.δe * ((d : ℝ) ^ 3) * ((n : ℝ) ^ 4) ≤ Real.exp (-14) := by
      -- From H.dsmall: δe * (d*n)^3 * n ≤ exp(-14)
      -- Expand (d*n)^3 = d^3 * n^3, so δe * d^3 * n^3 * n = δe * d^3 * n^4
      have h := hdsmall
      have h_expanded : p.δe * ((d : ℝ) * (n : ℝ)) ^ 3 * (n : ℝ) = p.δe * ((d : ℝ) ^ 3) * ((n : ℝ) ^ 4) := by ring
      rw [h_expanded] at h
      exact h
    have hd3_pos : 0 < (d : ℝ) ^ 3 := by positivity
    have h : p.δe * ((n : ℝ) ^ 2) * ((d : ℝ) ^ 3) ≤ Real.exp (-14) := by
      have hn2_le_n4 : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 4 := by
        have h_exp : (2 : ℕ) ≤ 4 := by norm_num
        exact pow_le_pow_right₀ hn1' h_exp
      have h_nonneg : 0 ≤ p.δe * ((d : ℝ) ^ 3) := by positivity
      have h_mul : p.δe * ((n : ℝ) ^ 2) * ((d : ℝ) ^ 3) ≤ p.δe * ((d : ℝ) ^ 3) * ((n : ℝ) ^ 4) := by
        calc
          p.δe * ((n : ℝ) ^ 2) * ((d : ℝ) ^ 3) = (p.δe * ((d : ℝ) ^ 3)) * ((n : ℝ) ^ 2) := by ring
          _ ≤ (p.δe * ((d : ℝ) ^ 3)) * ((n : ℝ) ^ 4) := mul_le_mul_of_nonneg_left hn2_le_n4 h_nonneg
          _ = p.δe * ((d : ℝ) ^ 3) * ((n : ℝ) ^ 4) := by ring
      exact le_trans h_mul h_dsmall'
    field_simp [hd3_pos.ne.symm]
    exact h
  -- exp(-14) / d^3 ≤ exp(-14) (since d ≥ 1, d^3 ≥ 1)
  have h_exp_div_d3_le_exp : Real.exp (-14) / ((d : ℝ) ^ 3) ≤ Real.exp (-14) := by
    have hd3_ge_one : 1 ≤ (d : ℝ) ^ 3 := by
      have h := pow_le_pow_left₀ (by norm_num : 0 ≤ (1 : ℝ)) hd1' 3
      simpa using h
    have h_exp_pos : 0 < Real.exp (-14) := Real.exp_pos _
    exact (div_le_self (le_of_lt h_exp_pos) hd3_ge_one)
  -- exp(-14) ≤ 1
  have h_exp_le_one : Real.exp (-14) ≤ 1 := by
    rw [Real.exp_neg]
    have h_exp14_ge_one : 1 ≤ Real.exp 14 := by
      have h := Real.add_one_le_exp 14
      linarith
    exact inv_le_one_of_one_le₀ h_exp14_ge_one
  -- B ≤ 1
  have hB_le_one : B ≤ 1 := by
    linarith
  -- B ≥ 0
  have hB_nonneg : 0 ≤ B := by
    rw [hB_def]
    positivity
  -- B > 0 (for Real.rpow_le_rpow_of_exponent_ge)
  have hB_pos : 0 < B := by
    rw [hB_def]
    positivity
  -- B^(3/2) ≤ B
  have hB_pow_le_B : B ^ ((3 : ℝ) / 2) ≤ B := by
    have h_exp : (1 : ℝ) ≤ (3 : ℝ) / 2 := by norm_num
    calc
      B ^ ((3 : ℝ) / 2) ≤ B ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_ge hB_pos hB_le_one h_exp
      _ = B := by simp
  -- sqrt(p.k0) ≤ 2
  have h_sqrt_k0_le_2 : Real.sqrt p.k0 ≤ 2 := by
    rw [hk0]
    have h_lam_le_half : p.lam ≤ 1/2 := by
      rw [hlam]
      have hden : 2 ≤ 725 * (d : ℝ) * L ^ 2 := by
        nlinarith
      have hpos_denom : 0 < 725 * (d : ℝ) * L ^ 2 := by positivity
      refine (one_div_le_one_div hpos_denom (by norm_num : 0 < (2 : ℝ))).mpr hden
    have h_one_minus_lam_pos : 0 < 1 - p.lam := by linarith
    calc
      Real.sqrt (((1 - p.lam) ^ 2)⁻¹) = (Real.sqrt ((1 - p.lam) ^ 2))⁻¹ := by rw [Real.sqrt_inv]
      _ = |1 - p.lam|⁻¹ := by rw [Real.sqrt_sq_eq_abs]
      _ = (1 - p.lam)⁻¹ := by rw [abs_of_pos h_one_minus_lam_pos]
      _ ≤ 2 := by
        field_simp
        linarith
  -- sqrt(32/9) ≤ 2
  have h_sqrt_32_9_le_2 : Real.sqrt (32/9 : ℝ) ≤ 2 := by
    calc
      Real.sqrt (32/9 : ℝ) ≤ Real.sqrt (4 : ℝ) := Real.sqrt_le_sqrt (by norm_num : (32/9 : ℝ) ≤ 4)
      _ = 2 := by norm_num
  -- Constant factor bound: (1/4) * sqrt(p.k0) * 36 * sqrt(32/9) ≤ 36
  have h_const_factor_le_36 : (1/4 : ℝ) * Real.sqrt p.k0 * (36 : ℝ) * Real.sqrt (32/9 : ℝ) ≤ (36 : ℝ) := by
    have h_prod : Real.sqrt p.k0 * Real.sqrt (32/9 : ℝ) ≤ 2 * 2 :=
      mul_le_mul h_sqrt_k0_le_2 h_sqrt_32_9_le_2 (Real.sqrt_nonneg _) (by norm_num)
    calc
      (1/4 : ℝ) * Real.sqrt p.k0 * (36 : ℝ) * Real.sqrt (32/9 : ℝ) =
        ((1/4 : ℝ) * (36 : ℝ)) * (Real.sqrt p.k0 * Real.sqrt (32/9 : ℝ)) := by ring
      _ ≤ ((1/4 : ℝ) * (36 : ℝ)) * (2 * 2) :=
        mul_le_mul_of_nonneg_left h_prod (by norm_num)
      _ = (36 : ℝ) := by norm_num
  -- Product equality: δe^(3/2) * n^(3/2) * x^(3/2) = B^(3/2)
  have h_prod_eq_Bpow : p.δe ^ ((3 : ℝ) / 2) * ((n : ℝ) ^ ((3 : ℝ) / 2)) * (x ^ ((3 : ℝ) / 2)) = B ^ ((3 : ℝ) / 2) := by
    calc
      p.δe ^ ((3 : ℝ) / 2) * ((n : ℝ) ^ ((3 : ℝ) / 2)) * (x ^ ((3 : ℝ) / 2)) =
          ((p.δe * (n : ℝ)) ^ ((3 : ℝ) / 2)) * (x ^ ((3 : ℝ) / 2)) := by
        rw [Real.mul_rpow (le_of_lt hde_pos) hn_pos']
      _ = ((p.δe * (n : ℝ)) * x) ^ ((3 : ℝ) / 2) := by
        rw [Real.mul_rpow (mul_nonneg (le_of_lt hde_pos) hn_pos') hx_nonneg]
      _ = B ^ ((3 : ℝ) / 2) := by rw [hB_def]
  -- sqrt(d) ≤ d^3 (for d ≥ 1)
  have hs_le_d3 : s ≤ (d : ℝ) ^ 3 := by
    rw [hs_def]
    have hs_le_d : Real.sqrt (d : ℝ) ≤ (d : ℝ) := by
      have hs_ge_one : 1 ≤ Real.sqrt (d : ℝ) := by
        calc
          1 = Real.sqrt 1 := by norm_num
          _ ≤ Real.sqrt (d : ℝ) := Real.sqrt_le_sqrt hd1'
      calc
        Real.sqrt (d : ℝ) = Real.sqrt (d : ℝ) * 1 := by ring
        _ ≤ Real.sqrt (d : ℝ) * Real.sqrt (d : ℝ) :=
          mul_le_mul_of_nonneg_left hs_ge_one (Real.sqrt_nonneg _)
        _ = d := Real.mul_self_sqrt hd_pos'
    have hd_le_d3 : (d : ℝ) ≤ (d : ℝ) ^ 3 := by
      have h_exp : (1 : ℕ) ≤ 3 := by norm_num
      simpa using pow_le_pow_right₀ hd1' h_exp
    linarith
  -- Main inequality chain
  calc
    1 / 4 * Real.sqrt p.k0 * df2C0 * Real.sqrt (32 / 9) * p.δe ^ ((3 : ℝ) / 2) * (n : ℝ) ^ ((3 : ℝ) / 2) *
      Real.sqrt d * Real.log (1 / p.δe) ^ ((3 : ℝ) / 2)
    = ((1/4 : ℝ) * Real.sqrt p.k0 * (36 : ℝ) * Real.sqrt (32/9 : ℝ)) *
      (p.δe ^ ((3 : ℝ) / 2) * ((n : ℝ) ^ ((3 : ℝ) / 2)) * (x ^ ((3 : ℝ) / 2))) *
      Real.sqrt (d : ℝ) := by
      rw [hx_def, df2C0]
      ring
    _ ≤ ((36 : ℝ)) * (B ^ ((3 : ℝ) / 2)) * Real.sqrt (d : ℝ) := by
      rw [h_prod_eq_Bpow]
      have h_nonneg_Bpow : 0 ≤ B ^ ((3 : ℝ) / 2) := Real.rpow_nonneg hB_nonneg _
      have h_mul : ((1/4 : ℝ) * Real.sqrt p.k0 * (36 : ℝ) * Real.sqrt (32/9 : ℝ)) *
        (B ^ ((3 : ℝ) / 2)) ≤ (36 : ℝ) * (B ^ ((3 : ℝ) / 2)) :=
        mul_le_mul_of_nonneg_right h_const_factor_le_36 h_nonneg_Bpow
      have h_mul_s : (((1/4 : ℝ) * Real.sqrt p.k0 * (36 : ℝ) * Real.sqrt (32/9 : ℝ)) *
        (B ^ ((3 : ℝ) / 2))) * Real.sqrt (d : ℝ) ≤
        ((36 : ℝ) * (B ^ ((3 : ℝ) / 2))) * Real.sqrt (d : ℝ) :=
        mul_le_mul_of_nonneg_right h_mul hs_nonneg
      simpa [mul_assoc] using h_mul_s
    _ = (36 : ℝ) * (B ^ ((3 : ℝ) / 2) * Real.sqrt (d : ℝ)) := by ring
    _ ≤ (36 : ℝ) * (B * Real.sqrt (d : ℝ)) := by
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num : 0 ≤ (36 : ℝ))
      exact mul_le_mul_of_nonneg_right hB_pow_le_B hs_nonneg
    _ = (36 : ℝ) * B * Real.sqrt (d : ℝ) := by ring
    _ ≤ (36 : ℝ) * (Real.exp (-14) / ((d : ℝ) ^ 3)) * Real.sqrt (d : ℝ) := by
      have hB_le : B ≤ Real.exp (-14) / ((d : ℝ) ^ 3) := by linarith
      apply mul_le_mul_of_nonneg_right ?_ hs_nonneg
      apply mul_le_mul_of_nonneg_left hB_le (by norm_num)
    _ = (36 : ℝ) * Real.exp (-14) * (Real.sqrt (d : ℝ) / ((d : ℝ) ^ 3)) := by ring
    _ ≤ (36 : ℝ) * Real.exp (-14) * 1 := by
      have h_nonneg : 0 ≤ (36 : ℝ) * Real.exp (-14) := by positivity
      apply mul_le_mul_of_nonneg_left ?_ h_nonneg
      have hd3_pos : 0 < (d : ℝ) ^ 3 := by positivity
      exact (div_le_one hd3_pos).mpr hs_le_d3
    _ = (36 : ℝ) * Real.exp (-14) := by ring
    _ ≤ 3/4 := by
      rw [Real.exp_neg 14]
      have h_exp14_pos : 0 < Real.exp 14 := Real.exp_pos _
      apply (div_le_iff₀ h_exp14_pos).mpr
      have h_exp7_ge_8 : (8 : ℝ) ≤ Real.exp 7 := by
        have h := Real.add_one_le_exp 7
        linarith
      have h_exp14_ge_64 : (64 : ℝ) ≤ Real.exp 14 := by
        calc
          (64 : ℝ) = (8 : ℝ) * (8 : ℝ) := by norm_num
          _ ≤ Real.exp 7 * Real.exp 7 := mul_le_mul h_exp7_ge_8 h_exp7_ge_8 (by positivity) (by linarith)
          _ = Real.exp (7 + 7) := by rw [Real.exp_add]
          _ = Real.exp 14 := by norm_num
      nlinarith

/-! ### The terms of the long rows against `ρ` -/

theorem cmp_one (p : Df2OPar) (d n : ℕ) (H : RowHyp p d n) : 1 ≤ p.rho / 10 ^ 8 := by
  have hd' : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast H.hd
  have hL : (504 : ℝ) ≤ p.Le := H.L504
  rw [H.rho]
  rw [le_div_iff₀ (by norm_num : (0 : ℝ) < (10 : ℝ) ^ 8)]
  have hd_sq : (1 : ℝ) ≤ (d : ℝ) ^ 2 := by
    calc
      (1 : ℝ) = (1 : ℝ) ^ 2 := by norm_num
      _ ≤ (d : ℝ) ^ 2 := by nlinarith
  have hL_cube : (504 : ℝ) ^ 3 ≤ p.Le ^ 3 := by
    have h504pos : 0 ≤ (504 : ℝ) := by norm_num
    have hLeppos : 0 ≤ p.Le := by linarith
    have hsq : (504 : ℝ) ^ 2 ≤ p.Le ^ 2 := by nlinarith
    calc
      (504 : ℝ) ^ 3 = (504 : ℝ) ^ 2 * (504 : ℝ) := by ring
      _ ≤ p.Le ^ 2 * (504 : ℝ) := by nlinarith
      _ ≤ p.Le ^ 2 * p.Le := by nlinarith
      _ = p.Le ^ 3 := by ring
  have hbase : (10 : ℝ) ^ 8 ≤ (2 * 725 : ℝ) * (504 : ℝ) ^ 3 := by
    norm_num
  nlinarith

theorem cmp_pri (p : Df2OPar) (d n : ℕ) (H : RowHyp p d n) : df2Pri p ≤ p.rho / 300 := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast H.hd
  have hLpos : 0 < p.Le := by
    have : 504 ≤ p.Le := H.L504
    linarith
  have hlog_nonneg : 0 ≤ Real.log (2 * (d : ℝ) + 2) := by
    have hpos' : 1 ≤ 2 * (d : ℝ) + 2 := by nlinarith
    exact Real.log_nonneg hpos'
  have hlog_bound : Real.log (2 * (d : ℝ) + 2) ≤ p.Le / 36 := by
    have h := H.hlog
    have h_eq : Real.log (1 / p.δe) = p.Le / 36 := by
      linarith [H.Le]
    rw [h_eq] at h
    exact h
  dsimp [df2Pri]
  rw [H.rho, H.R, H.sig2]
  have hLHS : (134 * (d : ℝ) * Real.sqrt (Real.log (2 * (d : ℝ) + 2))) ^ 2 / (2 * (1 / (8 * p.Le))) =
    4 * (134 : ℝ) ^ 2 * (d : ℝ) ^ 2 * p.Le * Real.log (2 * (d : ℝ) + 2) := by
    calc
      (134 * (d : ℝ) * Real.sqrt (Real.log (2 * (d : ℝ) + 2))) ^ 2 / (2 * (1 / (8 * p.Le))) =
        ((134 * (d : ℝ)) ^ 2 * (Real.sqrt (Real.log (2 * (d : ℝ) + 2))) ^ 2) / (2 * (1 / (8 * p.Le))) := by ring
      _ = ((134 * (d : ℝ)) ^ 2 * Real.log (2 * (d : ℝ) + 2)) / (2 * (1 / (8 * p.Le))) := by
        rw [Real.sq_sqrt hlog_nonneg]
      _ = ((134 : ℝ) ^ 2 * (d : ℝ) ^ 2 * Real.log (2 * (d : ℝ) + 2)) / (1 / (4 * p.Le)) := by ring
      _ = ((134 : ℝ) ^ 2 * (d : ℝ) ^ 2 * Real.log (2 * (d : ℝ) + 2)) * (4 * p.Le) := by
        field_simp [hLpos.ne.symm]
      _ = 4 * (134 : ℝ) ^ 2 * (d : ℝ) ^ 2 * p.Le * Real.log (2 * (d : ℝ) + 2) := by ring
  rw [hLHS]
  have hbound : 4 * (134 : ℝ) ^ 2 * (d : ℝ) ^ 2 * p.Le * Real.log (2 * (d : ℝ) + 2) ≤
    4 * (134 : ℝ) ^ 2 * (d : ℝ) ^ 2 * p.Le * (p.Le / 36) := by
    have hnonneg : 0 ≤ 4 * (134 : ℝ) ^ 2 * (d : ℝ) ^ 2 * p.Le := by
      positivity
    nlinarith
  have hfinal : 4 * (134 : ℝ) ^ 2 * (d : ℝ) ^ 2 * p.Le * (p.Le / 36) ≤ (2 * 725 * (d : ℝ) ^ 2 * p.Le ^ 3) / 300 := by
    have hkey : 4 * (134 : ℝ) ^ 2 * 300 ≤ 2 * 725 * 36 * p.Le := by
      nlinarith [H.L504]
    field_simp [show (300 : ℝ) ≠ 0 from by norm_num, show (36 : ℝ) ≠ 0 from by norm_num]
    nlinarith
  nlinarith

theorem cmp_stab (p : Df2OPar) (d n : ℕ) (H : RowHyp p d n) : df2Stab p d n ≤ p.rho / 10 ^ 6 := by
  rcases H with ⟨hd, hn, de_pos, de_lt, Le, L504, cx, dsmall, lam, eta, sig2, rho, eps, eps_le, reg, kap, theta, alpha, c1, gam, k0, R, hlog⟩
  have hLe : 0 < p.Le := by linarith
  have hLe_ne : p.Le ≠ 0 := by linarith
  have hd_nonneg : 0 ≤ (d : ℝ) := Nat.cast_nonneg _
  have hn_nonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
  have hsqrt_n_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  have hsqrt_n_ne : Real.sqrt (n : ℝ) ≠ 0 := by linarith
  have h10_ne : (10 : ℝ) ^ 6 ≠ 0 := by norm_num
  -- Compute df2Stab in closed form: 2*4*(√d/(p.Le*√n))^2*d*n*p.Le = 8*d^2/p.Le
  have hStab_eq : df2Stab p d n = 8 * ((d : ℝ) ^ 2) / p.Le := by
    unfold df2Stab
    rw [eta, show df2Cg = (4 : ℝ) from rfl]
    field_simp [hLe_ne, hsqrt_n_ne]
    ring_nf
    rw [Real.sq_sqrt hd_nonneg, Real.sq_sqrt hn_nonneg]
    ring_nf
  -- Compute p.rho in closed form: 2*725*d^2*p.Le^3 = 1450*d^2*p.Le^3
  have hRho_eq : p.rho = 1450 * ((d : ℝ) ^ 2) * p.Le ^ 3 := by
    rw [rho]
    ring
  rw [hStab_eq, hRho_eq]
  -- Goal: 8*d^2/p.Le ≤ 1450*d^2*p.Le^3/10^6
  -- Multiply both sides by p.Le * 10^6 (positive) and use L504: p.Le ≥ 504
  have hkey : 8 * (10 : ℝ) ^ 6 ≤ 1450 * p.Le ^ 4 := by
    have hp4 : (504 : ℝ) ^ 4 ≤ p.Le ^ 4 := by gcongr
    have hdiv : 8 * (10 : ℝ) ^ 6 ≤ 1450 * (504 : ℝ) ^ 4 := by norm_num
    nlinarith
  field_simp [hLe_ne, h10_ne]
  nlinarith

set_option maxHeartbeats 800000 in
theorem cmp_b1 (p : Df2OPar) (d n : ℕ) (H : RowHyp p d n) : p.eta * df2B1 p d n ≤ p.rho / 1000 := by
  -- Extract numeric hypotheses, cast to ℝ
  have hd : 1 ≤ (d : ℝ) := by exact_mod_cast H.hd
  have hn : 1 ≤ (n : ℝ) := by exact_mod_cast H.hn
  have hdpos : 0 ≤ (d : ℝ) := by linarith
  have hnpos : 0 ≤ (n : ℝ) := by linarith
  have hLpos : 0 < p.Le := by linarith [H.L504]
  have hLpos' : 0 ≤ p.Le := by linarith
  -- Shorthands
  set s := Real.sqrt (d : ℝ) with hs_def
  set t := Real.sqrt (n : ℝ) with ht_def
  set L := p.Le with hL_def
  have hs_nonneg : 0 ≤ s := Real.sqrt_nonneg _
  have ht_nonneg : 0 ≤ t := Real.sqrt_nonneg _
  have hs_sq : s ^ 2 = (d : ℝ) := Real.sq_sqrt hdpos
  have ht_sq : t ^ 2 = (n : ℝ) := Real.sq_sqrt hnpos
  have hs_one : 1 ≤ s := by
    calc
      1 = Real.sqrt 1 := by norm_num
      _ ≤ Real.sqrt (d : ℝ) := Real.sqrt_le_sqrt hd
      _ = s := by rw [hs_def]
  have ht_one : 1 ≤ t := by
    calc
      1 = Real.sqrt 1 := by norm_num
      _ ≤ Real.sqrt (n : ℝ) := Real.sqrt_le_sqrt hn
      _ = t := by rw [ht_def]
  have hL504 : 504 ≤ L := H.L504
  have hL_one : 1 ≤ L := by linarith
  -- Key bound: 29000 * d * s * L^5 ≤ t
  have h_reg_raw : 29000 * ((d : ℝ) * Real.sqrt (d : ℝ)) * p.Le ^ 5 ≤ Real.sqrt (n : ℝ) := H.reg
  have h_reg : 29000 * (d : ℝ) * s * L ^ 5 ≤ t := by
    simpa [hs_def, ht_def, hL_def, mul_assoc] using h_reg_raw
  have h_st : s ≤ t := by
    have h_one_le : 1 ≤ 29000 * (d : ℝ) * L ^ 5 := by
      have : (1 : ℝ) ≤ 29000 := by norm_num
      have hd' : (1 : ℝ) ≤ (d : ℝ) := hd
      have hL5pow : (1 : ℝ) ≤ L ^ 5 := by
        have hL_nonneg : 0 ≤ L := by linarith
        have hL5 : L ^ 5 = L * (L ^ 4) := by ring
        rw [hL5]
        have hL4 : 1 ≤ L ^ 4 := by
          have hL2 : 1 ≤ L ^ 2 := by nlinarith
          nlinarith
        nlinarith
      nlinarith
    calc
      s = 1 * s := by ring
      _ ≤ (29000 * (d : ℝ) * L ^ 5) * s := by nlinarith
      _ = 29000 * (d : ℝ) * s * L ^ 5 := by ring
      _ ≤ t := h_reg
  -- Key algebraic identity: LHS = term1 + term2 + term3
  have h_lhs_eq : p.eta * df2B1 p d n = (s / (L * t)) + (725 * 11 / 20 : ℝ) * (d : ℝ) ^ 2 * L * Real.sqrt (10 * L) + (13 / 2000 : ℝ) * (d : ℝ) * s / (L ^ 2) := by
    dsimp [df2B1]
    rw [H.eta, H.lam, H.eps]
    rw [← hL_def, ← hs_def, ← ht_def]
    -- Simplify 1/(1/(725*d*L^2)) = 725*d*L^2 and the eps fraction together
    have h_sqrt_prod : Real.sqrt (10 * (d : ℝ) * (n : ℝ) * L) = Real.sqrt (10 * L) * s * t := by
      calc
        Real.sqrt (10 * (d : ℝ) * (n : ℝ) * L) = Real.sqrt ((10 * L) * ((d : ℝ) * (n : ℝ))) := by ring
        _ = Real.sqrt (10 * L) * Real.sqrt ((d : ℝ) * (n : ℝ)) := Real.sqrt_mul (by positivity) _
        _ = Real.sqrt (10 * L) * (Real.sqrt (d : ℝ) * Real.sqrt (n : ℝ)) := by rw [Real.sqrt_mul hdpos]
        _ = Real.sqrt (10 * L) * s * t := by rw [hs_def, ht_def]; ring
    rw [h_sqrt_prod]
    -- Now simplify the whole expression using field_simp and ring
    have h_denom1 : L * t ≠ 0 := by positivity
    have h_denom2 : 20 * 725 * L ^ 3 ≠ 0 := by positivity
    field_simp [h_denom1, h_denom2]
    ring_nf
    rw [hs_sq]
    ring
  rw [h_lhs_eq]
  -- RHS: p.rho / 1000 = (2*725*d^2*L^3)/1000 = (29/20)*d^2*L^3
  rw [H.rho, hL_def]
  have h_rhs : (2 * 725 * (d : ℝ) ^ 2 * L ^ 3) / 1000 = (29/20 : ℝ) * (d : ℝ) ^ 2 * L ^ 3 := by
    ring
  rw [h_rhs]
  -- Goal: s/(L*t) + (725*11/20)*d^2*L*√(10*L) + (13/2000)*d*s/L^2 ≤ (29/20)*d^2*L^3
  -- Term 1: s/(L*t) ≤ 1
  have h_term1 : s / (L * t) ≤ 1 := by
    apply (div_le_one ?_).mpr
    · calc
        s ≤ t := h_st
        _ ≤ L * t := by nlinarith
    · positivity
  -- Term 2: (725*11/20)*d^2*L*√(10*L) ≤ 1300*d^2*L*√L
  have h_term2 : (725 * 11 / 20 : ℝ) * (d : ℝ) ^ 2 * L * Real.sqrt (10 * L) ≤ 1300 * (d : ℝ) ^ 2 * L * Real.sqrt L := by
    have h_sqrt10_le : Real.sqrt 10 ≤ 32/10 := by
      have h_sq : (10 : ℝ) ≤ (32/10 : ℝ) ^ 2 := by norm_num
      calc
        Real.sqrt 10 ≤ Real.sqrt ((32/10 : ℝ) ^ 2) := Real.sqrt_le_sqrt h_sq
        _ = 32/10 := Real.sqrt_sq (by norm_num)
    have h_nonneg : 0 ≤ (725 * 11 / 20 : ℝ) * (d : ℝ) ^ 2 * L := by positivity
    have h_sqrtL_nonneg : 0 ≤ Real.sqrt L := Real.sqrt_nonneg _
    calc
      (725 * 11 / 20 : ℝ) * (d : ℝ) ^ 2 * L * Real.sqrt (10 * L)
          = (725 * 11 / 20 : ℝ) * (d : ℝ) ^ 2 * L * (Real.sqrt 10 * Real.sqrt L) := by
        rw [Real.sqrt_mul (by norm_num : 0 ≤ (10 : ℝ))]
      _ = ((725 * 11 / 20 : ℝ) * Real.sqrt 10 * Real.sqrt L) * (d : ℝ) ^ 2 * L := by ring
      _ ≤ ((725 * 11 / 20 : ℝ) * (32/10 : ℝ) * Real.sqrt L) * (d : ℝ) ^ 2 * L := by
        have h_mul : Real.sqrt 10 * Real.sqrt L ≤ (32/10 : ℝ) * Real.sqrt L := by
          nlinarith
        nlinarith
      _ = (725 * 11 * 32 / 200 : ℝ) * (d : ℝ) ^ 2 * L * Real.sqrt L := by ring
      _ ≤ 1300 * (d : ℝ) ^ 2 * L * Real.sqrt L := by
        have h_coeff : (725 * 11 * 32 / 200 : ℝ) ≤ 1300 := by norm_num
        nlinarith
  -- Term 3: (13/2000)*d*s/L^2 ≤ d^2
  have h_term3 : (13/2000 : ℝ) * (d : ℝ) * s / (L ^ 2) ≤ (d : ℝ) ^ 2 := by
    have hLsq_pos : 0 < L ^ 2 := by positivity
    field_simp [hLsq_pos.ne.symm]
    rw [← hs_sq]
    have hs_pos' : 0 < s := by linarith
    have h_ineq : (13 : ℝ) ≤ 2000 * s * L ^ 2 := by
      nlinarith
    nlinarith
  -- Combine the three terms
  have h_sum : s / (L * t) + (725 * 11 / 20 : ℝ) * (d : ℝ) ^ 2 * L * Real.sqrt (10 * L) + (13 / 2000 : ℝ) * (d : ℝ) * s / (L ^ 2) ≤
      1 + 1300 * (d : ℝ) ^ 2 * L * Real.sqrt L + (d : ℝ) ^ 2 := by
    nlinarith
  -- Now need: 1 + 1300*d^2*L*√L + d^2 ≤ (29/20)*d^2*L^3
  -- Key inequality: 1 + d^2 ≤ 2*d^2*L*√L
  have h_key : 1 + (d : ℝ) ^ 2 ≤ 2 * (d : ℝ) ^ 2 * L * Real.sqrt L := by
    have h_dsq_ge_one : 1 ≤ (d : ℝ) ^ 2 := by
      nlinarith
    have h_L_sqrtL_ge_one : 1 ≤ L * Real.sqrt L := by
      have h_sqrtL_ge_22 : 22 ≤ Real.sqrt L := by
        have h484 : (484 : ℝ) ≤ L := by
          have : (484 : ℝ) ≤ 504 := by norm_num
          linarith
        calc
          (22 : ℝ) = Real.sqrt ((22 : ℝ) ^ 2) := by norm_num
          _ = Real.sqrt 484 := by norm_num
          _ ≤ Real.sqrt L := Real.sqrt_le_sqrt h484
      nlinarith
    nlinarith
  -- From h_key: 1 + d^2 ≤ 2*d^2*L*√L
  -- So 1 + 1300*d^2*L*√L + d^2 ≤ 2*d^2*L*√L + 1300*d^2*L*√L = 1302*d^2*L*√L
  have h_mid : 1 + 1300 * (d : ℝ) ^ 2 * L * Real.sqrt L + (d : ℝ) ^ 2 ≤ 1302 * (d : ℝ) ^ 2 * L * Real.sqrt L := by
    nlinarith
  -- Now need: 1302*d^2*L*√L ≤ (29/20)*d^2*L^3
  have h_final : 1302 * (d : ℝ) ^ 2 * L * Real.sqrt L ≤ (29/20 : ℝ) * (d : ℝ) ^ 2 * L ^ 3 := by
    have hLpos'' : 0 < L := by linarith
    have h_sqrtL_ge_22 : 22 ≤ Real.sqrt L := by
      have h484 : (484 : ℝ) ≤ L := by
        have : (484 : ℝ) ≤ 504 := by norm_num
        linarith
      calc
        (22 : ℝ) = Real.sqrt ((22 : ℝ) ^ 2) := by norm_num
        _ = Real.sqrt 484 := by norm_num
        _ ≤ Real.sqrt L := Real.sqrt_le_sqrt h484
    have h_sqrtL_le_L_div_22 : Real.sqrt L ≤ L / 22 := by
      have h22_sqrtL_le_L : 22 * Real.sqrt L ≤ L := by
        have h_sq : (Real.sqrt L) ^ 2 = L := Real.sq_sqrt hLpos'
        nlinarith
      linarith
    have h_bound1 : 1302 * Real.sqrt L ≤ (1302/22 : ℝ) * L := by
      nlinarith
    have h_bound2 : (1302/22 : ℝ) * L ≤ (29/20 : ℝ) * L ^ 2 := by
      have hL_ge_504 : (504 : ℝ) ≤ L := hL504
      nlinarith
    have h_ineq : 1302 * Real.sqrt L ≤ (29/20 : ℝ) * L ^ 2 := by
      nlinarith
    have h_dsq_nonneg : 0 ≤ (d : ℝ) ^ 2 := by positivity
    nlinarith
  -- Combine everything
  nlinarith

set_option maxHeartbeats 800000 in
theorem cmp_bn (p : Df2OPar) (d n : ℕ) (H : RowHyp p d n) :
    p.eta * df2Bn p d n / (8 * p.Le * p.lam ^ 2) ≤ p.rho / 1000 := by
  rcases H with ⟨hd, hn, de_pos, de_lt, hLe, hL504, hcx, hdsmall, hlam, heta, hsig2, hrho, heps, heps_le, hreg, hkap, htheta, halpha, hc1, hgam, hk0, hR, hhlog⟩
  have hdpos' : 0 ≤ (d : ℝ) := by exact mod_cast (Nat.zero_le d)
  have hnpos' : 0 ≤ (n : ℝ) := by exact mod_cast (Nat.zero_le n)
  have hLpos : 0 < p.Le := by linarith
  have hLpos' : 0 ≤ p.Le := by linarith
  have hs_pos : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr (by exact mod_cast hd)
  have ht_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by exact mod_cast hn)
  set s := Real.sqrt (d : ℝ) with hs_def
  set t := Real.sqrt (n : ℝ) with ht_def
  have hs_sq : s ^ 2 = (d : ℝ) := Real.sq_sqrt hdpos'
  have ht_sq : t ^ 2 = (n : ℝ) := Real.sq_sqrt hnpos'
  have hs_nonneg : 0 ≤ s := Real.sqrt_nonneg _
  have ht_nonneg : 0 ≤ t := Real.sqrt_nonneg _
  have hs_le_d : s ≤ (d : ℝ) := by
    have hd1 : 1 ≤ (d : ℝ) := by exact mod_cast hd
    nlinarith [Real.sq_sqrt hdpos']
  have ht_ge_one : 1 ≤ t := by
    have hn1 : 1 ≤ (n : ℝ) := by exact mod_cast hn
    calc
      1 = Real.sqrt 1 := by norm_num
      _ ≤ Real.sqrt (n : ℝ) := Real.sqrt_le_sqrt hn1
      _ = t := rfl
  have hL_ge_504 : 504 ≤ p.Le := hL504
  have hreg' : 29000 * (d : ℝ) * s * p.Le ^ 5 ≤ t := by
    simpa [hs_def, ht_def, mul_assoc] using hreg
  -- bound sqrt(10) using (725/8)*√10 ≤ 287, i.e., √10 ≤ 2296/725
  have h_sqrt10_le : Real.sqrt 10 ≤ (2296 : ℝ) / 725 := by
    have h_sq : (Real.sqrt 10) ^ 2 = 10 := Real.sq_sqrt (by norm_num : 0 ≤ (10 : ℝ))
    have h_target_sq : ((2296 : ℝ) / 725) ^ 2 = 5271616 / 525625 := by norm_num
    have h_ineq : (10 : ℝ) ≤ ((2296 : ℝ) / 725) ^ 2 := by
      rw [h_target_sq]
      norm_num
    nlinarith
  have h_sqrt10_bound : (725 : ℝ) / 8 * Real.sqrt 10 ≤ 287 := by
    nlinarith [h_sqrt10_le]
  -- compute the left-hand side identity: η*B_n/(8*L*λ²) = (725/8)*s*d*L²*(1+√10*s*t+s*t/(14500*L⁴))/t
  have hLHS : p.eta * df2Bn p d n / (8 * p.Le * p.lam ^ 2) =
      (725 / 8) * s * (d : ℝ) * p.Le ^ 2 * (1 + Real.sqrt 10 * s * t + s * t / (14500 * p.Le ^ 4)) / t := by
    rw [heta]
    unfold df2Bn
    rw [hlam, heps]
    have h_sqrt_dn : Real.sqrt (10 * (d : ℝ) * (n : ℝ)) = Real.sqrt 10 * s * t := by
      calc
        Real.sqrt (10 * (d : ℝ) * (n : ℝ)) = Real.sqrt (10 * ((d : ℝ) * (n : ℝ))) := by ring
        _ = Real.sqrt 10 * Real.sqrt ((d : ℝ) * (n : ℝ)) := by rw [Real.sqrt_mul (by norm_num : 0 ≤ (10 : ℝ))]
        _ = Real.sqrt 10 * (Real.sqrt (d : ℝ) * Real.sqrt (n : ℝ)) := by rw [Real.sqrt_mul hdpos']
        _ = Real.sqrt 10 * s * t := by rw [hs_def, ht_def, mul_assoc]
    rw [h_sqrt_dn]
    field_simp [show p.Le ≠ 0 from by linarith, show t ≠ 0 from by linarith, show s ≠ 0 from by linarith, show (d : ℝ) ≠ 0 from by linarith]
    ring_nf
    rw [hs_sq]
    ring_nf
  rw [hLHS]
  rw [hrho]
  -- Goal: (725/8)*s*d*L²*(1+√10*s*t+s*t/(14500*L⁴))/t ≤ 2*725*d²*L³/1000
  -- Expand the left side into three terms
  have h_expand : (725 / 8) * s * (d : ℝ) * p.Le ^ 2 * (1 + Real.sqrt 10 * s * t + s * t / (14500 * p.Le ^ 4)) / t =
      (725 / 8) * s * (d : ℝ) * p.Le ^ 2 / t + (725 / 8) * Real.sqrt 10 * (d : ℝ) ^ 2 * p.Le ^ 2 + (725 / 8) * (d : ℝ) ^ 2 / (14500 * p.Le ^ 2) := by
    field_simp [show t ≠ 0 from by linarith, show p.Le ≠ 0 from by linarith]
    ring_nf
    rw [hs_sq]
    ring_nf
  rw [h_expand]
  -- Now bound each term
  have h_term1 : (725 / 8) * s * (d : ℝ) * p.Le ^ 2 / t ≤ (725 / 8) * (d : ℝ) ^ 2 * p.Le ^ 2 := by
    have h : s / t ≤ (d : ℝ) := by
      have hineq : s ≤ (d : ℝ) * t := by
        calc
          s ≤ (d : ℝ) := hs_le_d
          _ ≤ (d : ℝ) * t := by
            nlinarith
      calc
        s / t ≤ ((d : ℝ) * t) / t := by gcongr
        _ = (d : ℝ) := by field_simp [ht_pos.ne.symm]
    calc
      (725 / 8) * s * (d : ℝ) * p.Le ^ 2 / t = (725 / 8) * (d : ℝ) * p.Le ^ 2 * (s / t) := by ring
      _ ≤ (725 / 8) * (d : ℝ) * p.Le ^ 2 * (d : ℝ) := by gcongr
      _ = (725 / 8) * (d : ℝ) ^ 2 * p.Le ^ 2 := by ring
  have h_term2 : (725 / 8) * Real.sqrt 10 * (d : ℝ) ^ 2 * p.Le ^ 2 ≤ 287 * (d : ℝ) ^ 2 * p.Le ^ 2 := by
    calc
      (725 / 8) * Real.sqrt 10 * (d : ℝ) ^ 2 * p.Le ^ 2 = ((725 : ℝ) / 8 * Real.sqrt 10) * ((d : ℝ) ^ 2 * p.Le ^ 2) := by ring
      _ ≤ 287 * ((d : ℝ) ^ 2 * p.Le ^ 2) := by gcongr
      _ = 287 * (d : ℝ) ^ 2 * p.Le ^ 2 := by ring
  have h_term3 : (725 / 8) * (d : ℝ) ^ 2 / (14500 * p.Le ^ 2) ≤ (d : ℝ) ^ 2 * p.Le ^ 2 := by
    have h : (725 : ℝ) / 8 / (14500 * p.Le ^ 2) ≤ p.Le ^ 2 := by
      field_simp [show p.Le ≠ 0 from by linarith]
      have hL4 : 1 ≤ p.Le ^ 4 := by
        have h504sq : (504 : ℝ) ^ 2 = 254016 := by norm_num
        have hL_ge_504_sq : (504 : ℝ) ^ 2 ≤ p.Le ^ 2 := by nlinarith
        nlinarith
      nlinarith
    calc
      (725 / 8) * (d : ℝ) ^ 2 / (14500 * p.Le ^ 2) = ((725 : ℝ) / 8 / (14500 * p.Le ^ 2)) * (d : ℝ) ^ 2 := by ring
      _ ≤ p.Le ^ 2 * (d : ℝ) ^ 2 := by gcongr
      _ = (d : ℝ) ^ 2 * p.Le ^ 2 := by ring
  -- Sum the three bounds
  have h_sum : (725 / 8) * (d : ℝ) ^ 2 * p.Le ^ 2 + 287 * (d : ℝ) ^ 2 * p.Le ^ 2 + (d : ℝ) ^ 2 * p.Le ^ 2 ≤
      2 * 725 * (d : ℝ) ^ 2 * p.Le ^ 3 / 1000 := by
    have h_coeff : (725 : ℝ)/8 + 287 + 1 = 3029/8 := by ring
    have hL_ineq : 3029/8 ≤ (29/20) * p.Le := by
      have h_base : (3029 : ℝ)/8 ≤ (29/20) * (504 : ℝ) := by norm_num
      have h_mul : (29/20) * (504 : ℝ) ≤ (29/20) * p.Le := by gcongr
      linarith
    calc
      (725 / 8) * (d : ℝ) ^ 2 * p.Le ^ 2 + 287 * (d : ℝ) ^ 2 * p.Le ^ 2 + (d : ℝ) ^ 2 * p.Le ^ 2
          = ((725 : ℝ)/8 + 287 + 1) * (d : ℝ) ^ 2 * p.Le ^ 2 := by ring
      _ = (3029/8) * (d : ℝ) ^ 2 * p.Le ^ 2 := by rw [h_coeff]
      _ ≤ ((29/20) * p.Le) * (d : ℝ) ^ 2 * p.Le ^ 2 := by gcongr
      _ = (2*725/1000) * (d : ℝ) ^ 2 * p.Le ^ 3 := by ring
      _ = 2 * 725 * (d : ℝ) ^ 2 * p.Le ^ 3 / 1000 := by ring
  -- Combine all bounds
  have h_total : (725 / 8) * s * (d : ℝ) * p.Le ^ 2 / t + (725 / 8) * Real.sqrt 10 * (d : ℝ) ^ 2 * p.Le ^ 2 + (725 / 8) * (d : ℝ) ^ 2 / (14500 * p.Le ^ 2) ≤
      2 * 725 * (d : ℝ) ^ 2 * p.Le ^ 3 / 1000 := by
    linarith
  exact h_total

theorem cmp_ne (p : Df2OPar) (d n : ℕ) (H : RowHyp p d n) : 10 * p.eta / (p.eps * p.lam) ≤ p.rho / 10 ^ 6 := by
  have hLpos : 0 < p.Le := by
    have h504pos : (0 : ℝ) < 504 := by norm_num
    exact lt_of_lt_of_le h504pos H.L504
  have hdpos : 0 < (d : ℝ) := by
    have := H.hd
    exact_mod_cast this
  have hnpos : 0 < (n : ℝ) := by
    have := H.hn
    exact_mod_cast this
  have hsqrtdpos : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr hdpos
  have hsqrtnpos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnpos
  have hL_ge_504 : (504 : ℝ) ≤ p.Le := H.L504
  have hd_one : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast H.hd
  rw [H.eta, H.eps, H.lam, H.rho]
  -- Compute LHS = 1/(2 * p.Le^4) and RHS = 2*725*d^2*p.Le^3/10^6
  -- Show LHS ≤ 1 ≤ RHS
  have hLHS_le_one : 10 * (Real.sqrt (d : ℝ) / (p.Le * Real.sqrt (n : ℝ))) /
      ((20 * 725 * ((d : ℝ) * Real.sqrt (d : ℝ)) * p.Le ^ 5 / Real.sqrt (n : ℝ)) *
      (1 / (725 * (d : ℝ) * p.Le ^ 2))) ≤ 1 := by
    field_simp [hLpos.ne.symm, hdpos.ne.symm, hnpos.ne.symm,
      hsqrtdpos.ne.symm, hsqrtnpos.ne.symm]
    ring_nf
    -- Goal: 10^6 ≤ 2 * p.Le^4
    -- Since p.Le ≥ 504, p.Le^4 ≥ 504^4, and 2*504^4 > 10^6
    have hL4_ge : (504 : ℝ) ^ 4 ≤ p.Le ^ 4 := by
      have hpos : 0 ≤ (504 : ℝ) := by norm_num
      -- Use induction or repeated mul_le_mul
      have h1 : (504 : ℝ) ^ 1 ≤ p.Le ^ 1 := by simpa using hL_ge_504
      have h2 : (504 : ℝ) ^ 2 ≤ p.Le ^ 2 := by
        nlinarith
      have h3 : (504 : ℝ) ^ 3 ≤ p.Le ^ 3 := by
        nlinarith
      have h4 : (504 : ℝ) ^ 4 ≤ p.Le ^ 4 := by
        nlinarith
      exact h4
    have h_num : (10 : ℝ) ^ 6 ≤ 2 * ((504 : ℝ) ^ 4) := by
      norm_num
    nlinarith
  have hRHS_ge_one : 1 ≤ (2 * 725 * (d : ℝ) ^ 2 * p.Le ^ 3) / (10 : ℝ) ^ 6 := by
    refine (one_le_div ?_).mpr ?_
    · positivity
    -- Goal: 10^6 ≤ 2*725*d^2*p.Le^3
    -- Since d ≥ 1 and p.Le ≥ 504, RHS ≥ 2*725*1*504^3
    have hd_sq_ge_one : (1 : ℝ) ≤ (d : ℝ) ^ 2 := by
      nlinarith
    have hL3_ge : (504 : ℝ) ^ 3 ≤ p.Le ^ 3 := by
      have h1 : (504 : ℝ) ^ 1 ≤ p.Le ^ 1 := by simpa using hL_ge_504
      have h2 : (504 : ℝ) ^ 2 ≤ p.Le ^ 2 := by
        nlinarith
      have h3 : (504 : ℝ) ^ 3 ≤ p.Le ^ 3 := by
        nlinarith
      exact h3
    have h_num : (10 : ℝ) ^ 6 ≤ 2 * 725 * (1 : ℝ) * ((504 : ℝ) ^ 3) := by
      norm_num
    have h_product : 2 * 725 * (1 : ℝ) * ((504 : ℝ) ^ 3) ≤ 2 * 725 * (d : ℝ) ^ 2 * p.Le ^ 3 := by
      nlinarith
    nlinarith
  -- Now combine: LHS ≤ 1 ≤ RHS
  have hLHS : 10 * (Real.sqrt (d : ℝ) / (p.Le * Real.sqrt (n : ℝ))) /
      ((20 * 725 * ((d : ℝ) * Real.sqrt (d : ℝ)) * p.Le ^ 5 / Real.sqrt (n : ℝ)) *
      (1 / (725 * (d : ℝ) * p.Le ^ 2))) ≤ 1 := hLHS_le_one
  have hRHS : 1 ≤ (2 * 725 * (d : ℝ) ^ 2 * p.Le ^ 3) / (10 : ℝ) ^ 6 := hRHS_ge_one
  linarith

theorem cmp_thn (p : Df2OPar) (d n : ℕ) (H : RowHyp p d n) : df2ThN p d n ≤ 1 / 100 := by
  have hd_real : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast H.hd
  have hn_real : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast H.hn
  have hL_ge_504 : (504 : ℝ) ≤ p.Le := H.L504
  have hL_pos : 0 < p.Le := by linarith
  have hd_nonneg : 0 ≤ (d : ℝ) := by linarith
  have hd_pos : (d : ℝ) ≠ 0 := by linarith
  let s := Real.sqrt (d : ℝ)
  let t := Real.sqrt (n : ℝ)
  have hs_pos : 0 < s := Real.sqrt_pos.mpr (by linarith)
  have ht_pos : 0 < t := Real.sqrt_pos.mpr (by linarith)
  have hs_ge_one : (1 : ℝ) ≤ s := by
    have h1sq_le_d : (1 : ℝ) ^ 2 ≤ (d : ℝ) := by nlinarith
    calc
      (1 : ℝ) = Real.sqrt ((1 : ℝ) ^ 2) := by norm_num
      _ ≤ Real.sqrt (d : ℝ) := Real.sqrt_le_sqrt h1sq_le_d
  have ht_ge_one : (1 : ℝ) ≤ t := by
    have h1sq_le_n : (1 : ℝ) ^ 2 ≤ (n : ℝ) := by nlinarith
    calc
      (1 : ℝ) = Real.sqrt ((1 : ℝ) ^ 2) := by norm_num
      _ ≤ Real.sqrt (n : ℝ) := Real.sqrt_le_sqrt h1sq_le_n
  have hsq_s : s ^ 2 = (d : ℝ) := Real.sq_sqrt hd_nonneg
  have h_sqrt10_le_4 : Real.sqrt (10 : ℝ) ≤ 4 := by
    calc
      Real.sqrt (10 : ℝ) ≤ Real.sqrt (16 : ℝ) := Real.sqrt_le_sqrt (by norm_num)
      _ = 4 := by norm_num
  -- η * λ * L² = 1/(725 * s * L * t)
  have h_eta_lam_L2 : p.eta * p.lam * p.Le ^ 2 = 1 / (725 * s * p.Le * t) := by
    rw [H.eta, H.lam]
    dsimp [s, t]
    field_simp [hL_pos.ne.symm, hs_pos.ne.symm, ht_pos.ne.symm]
    nlinarith [hsq_s]
  -- df2ThN = 2 * η * λ * L² * (1 + √(10 d n) + d² L/ε)
  have h_expr : df2ThN p d n = 2 * (p.eta * p.lam * p.Le ^ 2) *
      (1 + Real.sqrt (10 * (d : ℝ) * (n : ℝ)) + (d : ℝ) ^ 2 * p.Le / p.eps) := by
    rw [df2ThN, df2Bn]
    ring
  rw [h_expr, h_eta_lam_L2]
  -- Expand
  have h_expand : 2 * (1 / (725 * s * p.Le * t)) * (1 + Real.sqrt (10 * (d : ℝ) * (n : ℝ)) + (d : ℝ) ^ 2 * p.Le / p.eps) =
      2 / (725 * s * p.Le * t) + 2 * Real.sqrt (10 * (d : ℝ) * (n : ℝ)) / (725 * s * p.Le * t) + 2 * (d : ℝ) ^ 2 * p.Le / (p.eps * 725 * s * p.Le * t) := by
    ring
  rw [h_expand]
  -- Key bounds
  have h_sqrt10_div_L : Real.sqrt (10 : ℝ) / p.Le ≤ 4 / 504 := by
    have h1 : Real.sqrt (10 : ℝ) / p.Le ≤ 4 / p.Le := by
      gcongr
    have h2 : 4 / p.Le ≤ 4 / 504 := by
      have h_one_div : 1 / p.Le ≤ 1 / 504 :=
        (one_div_le_one_div hL_pos (by norm_num : 0 < (504 : ℝ))).mpr hL_ge_504
      have h := mul_le_mul_of_nonneg_left h_one_div (by norm_num : 0 ≤ (4 : ℝ))
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h
    linarith
  have h_prod_denom : (504 : ℝ) ≤ s * p.Le * t := by
    -- 504 = 504*1*1 ≤ p.Le * s * t = s*p.Le*t
    -- First: 1*1 ≤ s*t
    have h_st : (1 : ℝ) * 1 ≤ s * t :=
      mul_le_mul hs_ge_one ht_ge_one (by positivity) (by positivity)
    -- Then: 504*(1*1) ≤ p.Le*(s*t)
    have h_total : (504 : ℝ) * ((1 : ℝ) * 1) ≤ p.Le * (s * t) :=
      mul_le_mul hL_ge_504 h_st (by positivity) (by positivity)
    -- Simplify both sides
    simpa [mul_comm, mul_left_comm, mul_assoc] using h_total
  have h_denom_bound : (725 * 504 : ℝ) ≤ 725 * s * p.Le * t := by nlinarith
  -- Term 1 bound
  have hT1 : 2 / (725 * s * p.Le * t) ≤ 2 / (725 * 504) := by
    have hpos : 0 < 725 * s * p.Le * t := by positivity
    have hpos' : 0 < 725 * (504 : ℝ) := by norm_num
    have h := (one_div_le_one_div hpos hpos').mpr h_denom_bound
    have h' := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ (2 : ℝ))
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h'
  -- Term 2 bound
  have hT2 : 2 * Real.sqrt (10 * (d : ℝ) * (n : ℝ)) / (725 * s * p.Le * t) ≤ 8 / (725 * 504) := by
    have h_sqrt : Real.sqrt (10 * (d : ℝ) * (n : ℝ)) = Real.sqrt (10 : ℝ) * s * t := by
      calc
        Real.sqrt (10 * (d : ℝ) * (n : ℝ)) = Real.sqrt ((10 : ℝ) * ((d : ℝ) * (n : ℝ))) := by ring_nf
        _ = Real.sqrt (10 : ℝ) * Real.sqrt ((d : ℝ) * (n : ℝ)) := by rw [Real.sqrt_mul (by norm_num : 0 ≤ (10 : ℝ))]
        _ = Real.sqrt (10 : ℝ) * (Real.sqrt (d : ℝ) * Real.sqrt (n : ℝ)) := by rw [Real.sqrt_mul hd_nonneg]
        _ = Real.sqrt (10 : ℝ) * s * t := by dsimp [s, t]; ring
    rw [h_sqrt]
    have h_simp : 2 * (Real.sqrt (10 : ℝ) * s * t) / (725 * s * p.Le * t) = 2 * Real.sqrt (10 : ℝ) / (725 * p.Le) := by
      field_simp [hs_pos.ne.symm, ht_pos.ne.symm, hL_pos.ne.symm]
    rw [h_simp]
    calc
      2 * Real.sqrt (10 : ℝ) / (725 * p.Le) = (2 / 725) * (Real.sqrt (10 : ℝ) / p.Le) := by ring
      _ ≤ (2 / 725) * (4 / 504) := by
        apply mul_le_mul_of_nonneg_left h_sqrt10_div_L
        norm_num
      _ = 8 / (725 * 504) := by ring
  -- Term 3 bound
  have hT3 : 2 * (d : ℝ) ^ 2 * p.Le / (p.eps * 725 * s * p.Le * t) ≤ 2 / (725 * 504) := by
    rw [H.eps]
    -- Simplify LHS to 2/(20*725²*L⁵)
    have h_simp : 2 * (d : ℝ) ^ 2 * p.Le / ((20 * 725 * (d : ℝ) * s * p.Le ^ 5 / t) * 725 * s * p.Le * t) =
        2 / (20 * 725 ^ 2 * p.Le ^ 5) := by
      field_simp [hL_pos.ne.symm, hs_pos.ne.symm, ht_pos.ne.symm, hd_pos]
      nlinarith [hsq_s]
    -- The goal has (d*s) form; use ring to match
    have h_goal_eq : 2 * (d : ℝ) ^ 2 * p.Le / ((20 * 725 * (d : ℝ) * s * p.Le ^ 5 / t) * 725 * s * p.Le * t) ≤ 2 / (725 * 504) := by
      rw [h_simp]
      -- 2/(20*725²*L⁵) ≤ 2/(725*504)
      have hL1 : (1 : ℝ) ≤ p.Le := by linarith
      have hL5 : (1 : ℝ) ≤ p.Le ^ 5 := by
        have h2 : (1 : ℝ) ≤ p.Le ^ 2 := by nlinarith
        have h3 : (1 : ℝ) ≤ p.Le ^ 3 := by nlinarith
        have h4 : (1 : ℝ) ≤ p.Le ^ 4 := by nlinarith
        nlinarith
      have h_ineq : (725 * 504 : ℝ) ≤ 20 * 725 ^ 2 * p.Le ^ 5 := by nlinarith
      have hpos : 0 < 20 * 725 ^ 2 * p.Le ^ 5 := by positivity
      have hpos' : 0 < 725 * (504 : ℝ) := by norm_num
      have h := (one_div_le_one_div hpos hpos').mpr h_ineq
      have h' := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ (2 : ℝ))
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h'
    simpa [s, t, mul_assoc] using h_goal_eq
  -- Sum
  have h_sum : 2 / (725 * s * p.Le * t) + 2 * Real.sqrt (10 * (d : ℝ) * (n : ℝ)) / (725 * s * p.Le * t) +
      2 * (d : ℝ) ^ 2 * p.Le / (p.eps * 725 * s * p.Le * t) ≤ 12 / (725 * 504) := by
    linarith
  have h_final : 12 / (725 * 504 : ℝ) ≤ 1 / 100 := by norm_num
  linarith

theorem cmp_inc (p : Df2OPar) (d n : ℕ) (H : RowHyp p d n) :
    16 * p.c1 * p.rho * p.Le * p.lam ^ 2 ≤ 36 / 100 := by
  rw [H.c1, H.rho, H.lam]
  have hdpos : (d : ℝ) ≠ 0 := by
    have h : 1 ≤ (d : ℝ) := by exact_mod_cast H.hd
    linarith
  have hLepos : 0 < p.Le := by linarith [H.L504]
  field_simp [hdpos, hLepos.ne.symm]
  norm_num

/-! ### Assembly -/

namespace RowHyp

variable {p : Df2OPar} {d n : ℕ}

theorem L_pos (H : RowHyp p d n) : 0 < p.Le := by linarith [H.L504]

theorem d_pos (H : RowHyp p d n) : (0 : ℝ) < d := by have := H.hd; exact_mod_cast (by omega : 0 < d)

theorem lam_pos (H : RowHyp p d n) : 0 < p.lam := by
  have := H.L_pos; have := H.d_pos; rw [H.lam]; positivity

theorem trace_eq (H : RowHyp p d n) : d * p.Le / p.lam = p.rho / 2 := by
  have := H.L_pos; have := H.d_pos
  rw [H.lam, H.rho]; field_simp

theorem devK_eq (_H : RowHyp p d n) :
    p.eta * df2DevK p d n = p.eta * df2B1 p d n + p.eta * df2Bn p d n / (8 * p.Le * p.lam ^ 2) := by
  unfold df2DevK; ring

theorem dev_eq (H : RowHyp p d n) :
    p.eta * df2Dev p d n = p.eta * df2B1 p d n + 2 * (p.eta * df2Bn p d n / (8 * p.Le * p.lam ^ 2)) := by
  have := H.L_pos; have := H.lam_pos
  unfold df2Dev; field_simp; ring

theorem devP_eq (H : RowHyp p d n) : df2DevP p d n = p.eta * df2Bn p d n / (8 * p.Le * p.lam ^ 2) := by
  have := H.L_pos; have := H.lam_pos
  unfold df2DevP; rw [H.kap]; field_simp; ring

end RowHyp

theorem rows_of (p : Df2OPar) (d n : ℕ) (H : RowHyp p d n) : Df2Rows p d n := by
  have hL := H.L_pos
  have hd := H.d_pos
  have hρ : 0 < p.rho := by rw [H.rho]; positivity
  have h1 := cmp_one p d n H
  have hη1 := row_eta_le p d n H
  have hpri := cmp_pri p d n H
  have hstab := cmp_stab p d n H
  have hb1 := cmp_b1 p d n H
  have hbn := cmp_bn p d n H
  have hne := cmp_ne p d n H
  have hthn := cmp_thn p d n H
  have hinc := cmp_inc p d n H
  have htr := H.trace_eq
  have hK := H.devK_eq
  have hD := H.dev_eq
  have hP := H.devP_eq
  have hθ := H.theta; have hα := H.alpha; have hc1 := H.c1; have hγ := H.gam
  have hepos : 0 < p.eps := by rw [H.eps]; have := Real.sqrt_pos.2 (show (0 : ℝ) < n by exact_mod_cast H.hn); positivity
  exact {
    pos_de := H.de_pos
    de_lt := H.de_lt
    pos_lam := H.lam_pos
    lam_le := by
      rw [H.lam, div_le_iff₀ (by positivity)]
      have : (504 : ℝ) ^ 2 ≤ p.Le ^ 2 := pow_le_pow_left₀ (by norm_num) H.L504 2
      have : (1 : ℝ) ≤ d := by exact_mod_cast H.hd
      nlinarith
    pos_eta := by rw [H.eta]; have := Real.sqrt_pos.2 hd; have := Real.sqrt_pos.2 (show (0 : ℝ) < n by exact_mod_cast H.hn); positivity
    eta_le := hη1
    pos_sig2 := by rw [H.sig2]; positivity
    pos_rho := hρ
    pos_eps := hepos
    eps_le := H.eps_le
    one_le_R := row_one_le_R p d n H
    k0_le := row_k0_le p d n H
    r1 := row_r1 p d n H
    r2 := by rw [H.sig2]; rw [mul_one_div, div_le_one (by positivity)]; linarith [H.L504]
    r3 := by rw [H.sig2]; unfold df2C0; field_simp; norm_num
    r4 := row_r4 p d n H
    r5p := row_r5p p d n H
    r6 := row_r6 p d n H
    r6a := row_r6a p d n H
    r6b := row_r6b p d n H
    r7 := row_r7 p d n H
    r8 := row_r8 p d n H
    r11 := by rw [H.lam]; apply one_div_le_one_div_of_le (by positivity); nlinarith
    r12 := by linarith
    r14 := row_r14 p d n H
    r15p := by unfold df2C0 df2Cg; norm_num
    r17 := by rw [H.kap]; unfold df2C0; norm_num
    r19o := by rw [hK]; linarith
    r20 := by rw [hP, hγ]; linarith
    r21 := by linarith
    r22 := by rw [hD, hθ, hα]; linarith
    r24o := by rw [hK, hD, hP, hθ, hc1, hγ]; linarith
    r24b := by rw [hK, hD, hP, hθ, hc1, hγ]; linarith
    c22 := row_c22 p d n H
    c8 := row_c8 p d n H
    c16 := row_c16 p d n H
    c4 := row_c4 p d n H
    cnu := row_cnu p d n H
    c2dl := row_c2dl p d n H
    c500 := row_c500 p d n H
    cx := H.cx
    clg := row_clg p d n H
    cz := row_cz p d n H }

/-- The parameters of the learner in the regime satisfy `RowHyp`. -/
theorem rowHyp_of (d n : ℕ) (δ : ℝ) (hd : 1 ≤ d) (hn : 1 ≤ n) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (heps : (df2oPar d n δ).eps ≤ 1 / 2) : RowHyp (df2oPar d n δ) d n := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hdn : (1 : ℝ) ≤ (d : ℝ) * n := by nlinarith
  set δ1 := min (δ / 3) (Real.exp (-14) / ((d : ℝ) * n) ^ 3) with hδ1def
  have hδ1e : (df2oPar d n δ).δ1 = δ1 := rfl
  have hδe : (df2oPar d n δ).δe = 4 * δ1 / (5 * n) := rfl
  have hδ1pos : 0 < δ1 := lt_min (by positivity) (by positivity)
  have hδ1le : δ1 ≤ Real.exp (-14) / ((d : ℝ) * n) ^ 3 := min_le_right _ _
  have hδ1le' : δ1 ≤ δ / 3 := min_le_left _ _
  have hde : 0 < (df2oPar d n δ).δe := by rw [hδe]; positivity
  have hdsmall : (df2oPar d n δ).δe * ((d : ℝ) * n) ^ 3 * n ≤ Real.exp (-14) := by
    rw [hδe]
    have h3 : δ1 * ((d : ℝ) * n) ^ 3 ≤ Real.exp (-14) := by
      rwa [le_div_iff₀ (by positivity)] at hδ1le
    have : 4 * δ1 / (5 * n) * ((d : ℝ) * n) ^ 3 * n = 4 / 5 * (δ1 * ((d : ℝ) * n) ^ 3) := by
      field_simp
    rw [this]
    have := Real.exp_pos (-14)
    linarith
  have hcx : 14 + 3 * Real.log ((d : ℝ) * n) ≤ Real.log (1 / (df2oPar d n δ).δe) := by
    have hpos : 0 < Real.exp 14 * ((d : ℝ) * n) ^ 3 := by positivity
    have hle : Real.exp 14 * ((d : ℝ) * n) ^ 3 ≤ 1 / (df2oPar d n δ).δe := by
      rw [le_div_iff₀ hde]
      have := hdsmall
      have e1 : Real.exp 14 * Real.exp (-14) = 1 := by rw [← Real.exp_add]; norm_num
      have h2 : (df2oPar d n δ).δe * ((d : ℝ) * n) ^ 3 ≤ (df2oPar d n δ).δe * ((d : ℝ) * n) ^ 3 * n := by
        have : 0 ≤ (df2oPar d n δ).δe * ((d : ℝ) * n) ^ 3 := by positivity
        nlinarith
      have h4 : Real.exp 14 * ((df2oPar d n δ).δe * ((d : ℝ) * n) ^ 3) ≤ Real.exp 14 * Real.exp (-14) :=
        mul_le_mul_of_nonneg_left (h2.trans hdsmall) (Real.exp_pos 14).le
      nlinarith
    have := Real.log_le_log hpos hle
    rwa [Real.log_mul (Real.exp_pos 14).ne' (by positivity), Real.log_exp, Real.log_pow] at this
  have hlogdn : 0 ≤ Real.log ((d : ℝ) * n) := Real.log_nonneg hdn
  have hL : (df2oPar d n δ).Le = 36 * Real.log (1 / (df2oPar d n δ).δe) := rfl
  have hepsv : (df2oPar d n δ).eps =
      20 * 725 * (d * Real.sqrt d) * (df2oPar d n δ).Le ^ 5 / Real.sqrt n := rfl
  have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by linarith)
  refine
    { hd := hd
      hn := hn
      de_pos := hde
      de_lt := ?_
      Le := hL
      L504 := by rw [hL]; linarith
      cx := hcx
      dsmall := hdsmall
      lam := rfl
      eta := rfl
      sig2 := rfl
      rho := rfl
      eps := hepsv
      eps_le := heps
      reg := ?_
      kap := rfl
      theta := rfl
      alpha := rfl
      c1 := rfl
      gam := rfl
      k0 := rfl
      R := rfl
      hlog := ?_ }
  · rw [hδe, div_lt_one (by positivity)]; linarith
  · rw [hepsv, div_le_iff₀ hsn] at heps; linarith
  · refine le_trans ?_ hcx
    have h4 : Real.log (2 * d + 2) ≤ Real.log (4 * d) := Real.log_le_log (by positivity) (by linarith)
    rw [Real.log_mul (by norm_num) (by positivity)] at h4
    have hl4 : Real.log 4 < 14 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num); linarith
    have hld : Real.log d ≤ Real.log ((d : ℝ) * n) := Real.log_le_log (by positivity) (by nlinarith)
    linarith

end Layer2

/-- The rows hold at the parameters of the learner in the regime. -/
theorem df2RowsHold : Df2RowsHold := fun d n δ hd hn hδ0 hδ1 heps =>
  Layer2.rows_of _ d n (Layer2.rowHyp_of d n δ hd hn hδ0 hδ1 heps)

end AdversarialBco.Poly
