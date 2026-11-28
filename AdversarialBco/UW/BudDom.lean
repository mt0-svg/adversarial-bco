/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.UW.ParamT4U

@[expose] public section

/-!
# Theorem UW: DOM-W

(C4) to (C7): in the regime of the reference, `c̄_w (1 + Ξ_{w1}²) ≤ 1.75·10^{-35}` with
`c̄_w = κ_c y0`, `κ_c = η κ λ κ₀` at T4U and `Ξ_{w1} = (b0 + 1)^{1/2} + 2^{-p-1} + 1`. The proof reads only the upper
ends of the brackets of `b0` and `y0`, `ε(u) ≤ 1/4`, `u ≥ 1`, `L = 36 ln N_0 ≥ 17467` (`regW_Le`) and `p ≥ 160`:
with `s = L^{1/2} ≥ 132.16`, `η y0 ≤ (83 + 10 s)/(58000 d L^6)` (`η = ε/(14500 d L^6 u)`), `κ λ κ₀ ≤ 1.0001/(2900 d L²)`
and `1 + Ξ_{w1}² ≤ 4.002 d + s² + 2.002 s + 10.007`, and the product is at most
`1.0001 (83 + 10 s)(s² + 2.002 s + 14.009)/(1.682·10^8 d s^{16}) ≤ 1.75·10^{-35}` (`dom_poly`).
-/

namespace AdversarialBco.UW

open AdversarialBco.Poly
open AdversarialBco.Unified.BLO (NeO kDel parO parN)

/-- The constant step of DOM-W: for `d ≥ 1` and `s ≥ 132.16`,
`1.0001 (83 + 10 s)(4.002 d + s² + 2.002 s + 10.007) ≤ 1.75·10^{-35} · 1.682·10^8 d² s^{16}`. -/
theorem dom_poly (d s : ℝ) (hd : 1 ≤ d) (hs : 13216 / 100 ≤ s) :
    (83 + 10 * s) * (10001 / 10000) * (4002 / 1000 * d + s ^ 2 + 2002 / 1000 * s + 10007 / 1000) ≤
      1.75e-35 * 168200000 * d ^ 2 * s ^ 16 := by
  have hs0 : 0 ≤ s := by linarith
  have hA : 0 ≤ 83 + 10 * s := by linarith
  have h1 : 4002 / 1000 * d + s ^ 2 + 2002 / 1000 * s + 10007 / 1000 ≤
      d * (s ^ 2 + 2002 / 1000 * s + 14009 / 1000) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hd) (add_nonneg (sq_nonneg s) hs0)]
  have h2 : d ≤ d ^ 2 := by nlinarith
  have h3 : (83 + 10 * s) * (10001 / 10000) * (s ^ 2 + 2002 / 1000 * s + 14009 / 1000) ≤ 1081 / 100 * s ^ 3 := by
    have hc : 0 ≤ s - 13216 / 100 := by linarith
    nlinarith [mul_nonneg hc (sq_nonneg s), mul_nonneg hc hs0, sq_nonneg s]
  have h4 : (1081 / 100 : ℝ) * s ^ 3 ≤ 1.75e-35 * 168200000 * s ^ 16 := by
    have h13 : (13216 / 100 : ℝ) ^ 13 ≤ s ^ 13 := pow_le_pow_left₀ (by norm_num) hs 13
    have hc : (1081 / 100 : ℝ) ≤ 1.75e-35 * 168200000 * (13216 / 100) ^ 13 := by norm_num
    have hs3 : 0 ≤ s ^ 3 := by positivity
    calc (1081 / 100 : ℝ) * s ^ 3 ≤ 1.75e-35 * 168200000 * (13216 / 100) ^ 13 * s ^ 3 :=
          mul_le_mul_of_nonneg_right hc hs3
      _ ≤ 1.75e-35 * 168200000 * s ^ 13 * s ^ 3 := by gcongr
      _ = 1.75e-35 * 168200000 * s ^ 16 := by ring
  have hQ : 0 ≤ s ^ 2 + 2002 / 1000 * s + 14009 / 1000 := by positivity
  have hd0 : 0 ≤ d := by linarith
  calc (83 + 10 * s) * (10001 / 10000) * (4002 / 1000 * d + s ^ 2 + 2002 / 1000 * s + 10007 / 1000)
      ≤ (83 + 10 * s) * (10001 / 10000) * (d * (s ^ 2 + 2002 / 1000 * s + 14009 / 1000)) := by gcongr
    _ = d * ((83 + 10 * s) * (10001 / 10000) * (s ^ 2 + 2002 / 1000 * s + 14009 / 1000)) := by ring
    _ ≤ d * (1081 / 100 * s ^ 3) := by gcongr
    _ ≤ d ^ 2 * (1081 / 100 * s ^ 3) := by gcongr
    _ ≤ d ^ 2 * (1.75e-35 * 168200000 * s ^ 16) := by gcongr
    _ = 1.75e-35 * 168200000 * d ^ 2 * s ^ 16 := by ring

/-- `36 Λ_0 = L`. -/
theorem lam0_Le (d n : ℕ) : 36 * lam0 d n = Bit.PieceA.Le d n := rfl

/-- BL-O's precision is at least `160`. -/
theorem parO_p_ge (d n : ℕ) (δ : ℚ) : 160 ≤ (parO d n δ).p := by
  show 160 ≤ 10 * (NeO d n (kDel δ)).size + 16 * d.size + 160
  omega

theorem two_pow_small {k : ℕ} (hk : 10 ≤ k) : (1 : ℝ) / 2 ^ k ≤ 1 / 1000 := by
  have : (2 : ℝ) ^ 10 ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hk
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  linarith

/-- DOM-W on plain reals: the constant chain of (C4) to (C7). -/
theorem dom_real (d L u eps eta lam k0 y0 b0 t : ℝ) (hd : 1 ≤ d) (hL : 17467 ≤ L) (hu : 1 ≤ u) (heps0 : 0 < eps)
    (heps : eps ≤ 1 / 4) (hEta : eta = eps / (14500 * d * L ^ 6 * u)) (hlam : lam = 1 / (725 * d * L ^ 2))
    (hk0 : k0 = ((1 - lam) ^ 2)⁻¹) (hy0 : y0 ≤ 11 + 18 / eps + 10 * Real.sqrt L) (hy00 : 0 ≤ y0)
    (hb0 : b0 + 1 ≤ 2 * d + L + 4) (hb00 : 0 ≤ b0 + 1) (ht0 : 0 ≤ t) (ht : t ≤ 1 / 1000) :
    eta * (1 / 4) * lam * k0 * y0 * (1 + (Real.sqrt (b0 + 1) + t + 1) ^ 2) ≤ 1.75e-35 := by
  have hd0 : (0 : ℝ) < d := by linarith
  have hu0 : (0 : ℝ) < u := by linarith
  have hL0 : 0 < L := by linarith
  set s := Real.sqrt L with hsdef
  have hs : 13216 / 100 ≤ s := by
    rw [hsdef, show (13216 / 100 : ℝ) = Real.sqrt ((13216 / 100) ^ 2) by
      rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hs0 : 0 ≤ s := by linarith
  have hsL : s ^ 2 = L := Real.sq_sqrt hL0.le
  -- `η y0 ≤ (83 + 10 s)/(58000 d s^{12})`
  have hL6 : L ^ 6 = s ^ 12 := by rw [← hsL]; ring
  have hD0 : 0 < 14500 * d * s ^ 12 * u := by positivity
  have h1 : eps * y0 ≤ eps * (11 + 10 * s) + 18 := by
    have := mul_le_mul_of_nonneg_left hy0 heps0.le
    rw [mul_add, mul_add, mul_div_cancel₀ _ heps0.ne'] at this
    linarith
  have h2 : eps * (11 + 10 * s) + 18 ≤ (83 + 10 * s) / 4 := by nlinarith
  have hEY : eta * y0 ≤ (83 + 10 * s) / (58000 * d * s ^ 12) := by
    rw [hEta, hL6, div_mul_eq_mul_div, div_le_div_iff₀ hD0 (by positivity)]
    have h4 : (83 + 10 * s) / 4 * (58000 * d * s ^ 12) ≤ (83 + 10 * s) * (14500 * d * s ^ 12 * u) := by
      have h5 : 0 ≤ (83 + 10 * s) * (14500 * d * s ^ 12) := by positivity
      have e : (83 + 10 * s) * (14500 * d * s ^ 12 * u) - (83 + 10 * s) / 4 * (58000 * d * s ^ 12) =
          (83 + 10 * s) * (14500 * d * s ^ 12) * (u - 1) := by ring
      have := mul_nonneg h5 (sub_nonneg.mpr hu)
      linarith
    calc eps * y0 * (58000 * d * s ^ 12) ≤ (83 + 10 * s) / 4 * (58000 * d * s ^ 12) := by
          gcongr; exact h1.trans h2
      _ ≤ _ := h4
  -- `κ λ κ₀ ≤ 1.0001/(2900 d s^4)`
  have hL2 : L ^ 2 = s ^ 4 := by rw [← hsL]; ring
  have hlam1 : lam ≤ 1 / 10 ^ 11 := by
    rw [hlam, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hlam0 : 0 < lam := by rw [hlam]; positivity
  have hk1 : k0 ≤ 10001 / 10000 := by
    rw [hk0]
    have h1 : (10000 / 10001 : ℝ) ≤ (1 - lam) ^ 2 := by nlinarith
    calc ((1 - lam) ^ 2)⁻¹ ≤ (10000 / 10001 : ℝ)⁻¹ := inv_anti₀ (by norm_num) h1
      _ = 10001 / 10000 := by norm_num
  have hk00 : 0 ≤ k0 := by rw [hk0]; positivity
  have hKL : 1 / 4 * lam * k0 ≤ 10001 / 10000 / (2900 * d * s ^ 4) := by
    rw [hlam, hL2]
    calc 1 / 4 * (1 / (725 * d * s ^ 4)) * k0 = k0 / (2900 * d * s ^ 4) := by
          field_simp; ring
      _ ≤ 10001 / 10000 / (2900 * d * s ^ 4) := by gcongr
  -- `1 + Ξ_{w1}² ≤ 4.002 d + s² + 2.002 s + 10.007`
  set X := Real.sqrt (b0 + 1) with hXdef
  have hX0 : 0 ≤ X := Real.sqrt_nonneg _
  have hX2 : X ^ 2 = b0 + 1 := Real.sq_sqrt hb00
  have hX : X ≤ d + 2 + s := by
    rw [hXdef]
    calc Real.sqrt (b0 + 1) ≤ Real.sqrt ((d + 2 + s) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
      _ = d + 2 + s := Real.sqrt_sq (by positivity)
  have hXi : 1 + (X + t + 1) ^ 2 ≤ 4002 / 1000 * d + s ^ 2 + 2002 / 1000 * s + 10007 / 1000 := by
    have e : 1 + (X + t + 1) ^ 2 = 1 + X ^ 2 + 2 * X * (1 + t) + (1 + t) ^ 2 := by ring
    rw [e, hX2]
    have ht1 : 1 + t ≤ 1001 / 1000 := by linarith
    have ht2 : 0 ≤ 1 + t := by linarith
    have h1 : X * (1 + t) ≤ (d + 2 + s) * (1001 / 1000) := mul_le_mul hX ht1 ht2 (by positivity)
    have h2 : (1 + t) ^ 2 ≤ (1001 / 1000) ^ 2 := pow_le_pow_left₀ ht2 ht1 2
    have h3 : b0 + 1 ≤ 2 * d + s ^ 2 + 4 := by rw [hsL]; exact hb0
    linarith
  -- the product
  have hEY0 : 0 ≤ eta * y0 := by rw [hEta]; positivity
  have hKL0 : 0 ≤ 1 / 4 * lam * k0 := by positivity
  have hmain : eta * (1 / 4) * lam * k0 * y0 * (1 + (X + t + 1) ^ 2) ≤
      (83 + 10 * s) / (58000 * d * s ^ 12) * (10001 / 10000 / (2900 * d * s ^ 4)) *
        (4002 / 1000 * d + s ^ 2 + 2002 / 1000 * s + 10007 / 1000) := by
    calc eta * (1 / 4) * lam * k0 * y0 * (1 + (X + t + 1) ^ 2) =
        (eta * y0) * (1 / 4 * lam * k0) * (1 + (X + t + 1) ^ 2) := by ring
      _ ≤ _ := by
        apply mul_le_mul (mul_le_mul hEY hKL hKL0 (by positivity)) hXi (by positivity) (by positivity)
  refine hmain.trans ?_
  have key := dom_poly d s hd hs
  rw [show (83 + 10 * s) / (58000 * d * s ^ 12) * (10001 / 10000 / (2900 * d * s ^ 4)) *
      (4002 / 1000 * d + s ^ 2 + 2002 / 1000 * s + 10007 / 1000) =
      (83 + 10 * s) * (10001 / 10000) * (4002 / 1000 * d + s ^ 2 + 2002 / 1000 * s + 10007 / 1000) /
        (168200000 * d ^ 2 * s ^ 16) by field_simp; ring]
  rw [div_le_iff₀ (by positivity)]
  linarith

/-- **DOM-W** (C7). -/
theorem domW : DomW := by
  intro d n δ ρ _ _ _ hR
  have hd : (1 : ℝ) ≤ d := by exact_mod_cast hR.hd
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast hR.hn
  have hu0 : (0 : ℝ) < ρ.u := by linarith [hR.hu]
  have hL : 17467 ≤ Bit.PieceA.Le d n := regW_Le hR.hd hR.hn hR.hu hR.heps
  have hL0 : 0 < Bit.PieceA.Le d n := by linarith
  have heps0 : 0 < (parW d n ρ.u).eps := by
    rw [parW_eps, Bit.PieceA.eps]
    have := Real.sqrt_pos.mpr (show (0 : ℝ) < n by linarith)
    have := Real.sqrt_pos.mpr (show (0 : ℝ) < d by linarith)
    have := Real.sqrt_pos.mpr hu0
    positivity
  have hy00 : 0 ≤ ρ.y0 := by
    have h := hR.y0_lo
    have : 0 ≤ 18 / (parW d n ρ.u).eps := by positivity
    have : 0 ≤ Real.sqrt (12 * lam0 d n) := Real.sqrt_nonneg _
    linarith
  have hy0 := hR.y0_hi
  rw [lam0_Le] at hy0
  have hb0 := hR.b0_hi
  rw [lam0_Le] at hb0
  have hb00 := hR.b0_lo
  rw [lam0_Le] at hb00
  have ht := two_pow_small (k := (parO d n δ).p + 1) (by have := parO_p_ge d n δ; omega)
  have h := dom_real d (Bit.PieceA.Le d n) ρ.u (parW d n ρ.u).eps (parW d n ρ.u).eta (parW d n ρ.u).lam
    (parW d n ρ.u).k0 ρ.y0 ρ.b0 (1 / 2 ^ ((parO d n δ).p + 1)) hd hL hR.hu heps0 hR.heps
    (parW_eta_eps hR.hd hR.hn hu0 hL0) (parW_lam d n ρ.u) (parW_k0 d n ρ.u) hy0 hy00 (by linarith) (by linarith)
    (by positivity) ht
  rwa [parW_kap]

end AdversarialBco.UW
