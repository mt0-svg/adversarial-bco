/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.BudEncMaj

@[expose] public section

/-!
# Lemma ENC-W: the fields of PARAM-W that read the root of `u'`

Unified/BudEncR.lean and BudEncMaj.lean: over Theorem U's abstract record `EncR` at the floor
(`N_e := N_0`, `Le := L_f`; UW/BudEncW.lean, `encF`), BL-OW's `ε'`, `η'` and `κ_c'` carry the root `r_u = sqrtDn_q u'`:
`ε' = up_{pF}(14500 d (r_d + 2^{-q}) L_f⁺^5 (r_u + 2^{-q})/r_n)`, `η' = rnd_{pF}(r_d/(L_f' r_n r_u))`, `κ_c' =
rnd_{pF}(η' λ'/(4 (1 - λ')²))`, against the reference's `ε(u) = ε u^{1/2}`, `η(u) = η/u^{1/2}`, `κ_c(u) = η(u) λ/(4 (1 -
λ)²)`. With `r_u ≤ u^{1/2} ≤ r_u + 2^{-q}`, `1 ≤ r_u` and the precision `2^{-pF} N u^{1/2} ≤ 2^{-p-40}` (`hEu`, read at
the level: `u^{1/2} ≤ N_e`), they keep Lemma ENC's bounds: `ε(u) ≤ ε' ≤ ε(u) (1 + 2^{-p-4})`, `|η'/η(u) - 1| ≤
2^{-p-16}`, `|κ_c'/κ_c(u) - 1| ≤ 2^{-p-4}`. This file depends on Mathlib only.
-/

namespace AdversarialBco.UW.BudW.EncU

open AdversarialBco.Unified.BudR AdversarialBco.Unified.BudR.EncR AdversarialBco.Unified.BudR.EncR.OK

variable {r : EncR}

/-- PARAM's `ε` numerator without rounding, `X = 14500 d (r_d + 2^{-q}) L⁺^5/r_n`, encloses `ε` from above. -/
theorem eps_X (h : r.OK) : r.eps ≤ 14500 * r.d * (r.rd + r.eq) * r.Lh ^ 5 / r.rn ∧
    14500 * r.d * (r.rd + r.eq) * r.Lh ^ 5 / r.rn ≤ r.eps * (1 + r.tp / 2 ^ 15) := by
  obtain ⟨hd0, hn0, hNe0, hLe0, hLp0, -, -, -, hsd1, hsn1, heqb, -⟩ := h.base
  obtain ⟨-, -, hx3, hy1, hy2⟩ := h.root_rat
  obtain ⟨-, -, -, -, hz1, hz2⟩ := h.Lp_rat
  have htp := h.htp0
  have htp1 := h.htp1
  have heq0 := h.heq0
  have hrn0 : 1 ≤ r.rn := h.hrn0
  have hrd0 : 1 ≤ r.rd := h.hrd0
  have hsd0 : 0 < Real.sqrt r.d := by linarith
  have hsn0 : 0 < Real.sqrt r.n := by linarith
  set x := (r.rd + r.eq) / Real.sqrt r.d with hx
  set y := Real.sqrt r.n / r.rn with hy
  set z := r.Lh / r.Le with hz
  have heps0 : 0 < r.eps := by unfold EncR.eps; positivity
  have hq : 14500 * r.d * (r.rd + r.eq) * r.Lh ^ 5 / r.rn = r.eps * (x * y * z ^ 5) := by
    unfold EncR.eps
    simp only [x, y, z]
    field_simp
  have hx1 : 1 ≤ x := by
    rw [hx, le_div_iff₀ hsd0]; linarith [h.hrd2]
  have hz0 : 0 ≤ z := by positivity
  rw [hq]
  have hz5 : 1 ≤ z ^ 5 := one_le_pow₀ hz1
  constructor
  · have : 1 ≤ x * y * z ^ 5 := by
      have a : 1 * 1 ≤ x * y := mul_le_mul hx1 hy1 (by norm_num) (by linarith)
      have b : (1 * 1) * 1 ≤ x * y * z ^ 5 := mul_le_mul a hz5 (by norm_num) (by linarith)
      linarith
    exact le_mul_of_one_le_right heps0.le this
  · -- `x y z^5 ≤ (1 + eq)² (1 + tp/2^22)^5 ≤ 1 + tp/2^15`
    set t := r.tp / 2 ^ 22 with ht
    have ht0 : 0 ≤ t := by positivity
    have ht1 : t ≤ 1 / 2 ^ 182 := by
      rw [ht]; calc r.tp / 2 ^ 22 ≤ 1 / 2 ^ 160 / 2 ^ 22 := by gcongr
        _ = 1 / 2 ^ 182 := by norm_num
    have hz5u : z ^ 5 ≤ (1 + t) ^ 5 := pow_le_pow_left₀ hz0 hz2 5
    have h5 : (1 + t) ^ 5 ≤ 1 + 6 * t := by
      have : t ^ 2 ≤ t / 2 ^ 182 := by nlinarith
      have : t ^ 3 ≤ t ^ 2 := by nlinarith
      have : t ^ 4 ≤ t ^ 3 := by nlinarith
      have : t ^ 5 ≤ t ^ 4 := by nlinarith
      nlinarith
    have hxy : x * y ≤ (1 + r.eq) * (1 + r.eq) := mul_le_mul hx3 hy2 (by linarith) (by linarith)
    have hxyz : x * y * z ^ 5 ≤ (1 + r.eq) * (1 + r.eq) * (1 + 6 * t) :=
      mul_le_mul hxy (hz5u.trans h5) (by linarith) (by positivity)
    have he1 : r.eq ≤ 16 * t := by rw [ht]; linarith
    have hfin : (1 + r.eq) * (1 + r.eq) * (1 + 6 * t) ≤ 1 + 2 ^ 7 * t := by
      have e1 : r.eq ≤ 1 := by linarith
      have t1 : t ≤ 1 := by linarith
      have k1 : r.eq * r.eq ≤ r.eq := mul_le_of_le_one_left heq0.le e1
      have k2 : r.eq * t ≤ t := mul_le_of_le_one_left ht0 e1
      have k3 : r.eq * r.eq * t ≤ t := mul_le_of_le_one_left ht0 (k1.trans e1)
      have ex : (1 + r.eq) * (1 + r.eq) * (1 + 6 * t) =
          1 + 2 * r.eq + r.eq * r.eq + 6 * t + 12 * (r.eq * t) + 6 * (r.eq * r.eq * t) := by ring
      rw [ex]; linarith
    have : 1 + 2 ^ 7 * t = 1 + r.tp / 2 ^ 15 := by rw [ht]; ring
    have hle : x * y * z ^ 5 ≤ 1 + r.tp / 2 ^ 15 := by linarith
    exact mul_le_mul_of_nonneg_left hle heps0.le

/-- `ε(u) = ε u^{1/2} ≤ ε'`. -/
theorem epsW_le (h : r.OK) {u ru ep : ℝ} (hru : Real.sqrt u ≤ ru + r.eq)
    (hep : 14500 * r.d * (r.rd + r.eq) * r.Lh ^ 5 * (ru + r.eq) / r.rn ≤ ep) :
    r.eps * Real.sqrt u ≤ ep := by
  obtain ⟨h1, -⟩ := eps_X h
  have heps0 : 0 < r.eps := by
    obtain ⟨hd0, hn0, -, hLe0, -⟩ := h.base
    unfold EncR.eps; positivity
  have hX0 : 0 ≤ 14500 * r.d * (r.rd + r.eq) * r.Lh ^ 5 / r.rn := by linarith
  have e : 14500 * r.d * (r.rd + r.eq) * r.Lh ^ 5 * (ru + r.eq) / r.rn =
      14500 * r.d * (r.rd + r.eq) * r.Lh ^ 5 / r.rn * (ru + r.eq) := by ring
  rw [e] at hep
  calc r.eps * Real.sqrt u ≤ 14500 * r.d * (r.rd + r.eq) * r.Lh ^ 5 / r.rn * (ru + r.eq) :=
        mul_le_mul h1 hru (Real.sqrt_nonneg _) hX0
    _ ≤ ep := hep

/-- `ε' ≤ ε(u) (1 + 2^{-p-4})`. -/
theorem epsW_rel (h : r.OK) {u ru ep : ℝ} (hu : 1 ≤ u) (hru1 : 1 ≤ ru) (hru : ru ≤ Real.sqrt u)
    (hep : ep ≤ 14500 * r.d * (r.rd + r.eq) * r.Lh ^ 5 * (ru + r.eq) / r.rn + r.eF) :
    ep ≤ r.eps * Real.sqrt u * (1 + r.tp / 16) := by
  obtain ⟨-, h2⟩ := eps_X h
  obtain ⟨hd0, hn0, hNe0, hLe0, -, -, hnN, -, hsd1, hsn1, heqb, heFb⟩ := h.base
  have htp := h.htp0
  have htp1 := h.htp1
  have heq0 := h.heq0
  have heF0 := h.heF0
  have heps0 : 0 < r.eps := by unfold EncR.eps; positivity
  have hsu1 : 1 ≤ Real.sqrt u := Real.one_le_sqrt.mpr hu
  set X := 14500 * r.d * (r.rd + r.eq) * r.Lh ^ 5 / r.rn with hXd
  have e : 14500 * r.d * (r.rd + r.eq) * r.Lh ^ 5 * (ru + r.eq) / r.rn = X * (ru + r.eq) := by rw [hXd]; ring
  rw [e] at hep
  -- `ru + eq ≤ u^{1/2} (1 + eq)`
  have hr : ru + r.eq ≤ Real.sqrt u * (1 + r.eq) := by
    have k : r.eq ≤ Real.sqrt u * r.eq := le_mul_of_one_le_left heq0.le hsu1
    have ex : Real.sqrt u * (1 + r.eq) = Real.sqrt u + Real.sqrt u * r.eq := by ring
    rw [ex]; linarith
  have hX0 : 0 ≤ X := le_trans heps0.le (eps_X h).1
  have h3 : X * (ru + r.eq) ≤ r.eps * (1 + r.tp / 2 ^ 15) * (Real.sqrt u * (1 + r.eq)) :=
    mul_le_mul h2 hr (by linarith) (by positivity)
  -- `eF ≤ ε u^{1/2} tp/2^40`: `1/ε ≤ n^{1/2} ≤ N`, `eF N ≤ tp/2^40`
  have hinv : 1 ≤ r.eps * r.Ne := by
    unfold EncR.eps
    rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
    have hsnn : Real.sqrt r.n ≤ r.n := by
      rw [Real.sqrt_le_left (by linarith)]; exact le_self_pow₀ h.hn (by norm_num)
    have hL1 : (1 : ℝ) ≤ r.Le := le_trans (by norm_num) h.hLe
    have a : 1 ≤ 14500 * r.d * Real.sqrt r.d * r.Le ^ 5 := by
      have : (1 : ℝ) ≤ r.Le ^ 5 := one_le_pow₀ hL1
      have : (1 : ℝ) ≤ r.d * Real.sqrt r.d := by nlinarith [h.hd]
      nlinarith
    nlinarith
  have hNe1 : (1 : ℝ) ≤ r.Ne := Ne_one h
  have heFN : r.eF * r.Ne ≤ r.tp / 2 ^ 40 := by
    have : r.eF * r.Ne ≤ r.eF * r.Ne ^ 2 :=
      mul_le_mul_of_nonneg_left (le_self_pow₀ hNe1 (by norm_num)) heF0.le
    linarith
  have h4 : r.eF ≤ r.eps * Real.sqrt u * (r.tp / 2 ^ 40) := by
    have a : r.eF ≤ r.eF * (r.eps * r.Ne) := le_mul_of_one_le_right heF0.le hinv
    have b : r.eF * (r.eps * r.Ne) = r.eps * (r.eF * r.Ne) := by ring
    have c : r.eps * (r.eF * r.Ne) ≤ r.eps * (r.tp / 2 ^ 40) := mul_le_mul_of_nonneg_left heFN heps0.le
    have d' : r.eps * (r.tp / 2 ^ 40) ≤ r.eps * Real.sqrt u * (r.tp / 2 ^ 40) := by
      have : r.eps * (r.tp / 2 ^ 40) * 1 ≤ r.eps * (r.tp / 2 ^ 40) * Real.sqrt u :=
        mul_le_mul_of_nonneg_left hsu1 (by positivity)
      nlinarith
    linarith
  -- the constant
  have hc : (1 + r.tp / 2 ^ 15) * (1 + r.eq) + r.tp / 2 ^ 40 ≤ 1 + r.tp / 16 := by
    have : r.eq ≤ r.tp / 2 ^ 18 := heqb
    have : r.tp / 2 ^ 15 * r.eq ≤ r.tp / 2 ^ 18 := by
      have : r.eq ≤ 1 := by linarith [show r.tp / 2 ^ 18 ≤ 1 by linarith]
      nlinarith
    nlinarith
  have hE : 0 ≤ r.eps * Real.sqrt u := by positivity
  calc ep ≤ X * (ru + r.eq) + r.eF := hep
    _ ≤ r.eps * (1 + r.tp / 2 ^ 15) * (Real.sqrt u * (1 + r.eq)) + r.eps * Real.sqrt u * (r.tp / 2 ^ 40) := by
        linarith
    _ = r.eps * Real.sqrt u * ((1 + r.tp / 2 ^ 15) * (1 + r.eq) + r.tp / 2 ^ 40) := by ring
    _ ≤ r.eps * Real.sqrt u * (1 + r.tp / 16) := mul_le_mul_of_nonneg_left hc hE

/-- `|η'/η(u) - 1| ≤ 2^{-p-16}`, `η(u) = η/u^{1/2}`, `η' = rnd_{pF}(r_d/(L' r_n r_u))`. -/
theorem etaW_rel (h : r.OK) {u ru et : ℝ} (hru1 : 1 ≤ ru) (hru : ru ≤ Real.sqrt u)
    (hru2 : Real.sqrt u ≤ ru + r.eq) (hEu : r.eF * r.Ne * Real.sqrt u ≤ r.tp / 2 ^ 40)
    (het : |et - r.rd / (r.Lp * r.rn * ru)| ≤ r.eF / 2) :
    |et / (r.eta / Real.sqrt u) - 1| ≤ r.tp / 2 ^ 16 := by
  obtain ⟨hd0, hn0, hNe0, hLe0, hLp0, -, -, -, hsd1, hsn1, heqb, heFb⟩ := h.base
  obtain ⟨hrd1, hrd2, -, hrn1, hrn2⟩ := h.root_rat
  obtain ⟨hl1, hl2, -⟩ := h.Lp_rat
  have htp := h.htp0
  have htp1 := h.htp1
  have heq0 := h.heq0
  have heF0 := h.heF0
  have hrd0 : 1 ≤ r.rd := h.hrd0
  have hrn0 : 1 ≤ r.rn := h.hrn0
  have hsu0 : 0 < Real.sqrt u := by linarith
  have heta0 : 0 < r.eta := by unfold EncR.eta; positivity
  have hetaW0 : 0 < r.eta / Real.sqrt u := by positivity
  set x := r.rd / Real.sqrt r.d
  set y := Real.sqrt r.n / r.rn
  set z := r.Le / r.Lp
  set w := Real.sqrt u / ru with hw
  have hq : r.rd / (r.Lp * r.rn * ru) / (r.eta / Real.sqrt u) = x * y * z * w := by
    unfold EncR.eta
    simp only [x, y, z, w]
    field_simp
  have hx0 : 0 ≤ x := by positivity
  have hy1 : 1 ≤ y := hrn1
  have hz1 : 1 ≤ z := hl1
  have hw1 : 1 ≤ w := by rw [hw, le_div_iff₀ (by linarith)]; linarith
  have hw2 : w ≤ 1 + r.eq := by
    rw [hw, div_le_iff₀ (by linarith)]
    have k : r.eq ≤ r.eq * ru := le_mul_of_one_le_right heq0.le hru1
    have ex : (1 + r.eq) * ru = ru + r.eq * ru := by ring
    rw [ex]; linarith
  have hup : x * y * z * w - 1 ≤ 60 * (r.tp / 2 ^ 22) := by
    have a : x * y ≤ 1 * (1 + r.eq) := mul_le_mul hrd2 hrn2 (by linarith) (by norm_num)
    have b : x * y * z ≤ (1 + r.eq) * (1 + r.tp / 2 ^ 22) :=
      mul_le_mul (by linarith) hl2 (by linarith) (by positivity)
    have c : x * y * z * w ≤ (1 + r.eq) * (1 + r.tp / 2 ^ 22) * (1 + r.eq) :=
      mul_le_mul b hw2 (by linarith) (by positivity)
    have t1 : r.tp ≤ 1 := le_trans htp1 (by norm_num)
    have e1 : r.eq ≤ r.tp / 2 ^ 18 := heqb
    have e2 : r.eq ≤ 1 / 2 ^ 18 := by linarith [show r.tp / 2 ^ 18 ≤ 1 / 2 ^ 18 by gcongr]
    have d1 : (1 + r.eq) * (1 + r.tp / 2 ^ 22) * (1 + r.eq) ≤ 1 + 60 * (r.tp / 2 ^ 22) := by
      have hs0 : 0 ≤ r.tp / 2 ^ 22 := by positivity
      have e3 : r.eq ≤ 1 := by linarith
      have k1 : r.eq * r.eq ≤ r.eq := mul_le_of_le_one_left heq0.le e3
      have k2 : r.eq * (r.tp / 2 ^ 22) ≤ r.tp / 2 ^ 22 := mul_le_of_le_one_left hs0 e3
      have k3 : r.eq * r.eq * (r.tp / 2 ^ 22) ≤ r.tp / 2 ^ 22 := mul_le_of_le_one_left hs0 (k1.trans e3)
      have ex : (1 + r.eq) * (1 + r.tp / 2 ^ 22) * (1 + r.eq) = 1 + 2 * r.eq + r.eq * r.eq + r.tp / 2 ^ 22 +
          2 * (r.eq * (r.tp / 2 ^ 22)) + r.eq * r.eq * (r.tp / 2 ^ 22) := by ring
      rw [ex]; linarith
    linarith
  have hlo : 1 - x * y * z * w ≤ r.tp / 2 ^ 18 := by
    have a : x * 1 ≤ x * y := mul_le_mul_of_nonneg_left hy1 hx0
    have b : x * y * 1 ≤ x * y * z := mul_le_mul_of_nonneg_left hz1 (by positivity)
    have c : x * y * z * 1 ≤ x * y * z * w := mul_le_mul_of_nonneg_left hw1 (by positivity)
    linarith
  -- the rounding: `1/η(u) = u^{1/2}/η ≤ N u^{1/2}`
  have hinv : 1 / r.eta ≤ r.Ne := by
    unfold EncR.eta
    rw [one_div_div, div_le_iff₀ (by linarith)]
    have hsnn : Real.sqrt r.n ≤ r.n := by
      rw [Real.sqrt_le_left (by linarith)]; exact le_self_pow₀ h.hn (by norm_num)
    have hL1 : (1 : ℝ) ≤ r.Le := le_trans (by norm_num) h.hLe
    have a1 : r.Le * Real.sqrt r.n ≤ r.Le * r.n := by gcongr
    have a2 : r.Le * r.n ≤ r.Le ^ 4 * r.d * r.n := by
      have : r.Le ≤ r.Le ^ 4 * r.d := by
        calc r.Le ≤ r.Le ^ 4 := le_self_pow₀ hL1 (by norm_num)
          _ ≤ r.Le ^ 4 * r.d := le_mul_of_one_le_right (by positivity) h.hd
      exact mul_le_mul_of_nonneg_right this hn0.le
    have a3 : r.Le ^ 4 * r.d * r.n ≤ r.Ne * Real.sqrt r.d := by
      have := mul_le_mul h.hsm hsd1 (by norm_num) hNe0.le
      linarith
    linarith
  have hR : |et - r.rd / (r.Lp * r.rn * ru)| / (r.eta / Real.sqrt u) ≤ r.tp / 2 ^ 40 := by
    rw [div_le_iff₀ hetaW0]
    have h1 : 1 ≤ r.Ne * r.eta := by
      have := hinv
      rw [div_le_iff₀ heta0] at this; linarith
    have h2 : r.eF ≤ r.eF * r.Ne * Real.sqrt u * (r.eta / Real.sqrt u) := by
      have e : r.eF * r.Ne * Real.sqrt u * (r.eta / Real.sqrt u) = r.eF * (r.Ne * r.eta) := by
        field_simp
      rw [e]
      exact le_mul_of_one_le_right heF0.le h1
    have h3 : r.eF * r.Ne * Real.sqrt u * (r.eta / Real.sqrt u) ≤ r.tp / 2 ^ 40 * (r.eta / Real.sqrt u) :=
      mul_le_mul_of_nonneg_right hEu hetaW0.le
    linarith
  have hdec : et / (r.eta / Real.sqrt u) - 1 =
      (et - r.rd / (r.Lp * r.rn * ru)) / (r.eta / Real.sqrt u) + (x * y * z * w - 1) := by
    rw [← hq]; field_simp; ring
  rw [hdec]
  have h2 : |x * y * z * w - 1| ≤ 60 * (r.tp / 2 ^ 22) := by
    rw [abs_le]; constructor <;> linarith
  calc _ ≤ |(et - r.rd / (r.Lp * r.rn * ru)) / (r.eta / Real.sqrt u)| + |x * y * z * w - 1| := abs_add_le _ _
    _ ≤ r.tp / 2 ^ 40 + 60 * (r.tp / 2 ^ 22) := by
        rw [abs_div, abs_of_pos hetaW0]; linarith
    _ ≤ r.tp / 2 ^ 16 := by
        have : r.tp / 2 ^ 40 ≤ r.tp / 2 ^ 22 := by gcongr <;> norm_num
        linarith

/-- `|κ_c'/κ_c(u) - 1| ≤ 2^{-p-4}`, `κ_c(u) = η(u) λ/(4 (1 - λ)²)`, `κ_c' = rnd_{pF}(η' λ'/(4 (1 - λ')²))`. -/
theorem kapcW_rel (h : r.OK) {u et kp : ℝ} (hu : 1 ≤ u) (hEu : r.eF * r.Ne * Real.sqrt u ≤ r.tp / 2 ^ 40)
    (her : |et / (r.eta / Real.sqrt u) - 1| ≤ r.tp / 2 ^ 16)
    (hkp : |kp - et * r.lm / (4 * (1 - r.lm) ^ 2)| ≤ r.eF / 2) :
    |kp / (r.eta / Real.sqrt u * r.lam / (4 * (1 - r.lam) ^ 2)) - 1| ≤ r.tp / 16 := by
  obtain ⟨hd0, hn0, hNe0, hLe0, hLp0, -, -, -, hsd1, hsn1, -, heFb⟩ := h.base
  have hlr := h.lam_rel
  have htp := h.htp0
  have htp1 := h.htp1
  have heF0 := h.heF0
  have hd := h.hd
  have hLe := h.hLe
  have hsu1 : 1 ≤ Real.sqrt u := Real.one_le_sqrt.mpr hu
  have hsu0 : 0 < Real.sqrt u := by linarith
  set δ : ℝ := r.tp / 2 ^ 16 with hδ
  have hδ0 : 0 ≤ δ := by positivity
  have hδs : δ ≤ 1 / 2 ^ 170 := by
    rw [hδ]; calc r.tp / 2 ^ 16 ≤ 1 / 2 ^ 160 / 2 ^ 16 := by gcongr
      _ = 1 / 2 ^ 176 := by norm_num
      _ ≤ 1 / 2 ^ 170 := by norm_num
  have hlam0 : 0 < r.lam := by unfold EncR.lam; positivity
  have hlam1 : r.lam ≤ 1 / 4 := by
    unfold EncR.lam
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have hL2 : (1 : ℝ) ≤ r.Le ^ 2 := one_le_pow₀ (by linarith)
    have : (1 : ℝ) ≤ r.d * r.Le ^ 2 := one_le_mul_of_one_le_of_one_le hd hL2
    have ex : 725 * r.d * r.Le ^ 2 = 725 * (r.d * r.Le ^ 2) := by ring
    rw [ex]; linarith
  have hlm : |r.lm - r.lam| ≤ r.lam * δ := by
    have e : r.lm - r.lam = r.lam * (r.lm / r.lam - 1) := by field_simp
    rw [e, abs_mul, abs_of_pos hlam0]
    exact mul_le_mul_of_nonneg_left hlr hlam0.le
  have hlmd : r.lam * δ ≤ 1 / 16 := by
    have : r.lam * δ ≤ 1 / 4 * (1 / 2 ^ 170) := mul_le_mul hlam1 hδs hδ0 (by norm_num)
    linarith [show (1 : ℝ) / 4 * (1 / 2 ^ 170) ≤ 1 / 16 by norm_num]
  have hlm1 : 1 / 2 ≤ 1 - r.lm := by
    have := (abs_le.mp hlm).2; linarith
  have hlam2 : 1 / 2 ≤ 1 - r.lam := by linarith
  have hC : |(1 - r.lam) / (1 - r.lm) - 1| ≤ δ := by
    have e : (1 - r.lam) / (1 - r.lm) - 1 = (r.lm - r.lam) / (1 - r.lm) := by
      field_simp; ring
    rw [e, abs_div, abs_of_pos (by linarith : (0 : ℝ) < 1 - r.lm), div_le_iff₀ (by linarith)]
    have a : r.lam * δ ≤ 1 / 4 * δ := mul_le_mul_of_nonneg_right hlam1 hδ0
    have b : δ * (1 / 2) ≤ δ * (1 - r.lm) := mul_le_mul_of_nonneg_left hlm1 hδ0
    linarith
  have hC2 : |((1 - r.lam) / (1 - r.lm)) * ((1 - r.lam) / (1 - r.lm)) - 1| ≤ δ * (1 + δ) + δ :=
    mul_rel _ _ δ δ hC hC hδ0
  have hAB : |(et / (r.eta / Real.sqrt u)) * (r.lm / r.lam) - 1| ≤ δ * (1 + δ) + δ :=
    mul_rel _ _ δ δ her hlr hδ0
  have hδ2 : δ * (1 + δ) + δ ≤ 3 * δ := by
    have k : δ * δ ≤ δ := mul_le_of_le_one_left hδ0 (by linarith)
    have ex : δ * (1 + δ) + δ = 2 * δ + δ * δ := by ring
    rw [ex]; linarith
  have hP : |((et / (r.eta / Real.sqrt u)) * (r.lm / r.lam)) *
      (((1 - r.lam) / (1 - r.lm)) * ((1 - r.lam) / (1 - r.lm))) - 1| ≤ 3 * δ * (1 + 3 * δ) + 3 * δ :=
    mul_rel _ _ (3 * δ) (3 * δ) (le_trans hAB hδ2) (le_trans hC2 hδ2) (by positivity)
  have heta0 : 0 < r.eta := by unfold EncR.eta; positivity
  have hetaW0 : 0 < r.eta / Real.sqrt u := by positivity
  have hkc0 : 0 < r.eta / Real.sqrt u * r.lam / (4 * (1 - r.lam) ^ 2) := by positivity
  have hy : et * r.lm / (4 * (1 - r.lm) ^ 2) / (r.eta / Real.sqrt u * r.lam / (4 * (1 - r.lam) ^ 2)) =
      ((et / (r.eta / Real.sqrt u)) * (r.lm / r.lam)) *
        (((1 - r.lam) / (1 - r.lm)) * ((1 - r.lam) / (1 - r.lm))) := by
    have : (1 - r.lm) ≠ 0 := by linarith
    have : (1 - r.lam) ≠ 0 := by linarith
    field_simp
  -- the rounding: `1/κ_c(u) ≤ 2900 N u^{1/2}`
  have hinv : 1 / (r.eta / Real.sqrt u * r.lam / (4 * (1 - r.lam) ^ 2)) ≤ 2900 * r.Ne * Real.sqrt u := by
    rw [one_div_div]
    have h0 : (1 - r.lam) ^ 2 ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
    have h1 : 4 * (1 - r.lam) ^ 2 ≤ 4 := by linarith
    have h2 : 1 / (r.eta * r.lam) ≤ 725 * r.Ne := eta_lam_inv h
    have e : 4 * (1 - r.lam) ^ 2 / (r.eta / Real.sqrt u * r.lam) =
        4 * (1 - r.lam) ^ 2 * (1 / (r.eta * r.lam)) * Real.sqrt u := by
      field_simp
    rw [e]
    calc 4 * (1 - r.lam) ^ 2 * (1 / (r.eta * r.lam)) * Real.sqrt u ≤ 4 * (725 * r.Ne) * Real.sqrt u := by
          gcongr
      _ = 2900 * r.Ne * Real.sqrt u := by ring
  have hR : |(kp - et * r.lm / (4 * (1 - r.lm) ^ 2)) / (r.eta / Real.sqrt u * r.lam / (4 * (1 - r.lam) ^ 2))| ≤
      1450 * (r.tp / 2 ^ 40) := by
    rw [abs_div, abs_of_pos hkc0, div_eq_mul_one_div]
    calc |kp - et * r.lm / (4 * (1 - r.lm) ^ 2)| * (1 / (r.eta / Real.sqrt u * r.lam / (4 * (1 - r.lam) ^ 2))) ≤
          r.eF / 2 * (2900 * r.Ne * Real.sqrt u) := mul_le_mul hkp hinv (by positivity) (by positivity)
      _ = 1450 * (r.eF * r.Ne * Real.sqrt u) := by ring
      _ ≤ 1450 * (r.tp / 2 ^ 40) := by gcongr
  have hdec : kp / (r.eta / Real.sqrt u * r.lam / (4 * (1 - r.lam) ^ 2)) - 1 =
      (kp - et * r.lm / (4 * (1 - r.lm) ^ 2)) / (r.eta / Real.sqrt u * r.lam / (4 * (1 - r.lam) ^ 2)) +
      (et * r.lm / (4 * (1 - r.lm) ^ 2) / (r.eta / Real.sqrt u * r.lam / (4 * (1 - r.lam) ^ 2)) - 1) := by ring
  rw [hdec, hy]
  calc _ ≤ |(kp - et * r.lm / (4 * (1 - r.lm) ^ 2)) / (r.eta / Real.sqrt u * r.lam / (4 * (1 - r.lam) ^ 2))| +
        |((et / (r.eta / Real.sqrt u)) * (r.lm / r.lam)) *
          (((1 - r.lam) / (1 - r.lm)) * ((1 - r.lam) / (1 - r.lm))) - 1| := abs_add_le _ _
    _ ≤ 1450 * (r.tp / 2 ^ 40) + (3 * δ * (1 + 3 * δ) + 3 * δ) := add_le_add hR hP
    _ ≤ r.tp / 16 := by
        have t1 : r.tp ≤ 1 := le_trans htp1 (by norm_num)
        have k : 3 * δ * (1 + 3 * δ) ≤ 3 * δ * 2 := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        linarith

end AdversarialBco.UW.BudW.EncU
