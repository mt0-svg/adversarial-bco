/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.MagField
public import AdversarialBco.Unified.ProgOSplit

@[expose] public section

/-!
# The exponent of BL-O's calls: `expBLO : ExpBLO`

The exponent of ELL-O's integer call `clearO D` is that of the rowless problem
`(clearO D).base` (`ellExpO_eq`), whose `θ` is the `θ` of `clearQ D` (`base_theta`: the same objective, accuracy and
radius `R̄ = R_int`) and whose radius is `r/2`, so `1/(θ min(r/2, 1)) ≤ T^16` at the unit `T = 2^{K + E₀}`,
`K = pF + 8` (`fld_unit`), the three pairs (radius, accuracy) bounded by `pair_bndP` (over any PARAM whose `ε'` and
`s_b` are on the grid `2^{-pF}`). The exponent is at most `52 K + 48 E₀ + 8 ≤ 30000 (W + E₀ + 1)`.
-/

namespace AdversarialBco.Unified.MagO

open AdversarialBco AdversarialBco.Unified.BLO AdversarialBco.Unified.BudK AdversarialBco.Uni
open AdversarialBco.Bit.BLP (Par CallQ frob2 eBL)
open AdversarialBco.Bit.RQ (EllI clearQ ellExp lgQ)
open AdversarialBco.Bit.Transfer AdversarialBco.Bit.Transfer.BLM
open AdversarialBco.Unified.ProgO (InU wU)
open Matrix

variable {d : ℕ}

theorem ellExpO_eq (I : EllOI d) : ellExpO I = ellExp I.base := rfl

theorem base_theta (D : CallQ d) : (clearO D).base.θ = (clearQ D).θ := rfl

theorem base_r (D : CallQ d) : (clearO D).base.r = D.r / 2 := rfl

theorem base_Rb (D : CallQ d) : (clearO D).base.Rb = (clearQ D).Rb := rfl

/-- **`1/e` and `1/r` for BL's three calls**, over a PARAM whose `ε'` and `s_b` are on the grid `2^{-pF}`. -/
theorem pair_bndP (P : Par) (d n : ℕ) {T : ℚ} (hT : 128 ≤ T) (hNe : (P.Ne : ℚ) ≤ T) (hdT : (d : ℚ) ≤ T)
    (hnT : (n : ℚ) ≤ T) (hR : |P.R| ≤ T) (hpF : 2 * (2 : ℚ) ^ P.pF ≤ T) (heps : OnG P.pF P.eps)
    (hsbg : OnG P.pF P.sb) {r e : ℚ} (h : (r, e) ∈ callRE P d n) : 0 ≤ e ∧ |1 / e| ≤ T ^ 7 ∧ |r⁻¹| ≤ T ^ 2 := by
  have hT1 : (1 : ℚ) ≤ T := by linarith
  have hp1 : (2 : ℚ) ^ P.pF ≤ T := by
    have : (0 : ℚ) < 2 ^ P.pF := by positivity
    linarith
  have he1 : |(1 - P.eps)⁻¹| ≤ T := (inv_one_sub_grid heps).trans hp1
  have hsb : |P.sb⁻¹| ≤ T := (inv_grid hsbg).trans hp1
  have hNe0 : (0 : ℚ) ≤ P.Ne := Nat.cast_nonneg _
  have hd0 : (0 : ℚ) ≤ d := Nat.cast_nonneg _
  have habs : ∀ {x : ℚ}, 0 ≤ x → x ≤ T → |x| ≤ T ^ 1 := fun h0 h1 => by rw [abs_of_nonneg h0, pow_one]; exact h1
  have h8 : |(8 : ℚ)| ≤ T ^ 1 := habs (by norm_num) (by linarith)
  have hNd8 : |(P.Ne : ℚ) * d * 8| ≤ T ^ 3 := bnd_mul (bnd_mul (habs hNe0 hNe) (habs hd0 hdT)) h8
  have hrB : |(Bit.BLP.rB P)⁻¹| ≤ T ^ 2 := by
    unfold Bit.BLP.rB; rw [mul_inv, abs_mul, sq]
    exact mul_le_mul hsb he1 (abs_nonneg _) (by linarith)
  have hsb2 := inv_grid hsbg
  have hrB2 : |(Bit.BLP.rB P / 2)⁻¹| ≤ T ^ 2 := by
    unfold Bit.BLP.rB
    rw [inv_div, div_eq_mul_inv, mul_inv, abs_mul, abs_mul, abs_two, sq]
    calc 2 * (|P.sb⁻¹| * |(1 - P.eps)⁻¹|) = (2 * |P.sb⁻¹|) * |(1 - P.eps)⁻¹| := by ring
      _ ≤ T * T := mul_le_mul (by linarith) he1 (abs_nonneg _) (by linarith)
  simp only [callRE, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · refine ⟨by positivity, ?_, bnd_up hT1 (pw1 he1) (by norm_num)⟩
    rw [one_div_div, div_eq_mul_inv, ← inv_pow]
    exact bnd_up hT1 (bnd_mul hNd8 (by rw [sq]; exact bnd_mul (pw1 he1) (pw1 he1))) (by norm_num)
  · refine ⟨by positivity, ?_, hrB2⟩
    rw [one_div_div, div_eq_mul_inv, ← inv_pow]
    exact bnd_up hT1 (bnd_mul hNd8 (by rw [sq]; exact bnd_mul hrB hrB)) (by norm_num)
  · refine ⟨by unfold eBL; positivity, ?_, hrB2⟩
    unfold eBL
    rw [one_div_one_div]
    have h128 : |(128 : ℚ)| ≤ T ^ 1 := habs (by norm_num) hT
    have hn2 : |(n : ℚ) ^ 2| ≤ T ^ 2 := by
      rw [sq]; exact bnd_mul (habs (Nat.cast_nonneg _) hnT) (habs (Nat.cast_nonneg _) hnT)
    have hR2 : |P.R ^ 2| ≤ T ^ 2 := by rw [sq]; exact bnd_mul (pw1 hR) (pw1 hR)
    have h3 : |128 * (n : ℚ) ^ 2| ≤ T ^ 3 := bnd_mul (a := 1) (b := 2) h128 hn2
    have h5 : |128 * (n : ℚ) ^ 2 * P.R ^ 2| ≤ T ^ 5 := bnd_mul (a := 3) (b := 2) h3 hR2
    have h6 : |128 * (n : ℚ) ^ 2 * P.R ^ 2 * d| ≤ T ^ 6 := bnd_mul (a := 5) (b := 1) h5 (habs hd0 hdT)
    exact bnd_mul (a := 1) (b := 6) (habs hNe0 hNe) h6

/-- The exponent from the bounds: `3 j + lg R̄ + lg(d²(d + 1)) + 7 ≤ 30000 (W + E₀ + 1)`. -/
theorem exp_arith (j c1 c2 K E0 W : ℕ) (hj : j ≤ 16 * (K + E0)) (h1 : c1 ≤ K) (h2 : c2 ≤ 3 * K + 1)
    (hK : K ≤ 528 * W) : 3 * j + c1 + c2 + 7 ≤ 30000 * (W + E0 + 1) ^ 1 := by
  rw [pow_one]; omega

end AdversarialBco.Unified.MagO
