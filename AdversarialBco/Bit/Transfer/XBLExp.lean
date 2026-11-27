/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XBLMag
public import AdversarialBco.Bit.ApQ.Clear

@[expose] public section

/-!
# The exponent of BL's calls: the bounds

The exponent of the routine's point is `λ + 1` or `p`, both at most `3 j + lg R̄ + lg(d²(d + 1)) + 7`
(`ellExp_le`), with `j = lg(1/(θ min(r, 1)))`. On the cleared call the factor `D_P` cancels in `θ`:
`1/θ` is `1` or `3 (tr(P) R̄ + |f|₁) R̄ / e` (`invθ_le`), with `tr(B'B'ᵀ) = frob2 B' ≤ 2Λ`. For each of BL's three
pairs (radius, accuracy), `1/e` and `1/r` are products of PARAM's values and of inverses of points of the grid
`2^{-pF}` (`inv_grid`, `inv_one_sub_grid`; the pairs at BL-O's PARAM: `pair_bndP`, Unified/MagExp.lean). The junk
values of `x/0 = 0` need no case: every identity used holds in a field with `0⁻¹ = 0`.
-/

namespace AdversarialBco.Bit.Transfer.BLM

open AdversarialBco AdversarialBco.Bit AdversarialBco.Bit.BLP AdversarialBco.Bit.RQ Matrix

variable {d : ℕ}

/-! ## The exponent from `j` -/

theorem lgQ_le (x : ℚ) (u : ℕ) (h : x ≤ 2 ^ u) : lgQ x ≤ u := by
  unfold lgQ
  exact Nat.clog_le_of_le_pow (Nat.ceil_le.2 (by exact_mod_cast h))

/-- The exponent of the routine's point. -/
theorem ellExp_le (I : EllI d) : ellExp I ≤ 3 * I.j + Nat.clog 2 I.Rb + Nat.clog 2 (d ^ 2 * (d + 1)) + 7 := by
  unfold ellExp EllI.lam EllI.p
  split_ifs <;> omega

/-- `1/(θ min(r, 1))` from `1/θ` and `1/r`. -/
theorem X_le (I : EllI d) {T : ℚ} (hT : 1 ≤ T) {a b : ℕ} (hθ : |1 / I.θ| ≤ T ^ a) (hr : |I.r⁻¹| ≤ T ^ b) :
    1 / (I.θ * min I.r 1) ≤ T ^ (a + b) := by
  have hm : |1 / min I.r 1| ≤ T ^ b := by
    rcases le_total I.r 1 with h | h
    · rw [min_eq_left h, one_div]; exact hr
    · rw [min_eq_right h, div_one, abs_one]; exact one_le_pow₀ hT
  rw [← one_div_mul_one_div]
  exact (le_abs_self _).trans (bnd_mul hθ hm)

/-! ## The cleared objective -/

theorem LG_clear (D : BLP.CallQ d) :
    (clearQ D).LG = objDen D * (D.P.trace * (clearQ D).Rb + ∑ i, |D.f i|) := by
  unfold EllI.LG
  have h1 : (((clearQ D).P.trace : ℤ) : ℚ) = objDen D * D.P.trace := by
    simp only [Matrix.trace, Matrix.diag, Int.cast_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have := ApQ.clearQ_P D i i
    exact_mod_cast this
  have h2 : (∑ i, |((clearQ D).f i : ℚ)|) / (clearQ D).Df = objDen D * ∑ i, |D.f i| := by
    rw [Finset.sum_div, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h := ApQ.clearQ_f D i
    have hq : ((clearQ D).f i : ℚ) / (clearQ D).Df = objDen D * D.f i := by exact_mod_cast h
    have hDf : (0 : ℚ) < (clearQ D).Df := by exact_mod_cast ApQ.linDen_pos D
    calc |((clearQ D).f i : ℚ)| / (clearQ D).Df = |((clearQ D).f i : ℚ) / (clearQ D).Df| := by
          rw [abs_div, abs_of_pos hDf]
      _ = |(objDen D : ℚ) * D.f i| := by rw [hq]
      _ = objDen D * |D.f i| := by rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
  rw [h1, h2]
  ring

/-- **`1/θ` on a cleared call**: `1`, or `3 (tr(P) R̄ + |f|₁) R̄ / e`. -/
theorem invθ_le (D : BLP.CallQ d) {T : ℚ} (hT : 3 ≤ T) {a b : ℕ}
    (hL : abs (D.P.trace * (clearQ D).Rb + ∑ i, |D.f i|) ≤ T ^ a) (hRb : ((clearQ D).Rb : ℚ) ≤ T)
    (he : |1 / D.e| ≤ T ^ b) : |1 / (clearQ D).θ| ≤ T ^ (1 + a + 1 + b) := by
  have hT1 : (1 : ℚ) ≤ T := by linarith
  unfold EllI.θ
  split_ifs
  · rw [div_one, abs_one]; exact one_le_pow₀ hT1
  · have hD : (objDen D : ℚ) ≠ 0 := by exact_mod_cast (ApQ.objDen_pos D).ne'
    rw [one_div_div, LG_clear, ApQ.clearQ_e]
    rw [show 3 * (↑(objDen D) * (D.P.trace * ↑(clearQ D).Rb + ∑ i, |D.f i|)) * ↑(clearQ D).Rb =
        ↑(objDen D) * (3 * (D.P.trace * ↑(clearQ D).Rb + ∑ i, |D.f i|) * ↑(clearQ D).Rb) by ring,
      mul_div_mul_left _ _ hD, div_eq_mul_one_div]
    exact bnd_mul (bnd_mul (bnd_mul (pw1 (by rw [abs_of_pos (by norm_num : (0 : ℚ) < 3)]; exact hT)) hL)
      (pw1 (by rw [abs_of_nonneg (Nat.cast_nonneg _)]; exact hRb))) he

theorem trace_mul_tr (Bp : Matrix (Fin d) (Fin d) ℚ) : (Bp * Bpᵀ).trace = frob2 Bp := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, frob2, sq]

theorem frob2_nonneg (Bp : Matrix (Fin d) (Fin d) ℚ) : 0 ≤ frob2 Bp :=
  Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _

/-! ## BL's three pairs (radius, accuracy) -/

theorem inv_grid {k : ℕ} {x : ℚ} (hx : OnG k x) : |x⁻¹| ≤ 2 ^ k := by
  have e : x = (qn k x : ℚ) / 2 ^ k := by
    unfold OnG at hx; rw [hx, eq_div_iff (by positivity)]
  rw [e]
  exact grid_inv_abs _ _

theorem inv_one_sub_grid {k : ℕ} {x : ℚ} (hx : OnG k x) : |(1 - x)⁻¹| ≤ 2 ^ k := by
  have e : 1 - x = (((2 : ℤ) ^ k - qn k x : ℤ) : ℚ) / 2 ^ k := by
    unfold OnG at hx; push_cast; rw [hx, eq_div_iff (by positivity)]; ring
  rw [e]
  exact grid_inv_abs _ _

theorem onG_dn (k : ℕ) (x : ℚ) : OnG k (dn k x) := by
  unfold OnG; rw [qn_dn]; unfold dn; field_simp

end AdversarialBco.Bit.Transfer.BLM
