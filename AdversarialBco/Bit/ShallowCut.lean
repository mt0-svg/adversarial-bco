/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import Mathlib

@[expose] public section

/-!
# The shallow-cut ellipsoid update at depth β

The update of Procedure ROUND-β (GLS (3.3.13) to (3.3.17) with no rounding): from `E(A, c)` and a row `a` cut at depth
`β`, `c' = c - ρ A a/|a|_A`, `A' = σ (A - τ A a aᵀ A/(aᵀ A a))`, with `ρ = (1 - dβ)/(d + 1)`,
`σ = d² (1 - β²)/(d² - 1)`, `τ = 2 (1 - dβ)/((d + 1)(1 - β))`.

* `sc_incl_scalar`: Lemma SC (ii) in the reduced form: `(p + 2ρs + ρ² + τ/(1 - τ) (s + ρ)²)/σ ≤ 1` for `s² ≤ p ≤ 1`,
  `s ≤ β`.
* `sc_sherman_morrison`: the inverse of `A - τ A a aᵀ A/(aᵀ A a)` is `A⁻¹ + τ/((1 - τ) aᵀ A a) a aᵀ`.
* `sc_posDef`: Lemma SC (i), `A'` is positive definite.
* `sc_incl`: Lemma SC (ii), the kept cap `E(A, c) ∩ {aᵀ(x - c) ≤ β |a|_A}` lies in `E(A', c')`; from `sc_incl_inv` (the
  inverse of `A'` in closed form), `sc_incl_quad` (the form of `A'⁻¹` at `x - c'`, expanded) and `sc_incl_cs`
  (`(aᵀ y)² ≤ (aᵀ A a)(yᵀ A⁻¹ y)`).
* `sc_det`: `det A' = σⁿ (1 - τ) det A`.
* `sc_volume`: Lemma SC (iii), `(σ^d (1 - τ))^{1/2} ≤ exp(-(1 - dβ)²/(2d))` for `d ≥ 2`, `0 ≤ β < 1/d`. The proof is
  not the series of GLS (3.3.25). With `t = 1 - dβ`, `a = 1 - t/(d + 1)`, `b = 1 + t/(d - 1)`: `σ = a b` and
  `1 - τ = a/b` (`sc_vol_alg`), so `σ^d (1 - τ) = a^{d+1} b^{d-1}`; and `h(t) = ((d + 1)/2) log a + ((d - 1)/2) log b
  + t²/(2d)` has `h(0) = 0` and derivative `t (1/d - d/(d² - (1 - t)²)) ≤ 0` on `[0, 1]` (`sc_vol_deriv`, `sc_vol_h`).

Each lemma sits in a namespace
`AdversarialBco.Bit.Aux_<name>` with its helpers, the lemma itself at `AdversarialBco.Bit.<name>`.
-/

namespace AdversarialBco.Bit.Aux_sc_incl_scalar


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

theorem _root_.AdversarialBco.Bit.sc_incl_scalar (d β ρ σ τ p s : ℝ) (hd : 2 ≤ d) (hβ0 : 0 ≤ β) (hβd : d * β < 1)
    (hρ : ρ = (1 - d * β) / (d + 1)) (hσ : σ = d ^ 2 * (1 - β ^ 2) / (d ^ 2 - 1))
    (hτ : τ = 2 * (1 - d * β) / ((d + 1) * (1 - β))) (hsp : s ^ 2 ≤ p) (hp : p ≤ 1) (hsβ : s ≤ β) :
    (p + 2 * ρ * s + ρ ^ 2 + τ / (1 - τ) * (s + ρ) ^ 2) / σ ≤ 1 := by
  have hdpos : 0 < d := by linarith
  have hd1pos : 0 < d + 1 := by linarith
  have hd1sq_pos : 0 < d ^ 2 - 1 := by nlinarith
  have hβ_lt_one : β < 1 := by
    nlinarith
  have h_one_minus_β_pos : 0 < 1 - β := by linarith
  have h_one_plus_β_pos : 0 < 1 + β := by linarith
  have hσ_pos : 0 < σ := by
    rw [hσ]
    have hpos : 0 < 1 - β ^ 2 := by nlinarith
    positivity
  have h_one_minus_τ_pos : 0 < 1 - τ := by
    have h_expr : 1 - τ = ((d - 1) * (1 + β)) / ((d + 1) * (1 - β)) := by
      rw [hτ]
      field_simp [show (d + 1) * (1 - β) ≠ 0 from by positivity]
      ring
    rw [h_expr]
    have hnum : 0 < (d - 1) * (1 + β) := by
      have hd1 : 0 < d - 1 := by linarith
      positivity
    have hden : 0 < (d + 1) * (1 - β) := by positivity
    exact div_pos hnum hden
  have hτ_nonneg : 0 ≤ τ := by
    rw [hτ]
    have hnum : 0 ≤ 2 * (1 - d * β) := by nlinarith
    have hden : 0 ≤ (d + 1) * (1 - β) := by positivity
    exact div_nonneg hnum hden
  have h_s_ge_neg_one : -1 ≤ s := by
    have : s ^ 2 ≤ 1 := by linarith
    nlinarith
  have h_one_minus_τ_ne_zero : 1 - τ ≠ 0 := by linarith
  -- Key algebraic identity
  have h_identity : (1 - s ^ 2 + (s + ρ) ^ 2 / (1 - τ)) / σ - 1 =
      (τ / (σ * (1 - τ))) * ((s + 1) * (s - β)) := by
    field_simp [hσ_pos.ne', h_one_minus_τ_ne_zero]
    rw [hρ, hσ, hτ]
    field_simp [show d + 1 ≠ 0 from by linarith, show d ^ 2 - 1 ≠ 0 from by linarith [hd1sq_pos],
      show 1 - β ≠ 0 from by linarith]
    ring_nf
  -- Express the original numerator in a convenient form
  have h_numerator_eq : p + 2 * ρ * s + ρ ^ 2 + τ / (1 - τ) * (s + ρ) ^ 2 =
      (p - s ^ 2) + (s + ρ) ^ 2 / (1 - τ) := by
    calc
      p + 2 * ρ * s + ρ ^ 2 + τ / (1 - τ) * (s + ρ) ^ 2
          = (p - s ^ 2) + (s ^ 2 + 2 * ρ * s + ρ ^ 2) + τ / (1 - τ) * (s + ρ) ^ 2 := by ring
      _ = (p - s ^ 2) + (s + ρ) ^ 2 + τ / (1 - τ) * (s + ρ) ^ 2 := by ring
      _ = (p - s ^ 2) + ((1 - τ) / (1 - τ) + τ / (1 - τ)) * (s + ρ) ^ 2 := by
        field_simp [h_one_minus_τ_ne_zero]
        ring
      _ = (p - s ^ 2) + (1 / (1 - τ)) * (s + ρ) ^ 2 := by ring
      _ = (p - s ^ 2) + (s + ρ) ^ 2 / (1 - τ) := by ring
  have h_numerator_le : p + 2 * ρ * s + ρ ^ 2 + τ / (1 - τ) * (s + ρ) ^ 2 ≤
      1 - s ^ 2 + (s + ρ) ^ 2 / (1 - τ) := by
    rw [h_numerator_eq]
    nlinarith
  -- Divide both sides by σ > 0
  have h_main : (p + 2 * ρ * s + ρ ^ 2 + τ / (1 - τ) * (s + ρ) ^ 2) / σ ≤
      (1 - s ^ 2 + (s + ρ) ^ 2 / (1 - τ)) / σ := by
    exact (div_le_div_of_nonneg_right h_numerator_le (by linarith))
  -- RHS = 1 + τ/(σ(1-τ)) * (s+1)(s-β)
  have h_rhs_eq : (1 - s ^ 2 + (s + ρ) ^ 2 / (1 - τ)) / σ = 1 + (τ / (σ * (1 - τ))) * ((s + 1) * (s - β)) := by
    linarith [h_identity]
  rw [h_rhs_eq] at h_main
  -- Need: 1 + coeff * (s+1)(s-β) ≤ 1, i.e., coeff * (s+1)(s-β) ≤ 0
  have h_factor_nonpos : (s + 1) * (s - β) ≤ 0 := by
    have h1 : 0 ≤ s + 1 := by linarith
    have h2 : s - β ≤ 0 := by linarith
    nlinarith
  have h_coeff_nonneg : 0 ≤ τ / (σ * (1 - τ)) := by
    refine div_nonneg hτ_nonneg ?_
    positivity
  have h_prod_nonpos : (τ / (σ * (1 - τ))) * ((s + 1) * (s - β)) ≤ 0 := by
    nlinarith
  linarith

end AdversarialBco.Bit.Aux_sc_incl_scalar

namespace AdversarialBco.Bit.Aux_sc_sherman_morrison


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

theorem _root_.AdversarialBco.Bit.sc_sherman_morrison {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (hA : IsUnit A.det)
    (hAt : Aᵀ = A) (a : Fin d → ℝ) (τ : ℝ) (hq : a ⬝ᵥ (A *ᵥ a) ≠ 0) (hτ : τ ≠ 1) :
    (A - (τ / (a ⬝ᵥ (A *ᵥ a))) • vecMulVec (A *ᵥ a) (A *ᵥ a)) *
        (A⁻¹ + (τ / ((1 - τ) * (a ⬝ᵥ (A *ᵥ a)))) • vecMulVec a a) = 1 := by
  set q := a ⬝ᵥ (A *ᵥ a) with hq_def
  set u := A *ᵥ a with hu_def
  have hq_ne_zero : q ≠ 0 := hq
  have hτ_ne_one : τ ≠ 1 := hτ
  have h_oneminusτ_ne_zero : 1 - τ ≠ 0 := by
    intro hzero
    apply hτ_ne_one
    linarith
  set c₁ := τ / q with hc₁_def
  set c₂ := τ / ((1 - τ) * q) with hc₂_def
  have hAAinv : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A hA
  have hAinvA : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A hA
  have hA_vecMulVec : A * vecMulVec a a = vecMulVec u a := by
    calc
      A * vecMulVec a a = vecMulVec (A.mulVec a) a := by
        simpa using Matrix.mul_vecMulVec A a a
      _ = vecMulVec u a := by simp [hu_def]
  have h_vecMulVec_inv : vecMulVec u u * A⁻¹ = vecMulVec u a := by
    calc
      vecMulVec u u * A⁻¹ = vecMulVec u (u ᵥ* A⁻¹) := by
        simpa using Matrix.vecMulVec_mul u u A⁻¹
      _ = vecMulVec u (A⁻¹.transpose.mulVec u) := by
        rw [Matrix.mulVec_transpose A⁻¹ u]
      _ = vecMulVec u (A⁻¹.mulVec u) := by
        simp [Matrix.transpose_nonsing_inv A, hAt]
      _ = vecMulVec u (A⁻¹.mulVec (A.mulVec a)) := by simp [hu_def]
      _ = vecMulVec u ((A⁻¹ * A).mulVec a) := by
        simp [Matrix.mulVec_mulVec]
      _ = vecMulVec u ((1 : Matrix (Fin d) (Fin d) ℝ).mulVec a) := by
        simp [hAinvA]
      _ = vecMulVec u a := by simp
  have h_vecMulVec_prod : vecMulVec u u * vecMulVec a a = q • vecMulVec u a := by
    calc
      vecMulVec u u * vecMulVec a a = vecMulVec u ((u ⬝ᵥ a) • a) := by
        simpa using Matrix.vecMulVec_mul_vecMulVec u u a a
      _ = vecMulVec u (q • a) := by
        simp [hu_def, hq_def, dotProduct_comm]
      _ = q • vecMulVec u a := by simp
  have h_expand : (A - c₁ • vecMulVec u u) * (A⁻¹ + c₂ • vecMulVec a a) =
      1 + (c₂ - c₁ - c₁ * c₂ * q) • vecMulVec u a := by
    calc
      (A - c₁ • vecMulVec u u) * (A⁻¹ + c₂ • vecMulVec a a)
          = A * (A⁻¹ + c₂ • vecMulVec a a) - (c₁ • vecMulVec u u) * (A⁻¹ + c₂ • vecMulVec a a) := by
        rw [sub_mul]
      _ = (A * A⁻¹ + A * (c₂ • vecMulVec a a)) - ((c₁ • vecMulVec u u) * A⁻¹ + (c₁ • vecMulVec u u) * (c₂ • vecMulVec a a)) := by
        rw [mul_add, mul_add]
      _ = (1 + A * (c₂ • vecMulVec a a)) - ((c₁ • vecMulVec u u) * A⁻¹ + (c₁ • vecMulVec u u) * (c₂ • vecMulVec a a)) := by
        rw [hAAinv]
      _ = (1 + c₂ • (A * vecMulVec a a)) - ((c₁ • vecMulVec u u) * A⁻¹ + (c₁ • vecMulVec u u) * (c₂ • vecMulVec a a)) := by
        rw [Matrix.mul_smul]
      _ = (1 + c₂ • (A * vecMulVec a a)) - (c₁ • (vecMulVec u u * A⁻¹) + (c₁ • vecMulVec u u) * (c₂ • vecMulVec a a)) := by
        rw [Matrix.smul_mul]
      _ = (1 + c₂ • (A * vecMulVec a a)) - (c₁ • (vecMulVec u u * A⁻¹) + c₁ • (vecMulVec u u * (c₂ • vecMulVec a a))) := by
        rw [Matrix.smul_mul]
      _ = (1 + c₂ • (A * vecMulVec a a)) - (c₁ • (vecMulVec u u * A⁻¹) + c₁ • (c₂ • (vecMulVec u u * vecMulVec a a))) := by
        rw [Matrix.mul_smul]
      _ = (1 + c₂ • (A * vecMulVec a a)) - (c₁ • (vecMulVec u u * A⁻¹) + (c₁ * c₂) • (vecMulVec u u * vecMulVec a a)) := by
        rw [smul_smul c₁ c₂ (vecMulVec u u * vecMulVec a a)]
      _ = (1 + c₂ • vecMulVec u a) - (c₁ • vecMulVec u a + (c₁ * c₂) • (q • vecMulVec u a)) := by
        rw [hA_vecMulVec, h_vecMulVec_inv, h_vecMulVec_prod]
      _ = 1 + (c₂ • vecMulVec u a - c₁ • vecMulVec u a - (c₁ * c₂) • (q • vecMulVec u a)) := by
        abel
      _ = 1 + (c₂ • vecMulVec u a - c₁ • vecMulVec u a - (c₁ * c₂ * q) • vecMulVec u a) := by
        simp [smul_smul, mul_assoc]
      _ = 1 + ((c₂ - c₁ - c₁ * c₂ * q) • vecMulVec u a) := by
        simp [sub_smul]
      _ = 1 + (c₂ - c₁ - c₁ * c₂ * q) • vecMulVec u a := rfl
  calc
    (A - c₁ • vecMulVec u u) * (A⁻¹ + c₂ • vecMulVec a a)
        = 1 + (c₂ - c₁ - c₁ * c₂ * q) • vecMulVec u a := h_expand
    _ = 1 + ((τ / ((1 - τ) * q)) - (τ / q) - ((τ / q) * (τ / ((1 - τ) * q))) * q) • vecMulVec u a := by
      simp [hc₁_def, hc₂_def]
    _ = 1 := by
      field_simp [hq_ne_zero, h_oneminusτ_ne_zero]
      ring_nf
      simp

end AdversarialBco.Bit.Aux_sc_sherman_morrison

namespace AdversarialBco.Bit.Aux_sc_posDef


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

theorem _root_.AdversarialBco.Bit.sc_posDef {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.PosDef) (a : Fin d → ℝ)
    (ha : a ≠ 0) (σ τ : ℝ) (hσ : 0 < σ) (hτ : τ < 1) :
    (σ • (A - (τ / (a ⬝ᵥ (A *ᵥ a))) • vecMulVec (A *ᵥ a) (A *ᵥ a))).PosDef := by
  set q := a ⬝ᵥ (A *ᵥ a) with hq_def
  have hq_pos : 0 < q := by
    rw [hq_def]
    simpa [star_trivial] using hA.dotProduct_mulVec_pos ha
  set u := A *ᵥ a with hu_def
  have hu_herm : (vecMulVec u u).IsHermitian := by
    rw [IsHermitian, conjTranspose_vecMulVec]
    simp [star_trivial]
  have h_herm : (A - (τ / q) • vecMulVec u u).IsHermitian := by
    have h_sq : IsSelfAdjoint (τ / q : ℝ) := isSelfAdjoint_iff.mpr (star_trivial _)
    exact hA.1.sub (hu_herm.smul h_sq)
  have h_pos : ∀ x : Fin d → ℝ, x ≠ 0 → 0 < x ⬝ᵥ ((A - (τ / q) • vecMulVec u u) *ᵥ x) := by
    intro x hx
    have hx_pos : 0 < x ⬝ᵥ (A *ᵥ x) := by
      simpa [star_trivial] using hA.dotProduct_mulVec_pos hx
    have h_cauchy : (a ⬝ᵥ A *ᵥ x)^2 ≤ q * (x ⬝ᵥ A *ᵥ x) := by
      have h := hA.star_dotProduct_mulVec_mul_le a x
      simpa [star_trivial, hq_def, pow_two] using h
    have h_ux_eq : u ⬝ᵥ x = a ⬝ᵥ (A *ᵥ x) := by
      calc
        u ⬝ᵥ x = (A *ᵥ a) ⬝ᵥ x := rfl
        _ = x ⬝ᵥ (A *ᵥ a) := dotProduct_comm _ _
        _ = star x ⬝ᵥ (A *ᵥ a) := by simp [star_trivial]
        _ = star a ⬝ᵥ (A *ᵥ x) := hA.1.star_dotProduct_mulVec_comm x a
        _ = a ⬝ᵥ (A *ᵥ x) := by simp [star_trivial]
    have h_ux_sq : x ⬝ᵥ (vecMulVec u u *ᵥ x) = (u ⬝ᵥ x)^2 := by
      simp [vecMulVec_mulVec, dotProduct_smul, dotProduct_comm u x, pow_two]
    have h_target : 0 < x ⬝ᵥ (A *ᵥ x) - (τ / q) * (x ⬝ᵥ (vecMulVec u u *ᵥ x)) := by
      rw [h_ux_sq]
      have h_ux_sq_le : (u ⬝ᵥ x)^2 ≤ q * (x ⬝ᵥ A *ᵥ x) := by
        rw [h_ux_eq]
        exact h_cauchy
      by_cases hτ_nonpos : τ ≤ 0
      · have h_nonneg : 0 ≤ -(τ / q) := by
          have h_nonpos_div : τ / q ≤ 0 := div_nonpos_of_nonpos_of_nonneg hτ_nonpos (by linarith)
          linarith
        have h_sq_nonneg : 0 ≤ (u ⬝ᵥ x)^2 := sq_nonneg _
        have h_nonneg_prod : 0 ≤ -(τ / q) * (u ⬝ᵥ x)^2 := mul_nonneg h_nonneg h_sq_nonneg
        nlinarith
      · have hτ_pos : 0 < τ := by linarith
        have h_div_pos : 0 < τ / q := div_pos hτ_pos hq_pos
        have h_mul : (τ / q) * (u ⬝ᵥ x)^2 ≤ (τ / q) * (q * (x ⬝ᵥ A *ᵥ x)) :=
          mul_le_mul_of_nonneg_left h_ux_sq_le (by linarith)
        have h_right : (τ / q) * (q * (x ⬝ᵥ A *ᵥ x)) = τ * (x ⬝ᵥ A *ᵥ x) := by
          field_simp [hq_pos.ne']
        have h_sub_eq : x ⬝ᵥ (A *ᵥ x) - τ * (x ⬝ᵥ A *ᵥ x) = (1 - τ) * (x ⬝ᵥ A *ᵥ x) := by ring
        have h_pos_one_minus_tau : 0 < 1 - τ := by linarith
        have h_pos_prod : 0 < (1 - τ) * (x ⬝ᵥ A *ᵥ x) := by
          nlinarith
        nlinarith
    have h_mulVec_sub : (A - (τ / q) • vecMulVec u u) *ᵥ x = (A *ᵥ x) - (τ / q) • (vecMulVec u u *ᵥ x) := by
      rw [sub_mulVec, smul_mulVec]
    rw [h_mulVec_sub]
    have h_dotProduct_sub : x ⬝ᵥ ((A *ᵥ x) - (τ / q) • (vecMulVec u u *ᵥ x)) =
        x ⬝ᵥ (A *ᵥ x) - (τ / q) * (x ⬝ᵥ (vecMulVec u u *ᵥ x)) := by
      rw [dotProduct_sub, dotProduct_smul]
      simp
    rw [h_dotProduct_sub]
    exact h_target
  have h_pos_smul : ∀ x : Fin d → ℝ, x ≠ 0 → 0 < x ⬝ᵥ ((σ • (A - (τ / q) • vecMulVec u u)) *ᵥ x) := by
    intro x hx
    have h_inner_pos : 0 < x ⬝ᵥ ((A - (τ / q) • vecMulVec u u) *ᵥ x) := h_pos x hx
    have h_mulVec_smul : (σ • (A - (τ / q) • vecMulVec u u)) *ᵥ x = σ • ((A - (τ / q) • vecMulVec u u) *ᵥ x) := by
      rw [smul_mulVec]
    rw [h_mulVec_smul]
    have h_dotProduct_smul' : x ⬝ᵥ (σ • ((A - (τ / q) • vecMulVec u u) *ᵥ x)) = σ * (x ⬝ᵥ ((A - (τ / q) • vecMulVec u u) *ᵥ x)) := by
      rw [dotProduct_smul]
      simp
    rw [h_dotProduct_smul']
    nlinarith
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ h_pos_smul
  have h_sigma_herm : IsSelfAdjoint σ := isSelfAdjoint_iff.mpr (star_trivial _)
  have h_smul_herm : (σ • (A - (τ / q) • vecMulVec u u)).IsHermitian :=
    h_herm.smul h_sigma_herm
  exact h_smul_herm

end AdversarialBco.Bit.Aux_sc_posDef

namespace AdversarialBco.Bit.Aux_sc_incl_inv


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius

theorem _root_.AdversarialBco.Bit.sc_incl_inv {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) (a : Fin n → ℝ)
    (ha : a ≠ 0) (σ τ : ℝ) (hσ : σ ≠ 0) (hτ : τ ≠ 1) :
    (σ • (A - (τ / (a ⬝ᵥ (A *ᵥ a))) • vecMulVec (A *ᵥ a) (A *ᵥ a)))⁻¹ =
      σ⁻¹ • (A⁻¹ + (τ / ((1 - τ) * (a ⬝ᵥ (A *ᵥ a)))) • vecMulVec a a) := by
  have hAt : Aᵀ = A := by
    have h_herm : A.IsHermitian := hA.isHermitian
    rw [← conjTranspose_eq_transpose_of_trivial, h_herm.eq]
  have hA_det_pos : 0 < A.det := hA.det_pos
  have hA_det_unit : IsUnit A.det := hA_det_pos.ne.symm.isUnit
  have hq_pos : 0 < a ⬝ᵥ (A *ᵥ a) := by
    have := hA.dotProduct_mulVec_pos ha
    simpa [star] using this
  have hq_ne : a ⬝ᵥ (A *ᵥ a) ≠ 0 := by linarith
  have hMN : (A - (τ / (a ⬝ᵥ (A *ᵥ a))) • vecMulVec (A *ᵥ a) (A *ᵥ a)) *
      (A⁻¹ + (τ / ((1 - τ) * (a ⬝ᵥ (A *ᵥ a)))) • vecMulVec a a) = 1 :=
    sc_sherman_morrison A hA_det_unit hAt a τ hq_ne hτ
  have h_smul : (σ • (A - (τ / (a ⬝ᵥ (A *ᵥ a))) • vecMulVec (A *ᵥ a) (A *ᵥ a))) *
      (σ⁻¹ • (A⁻¹ + (τ / ((1 - τ) * (a ⬝ᵥ (A *ᵥ a)))) • vecMulVec a a)) = 1 := by
    calc
      (σ • (A - (τ / (a ⬝ᵥ (A *ᵥ a))) • vecMulVec (A *ᵥ a) (A *ᵥ a))) *
          (σ⁻¹ • (A⁻¹ + (τ / ((1 - τ) * (a ⬝ᵥ (A *ᵥ a)))) • vecMulVec a a))
          = (σ * σ⁻¹) • ((A - (τ / (a ⬝ᵥ (A *ᵥ a))) • vecMulVec (A *ᵥ a) (A *ᵥ a)) *
              (A⁻¹ + (τ / ((1 - τ) * (a ⬝ᵥ (A *ᵥ a)))) • vecMulVec a a)) := by
        rw [smul_mul_smul_comm]
      _ = (σ * σ⁻¹) • (1 : Matrix (Fin n) (Fin n) ℝ) := by rw [hMN]
      _ = 1 := by
        field_simp [hσ]
        simp
  exact Matrix.inv_eq_right_inv h_smul

end AdversarialBco.Bit.Aux_sc_incl_inv

namespace AdversarialBco.Bit.Aux_sc_incl_quad


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius

theorem _root_.AdversarialBco.Bit.sc_incl_quad {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) (a y : Fin n → ℝ)
    (ha : a ≠ 0) (ρ κ : ℝ) :
    (y + (ρ / Real.sqrt (a ⬝ᵥ (A *ᵥ a))) • (A *ᵥ a)) ⬝ᵥ
        ((A⁻¹ + κ • vecMulVec a a) *ᵥ (y + (ρ / Real.sqrt (a ⬝ᵥ (A *ᵥ a))) • (A *ᵥ a))) =
      y ⬝ᵥ (A⁻¹ *ᵥ y) + 2 * ρ * ((a ⬝ᵥ y) / Real.sqrt (a ⬝ᵥ (A *ᵥ a))) + ρ ^ 2 +
        κ * (a ⬝ᵥ (A *ᵥ a)) * ((a ⬝ᵥ y) / Real.sqrt (a ⬝ᵥ (A *ᵥ a)) + ρ) ^ 2 := by
  set q := a ⬝ᵥ (A *ᵥ a) with hq_def
  have hq_pos : 0 < q := by
    have := hA.dotProduct_mulVec_pos ha
    simpa [hq_def] using this
  set t := Real.sqrt q with ht_def
  have ht_pos : 0 < t := Real.sqrt_pos.mpr hq_pos
  have htsq : t ^ 2 = q := Real.sq_sqrt (by positivity)
  have hAinv : Invertible A := hA.isUnit.invertible
  have hAinv_u : A⁻¹ *ᵥ (A *ᵥ a) = a := by
    rw [Matrix.mulVec_mulVec, Matrix.inv_mul_of_invertible, Matrix.one_mulVec]
  have hAinv_symm : A⁻¹.IsHermitian := IsHermitian.inv hA.1
  have hAinv_transpose : A⁻¹ᵀ = A⁻¹ := by
    simpa [conjTranspose_eq_transpose_of_trivial] using hAinv_symm.eq
  have h_dot_mulVec_eq (M : Matrix (Fin n) (Fin n) ℝ) (u y : Fin n → ℝ) : u ⬝ᵥ (M *ᵥ y) = (Mᵀ *ᵥ u) ⬝ᵥ y := by
    rw [dotProduct_mulVec]
    have h : u ᵥ* M = Mᵀ *ᵥ u := by
      calc
        u ᵥ* M = u ᵥ* (Mᵀ)ᵀ := by simp
        _ = Mᵀ *ᵥ u := by rw [vecMul_transpose]
    rw [h]
  have h_u_dot_Ainv_y : (A *ᵥ a) ⬝ᵥ (A⁻¹ *ᵥ y) = a ⬝ᵥ y := by
    rw [h_dot_mulVec_eq A⁻¹ (A *ᵥ a) y, hAinv_transpose, hAinv_u]
  have h_u_dot_Ainv_u : (A *ᵥ a) ⬝ᵥ (A⁻¹ *ᵥ (A *ᵥ a)) = q := by
    rw [h_dot_mulVec_eq A⁻¹ (A *ᵥ a) (A *ᵥ a), hAinv_transpose, hAinv_u, hq_def]
  have h_y_dot_Ainv_u : y ⬝ᵥ (A⁻¹ *ᵥ (A *ᵥ a)) = a ⬝ᵥ y := by
    rw [h_dot_mulVec_eq A⁻¹ y (A *ᵥ a), hAinv_transpose]
    rw [dotProduct_comm, h_u_dot_Ainv_y]
  set u := A *ᵥ a with hu_def
  set z := y + (ρ / t) • u with hz_def
  have hz_Ainv_z : z ⬝ᵥ (A⁻¹ *ᵥ z) = y ⬝ᵥ (A⁻¹ *ᵥ y) + 2 * ρ * ((a ⬝ᵥ y) / t) + ρ ^ 2 := by
    calc
      z ⬝ᵥ (A⁻¹ *ᵥ z) = (y + (ρ / t) • u) ⬝ᵥ (A⁻¹ *ᵥ (y + (ρ / t) • u)) := rfl
      _ = (y + (ρ / t) • u) ⬝ᵥ (A⁻¹ *ᵥ y + A⁻¹ *ᵥ ((ρ / t) • u)) := by rw [mulVec_add]
      _ = (y + (ρ / t) • u) ⬝ᵥ (A⁻¹ *ᵥ y + (ρ / t) • (A⁻¹ *ᵥ u)) := by rw [mulVec_smul]
      _ = (y + (ρ / t) • u) ⬝ᵥ (A⁻¹ *ᵥ y) + (y + (ρ / t) • u) ⬝ᵥ ((ρ / t) • (A⁻¹ *ᵥ u)) := by rw [dotProduct_add]
      _ = (y ⬝ᵥ (A⁻¹ *ᵥ y) + ((ρ / t) • u) ⬝ᵥ (A⁻¹ *ᵥ y)) + (y ⬝ᵥ ((ρ / t) • (A⁻¹ *ᵥ u)) + ((ρ / t) • u) ⬝ᵥ ((ρ / t) • (A⁻¹ *ᵥ u))) := by
        simp [add_dotProduct, mul_add]
      _ = (y ⬝ᵥ (A⁻¹ *ᵥ y) + (ρ / t) * (u ⬝ᵥ (A⁻¹ *ᵥ y))) + ((ρ / t) * (y ⬝ᵥ (A⁻¹ *ᵥ u)) + ((ρ / t) * (ρ / t)) * (u ⬝ᵥ (A⁻¹ *ᵥ u))) := by
        simp [dotProduct_smul, smul_dotProduct, mul_assoc]
      _ = (y ⬝ᵥ (A⁻¹ *ᵥ y) + (ρ / t) * (a ⬝ᵥ y)) + ((ρ / t) * (y ⬝ᵥ a) + ((ρ / t) ^ 2) * q) := by
        rw [h_u_dot_Ainv_y, h_u_dot_Ainv_u, h_y_dot_Ainv_u, dotProduct_comm y a, hq_def]
        ring
      _ = (y ⬝ᵥ (A⁻¹ *ᵥ y) + (ρ / t) * (a ⬝ᵥ y)) + ((ρ / t) * (a ⬝ᵥ y) + ((ρ / t) ^ 2) * q) := by
        rw [dotProduct_comm y a]
      _ = y ⬝ᵥ (A⁻¹ *ᵥ y) + 2 * (ρ / t) * (a ⬝ᵥ y) + ((ρ / t) ^ 2) * q := by ring
      _ = y ⬝ᵥ (A⁻¹ *ᵥ y) + 2 * ρ * ((a ⬝ᵥ y) / t) + ρ ^ 2 := by
        field_simp [ht_pos.ne.symm]
        nlinarith [htsq]
  have hz_vecMulVec_z : z ⬝ᵥ (vecMulVec a a *ᵥ z) = q * ((a ⬝ᵥ y) / t + ρ) ^ 2 := by
    calc
      z ⬝ᵥ (vecMulVec a a *ᵥ z) = z ⬝ᵥ ((a ⬝ᵥ z) • a) := by
        rw [vecMulVec_mulVec]
        simp
      _ = (a ⬝ᵥ z) * (z ⬝ᵥ a) := by
        rw [dotProduct_smul, smul_eq_mul]
      _ = (a ⬝ᵥ z) * (a ⬝ᵥ z) := by rw [dotProduct_comm z a]
      _ = (a ⬝ᵥ z) ^ 2 := by ring
      _ = (a ⬝ᵥ (y + (ρ / t) • u)) ^ 2 := rfl
      _ = (a ⬝ᵥ y + (ρ / t) * (a ⬝ᵥ u)) ^ 2 := by
        simp [dotProduct_add, dotProduct_smul]
      _ = (a ⬝ᵥ y + (ρ / t) * q) ^ 2 := by rw [hu_def, hq_def]
      _ = (t * ((a ⬝ᵥ y) / t + ρ)) ^ 2 := by
        have h : a ⬝ᵥ y + (ρ / t) * q = t * ((a ⬝ᵥ y) / t + ρ) := by
          field_simp [ht_pos.ne.symm]
          calc
            a ⬝ᵥ y * t + ρ * q = a ⬝ᵥ y * t + ρ * (t ^ 2) := by rw [htsq]
            _ = t * (a ⬝ᵥ y + ρ * t) := by ring
        rw [h]
      _ = t ^ 2 * ((a ⬝ᵥ y) / t + ρ) ^ 2 := by ring
      _ = q * ((a ⬝ᵥ y) / t + ρ) ^ 2 := by rw [htsq]
  calc
    (y + (ρ / t) • (A *ᵥ a)) ⬝ᵥ ((A⁻¹ + κ • vecMulVec a a) *ᵥ (y + (ρ / t) • (A *ᵥ a))) =
        z ⬝ᵥ ((A⁻¹ + κ • vecMulVec a a) *ᵥ z) := rfl
    _ = z ⬝ᵥ (A⁻¹ *ᵥ z + κ • (vecMulVec a a *ᵥ z)) := by rw [add_mulVec, smul_mulVec]
    _ = z ⬝ᵥ (A⁻¹ *ᵥ z) + z ⬝ᵥ (κ • (vecMulVec a a *ᵥ z)) := by rw [dotProduct_add]
    _ = z ⬝ᵥ (A⁻¹ *ᵥ z) + κ * (z ⬝ᵥ (vecMulVec a a *ᵥ z)) := by
      rw [dotProduct_smul, smul_eq_mul]
    _ = (y ⬝ᵥ (A⁻¹ *ᵥ y) + 2 * ρ * ((a ⬝ᵥ y) / t) + ρ ^ 2) + κ * (q * ((a ⬝ᵥ y) / t + ρ) ^ 2) := by
      rw [hz_Ainv_z, hz_vecMulVec_z]
    _ = y ⬝ᵥ (A⁻¹ *ᵥ y) + 2 * ρ * ((a ⬝ᵥ y) / t) + ρ ^ 2 + κ * (a ⬝ᵥ (A *ᵥ a)) * ((a ⬝ᵥ y) / t + ρ) ^ 2 := by
      simp [hq_def, hu_def, mul_assoc]

end AdversarialBco.Bit.Aux_sc_incl_quad

namespace AdversarialBco.Bit.Aux_sc_incl_cs


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius

theorem _root_.AdversarialBco.Bit.sc_incl_cs {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) (a y : Fin n → ℝ) :
    (a ⬝ᵥ y) ^ 2 ≤ (a ⬝ᵥ (A *ᵥ a)) * (y ⬝ᵥ (A⁻¹ *ᵥ y)) := by
  have hA_unit : IsUnit A := hA.isUnit
  have hA_det_unit : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hA_unit
  have h_mul : A *ᵥ (A⁻¹ *ᵥ y) = y := by
    calc
      A *ᵥ (A⁻¹ *ᵥ y) = (A * A⁻¹) *ᵥ y := by rw [Matrix.mulVec_mulVec]
      _ = 1 *ᵥ y := by rw [Matrix.mul_nonsing_inv A hA_det_unit]
      _ = y := by simp
  set w := A⁻¹ *ᵥ y with hw
  have hy_eq : A *ᵥ w = y := h_mul
  have h1 : a ⬝ᵥ y = a ⬝ᵥ (A *ᵥ w) := by rw [hy_eq]
  have h2 : y ⬝ᵥ (A⁻¹ *ᵥ y) = w ⬝ᵥ (A *ᵥ w) := by
    calc
      y ⬝ᵥ (A⁻¹ *ᵥ y) = (A *ᵥ w) ⬝ᵥ w := by rw [hy_eq, hw]
      _ = w ⬝ᵥ (A *ᵥ w) := by rw [dotProduct_comm]
  rw [h1, h2]
  have h_cs := hA.star_dotProduct_mulVec_mul_le a w
  simpa [star_trivial, pow_two] using h_cs

end AdversarialBco.Bit.Aux_sc_incl_cs

namespace AdversarialBco.Bit.Aux_sc_incl


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius

theorem _root_.AdversarialBco.Bit.sc_incl {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) (a c x : Fin n → ℝ)
    (ha : a ≠ 0) (d β ρ σ τ : ℝ) (hd : 2 ≤ d) (hβ0 : 0 ≤ β) (hβd : d * β < 1)
    (hρ : ρ = (1 - d * β) / (d + 1)) (hσ : σ = d ^ 2 * (1 - β ^ 2) / (d ^ 2 - 1))
    (hτ : τ = 2 * (1 - d * β) / ((d + 1) * (1 - β)))
    (hx : (x - c) ⬝ᵥ (A⁻¹ *ᵥ (x - c)) ≤ 1) (hcut : a ⬝ᵥ (x - c) ≤ β * Real.sqrt (a ⬝ᵥ (A *ᵥ a))) :
    (x - (c - (ρ / Real.sqrt (a ⬝ᵥ (A *ᵥ a))) • (A *ᵥ a))) ⬝ᵥ
        ((σ • (A - (τ / (a ⬝ᵥ (A *ᵥ a))) • vecMulVec (A *ᵥ a) (A *ᵥ a)))⁻¹ *ᵥ
          (x - (c - (ρ / Real.sqrt (a ⬝ᵥ (A *ᵥ a))) • (A *ᵥ a)))) ≤ 1 := by
  have hqpos : 0 < a ⬝ᵥ (A *ᵥ a) := by
    have h := Matrix.PosDef.dotProduct_mulVec_pos hA ha
    simpa [starRingEnd_apply] using h
  have hqnezero : a ⬝ᵥ (A *ᵥ a) ≠ 0 := by linarith
  set q := a ⬝ᵥ (A *ᵥ a) with hqdef
  set t := Real.sqrt q with htdef
  have htpos : 0 < t := Real.sqrt_pos.mpr hqpos
  have htsq : t ^ 2 = q := Real.sq_sqrt hqpos.le
  set y := x - c with hydef
  set p := y ⬝ᵥ (A⁻¹ *ᵥ y) with hpdef
  set s := (a ⬝ᵥ y) / t with hsdef
  have hsβ : s ≤ β := by
    rw [hsdef, div_le_iff₀ htpos]
    simpa [hydef, htdef, hqdef] using hcut
  have hsp : s ^ 2 ≤ p := by
    rw [hsdef, hpdef]
    have hcs := sc_incl_cs A hA a y
    rw [← hqdef, ← hpdef] at hcs
    calc
      ((a ⬝ᵥ y) / t) ^ 2 = (a ⬝ᵥ y) ^ 2 / t ^ 2 := by ring
      _ = (a ⬝ᵥ y) ^ 2 / q := by rw [htsq]
      _ ≤ (q * p) / q := by
        gcongr
      _ = p := by field_simp [hqnezero]
  have hσpos : 0 < σ := by
    rw [hσ]
    have hdpos : 0 < d := by linarith
    have hβlt1 : β < 1 := by nlinarith
    have hnum : 0 < d ^ 2 * (1 - β ^ 2) := by
      have h1 : 0 < d ^ 2 := pow_pos hdpos 2
      have h2 : 0 < 1 - β ^ 2 := by nlinarith
      exact mul_pos h1 h2
    have hden : 0 < d ^ 2 - 1 := by nlinarith
    exact div_pos hnum hden
  have hσnezero : σ ≠ 0 := by linarith
  have hτnezero : τ ≠ 1 := by
    rw [hτ]
    have hdenpos : 0 < (d + 1) * (1 - β) := by
      have hβlt1 : β < 1 := by nlinarith
      nlinarith
    have hlt : 2 * (1 - d * β) / ((d + 1) * (1 - β)) < 1 := by
      refine (div_lt_one hdenpos).mpr ?_
      nlinarith
    linarith
  have hτpos : 0 < 1 - τ := by
    -- Since τ = 2*(1-dβ)/((d+1)*(1-β)) and dβ < 1, we have τ < 1
    -- Actually, we need 1 - τ > 0
    rw [hτ]
    have hβlt1 : β < 1 := by nlinarith
    have hnum : 0 < 2 * (1 - d * β) := by nlinarith
    have hden : 0 < (d + 1) * (1 - β) := by nlinarith
    have hτ_lt_one : 2 * (1 - d * β) / ((d + 1) * (1 - β)) < 1 := by
      refine (div_lt_one ?_).mpr ?_
      · exact hden
      · nlinarith
    linarith
  have h_main : (x - (c - (ρ / Real.sqrt (a ⬝ᵥ (A *ᵥ a))) • (A *ᵥ a))) ⬝ᵥ
        ((σ • (A - (τ / (a ⬝ᵥ (A *ᵥ a))) • vecMulVec (A *ᵥ a) (A *ᵥ a)))⁻¹ *ᵥ
          (x - (c - (ρ / Real.sqrt (a ⬝ᵥ (A *ᵥ a))) • (A *ᵥ a)))) =
      (p + 2 * ρ * s + ρ ^ 2 + (τ / (1 - τ)) * (s + ρ) ^ 2) / σ := by
    set κ := τ / ((1 - τ) * q) with hκdef
    have hvec : x - (c - (ρ / Real.sqrt (a ⬝ᵥ (A *ᵥ a))) • (A *ᵥ a)) = y + (ρ / t) • (A *ᵥ a) := by
      calc
        x - (c - (ρ / Real.sqrt (a ⬝ᵥ (A *ᵥ a))) • (A *ᵥ a)) =
            (x - c) + (ρ / Real.sqrt (a ⬝ᵥ (A *ᵥ a))) • (A *ᵥ a) := by
          abel
        _ = y + (ρ / t) • (A *ᵥ a) := by
          simp [hydef, htdef, hqdef]
    have hinv : (σ • (A - (τ / (a ⬝ᵥ (A *ᵥ a))) • vecMulVec (A *ᵥ a) (A *ᵥ a)))⁻¹ =
        σ⁻¹ • (A⁻¹ + κ • vecMulVec a a) := by
      rw [sc_incl_inv A hA a ha σ τ hσnezero hτnezero, hκdef, hqdef]
    have hκq : κ * q = τ / (1 - τ) := by
      rw [hκdef]
      calc
        (τ / ((1 - τ) * q)) * q = τ * q / ((1 - τ) * q) := by
          rw [div_mul_eq_mul_div]
        _ = τ / (1 - τ) := by
          rw [mul_div_mul_right τ (1 - τ) hqnezero]
    have hform : (y + (ρ / t) • (A *ᵥ a)) ⬝ᵥ
        ((A⁻¹ + κ • vecMulVec a a) *ᵥ (y + (ρ / t) • (A *ᵥ a))) =
        p + 2 * ρ * s + ρ ^ 2 + (τ / (1 - τ)) * (s + ρ) ^ 2 := by
      rw [sc_incl_quad A hA a y ha ρ κ]
      rw [hpdef, hsdef, htdef, hqdef]
      -- Goal: p + 2*ρ*s + ρ^2 + κ * q * (s+ρ)^2 = p + 2*ρ*s + ρ^2 + (τ/(1-τ))*(s+ρ)^2
      -- But κ is still present; we need to rewrite it too
      rw [hκdef]
      -- Goal: p + 2*ρ*s + ρ^2 + (τ/((1-τ)*q))*q*(s+ρ)^2 = p + 2*ρ*s + ρ^2 + (τ/(1-τ))*(s+ρ)^2
      calc
        p + 2 * ρ * s + ρ ^ 2 + (τ / ((1 - τ) * q)) * q * (s + ρ) ^ 2
            = p + 2 * ρ * s + ρ ^ 2 + ((τ / ((1 - τ) * q)) * q) * (s + ρ) ^ 2 := by ring
        _ = p + 2 * ρ * s + ρ ^ 2 + (τ / (1 - τ)) * (s + ρ) ^ 2 := by rw [hκq]
    calc
      (x - (c - (ρ / Real.sqrt (a ⬝ᵥ (A *ᵥ a))) • (A *ᵥ a))) ⬝ᵥ
          ((σ • (A - (τ / (a ⬝ᵥ (A *ᵥ a))) • vecMulVec (A *ᵥ a) (A *ᵥ a)))⁻¹ *ᵥ
            (x - (c - (ρ / Real.sqrt (a ⬝ᵥ (A *ᵥ a))) • (A *ᵥ a)))) =
        (y + (ρ / t) • (A *ᵥ a)) ⬝ᵥ
          ((σ • (A - (τ / (a ⬝ᵥ (A *ᵥ a))) • vecMulVec (A *ᵥ a) (A *ᵥ a)))⁻¹ *ᵥ
            (y + (ρ / t) • (A *ᵥ a))) := by
        simp [hvec]
      _ = (y + (ρ / t) • (A *ᵥ a)) ⬝ᵥ
          ((σ⁻¹ • (A⁻¹ + κ • vecMulVec a a)) *ᵥ (y + (ρ / t) • (A *ᵥ a))) := by rw [hinv]
      _ = (y + (ρ / t) • (A *ᵥ a)) ⬝ᵥ
          (σ⁻¹ • ((A⁻¹ + κ • vecMulVec a a) *ᵥ (y + (ρ / t) • (A *ᵥ a)))) := by
        rw [Matrix.smul_mulVec]
      _ = σ⁻¹ • ((y + (ρ / t) • (A *ᵥ a)) ⬝ᵥ
          ((A⁻¹ + κ • vecMulVec a a) *ᵥ (y + (ρ / t) • (A *ᵥ a)))) := by
        rw [dotProduct_smul]
      _ = σ⁻¹ • (p + 2 * ρ * s + ρ ^ 2 + (τ / (1 - τ)) * (s + ρ) ^ 2) := by rw [hform]
      _ = (p + 2 * ρ * s + ρ ^ 2 + (τ / (1 - τ)) * (s + ρ) ^ 2) / σ := by ring
  rw [h_main]
  exact sc_incl_scalar d β ρ σ τ p s hd hβ0 hβd hρ hσ hτ hsp (by
    -- need p ≤ 1, which is hx since p = (x-c) ⬝ᵥ (A⁻¹ *ᵥ (x-c))
    simpa [hpdef, hydef] using hx) hsβ

end AdversarialBco.Bit.Aux_sc_incl

namespace AdversarialBco.Bit.Aux_sc_det


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius

theorem _root_.AdversarialBco.Bit.sc_det {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det) (hAt : Aᵀ = A)
    (a : Fin n → ℝ) (σ τ : ℝ) (hq : a ⬝ᵥ (A *ᵥ a) ≠ 0) :
    (σ • (A - (τ / (a ⬝ᵥ (A *ᵥ a))) • vecMulVec (A *ᵥ a) (A *ᵥ a))).det = σ ^ n * (1 - τ) * A.det := by
  set u := A *ᵥ a with hu
  set q := a ⬝ᵥ u with hq_def
  have hq_ne : q ≠ 0 := hq
  have h_inv : A⁻¹ *ᵥ u = a := by
    calc
      A⁻¹ *ᵥ u = A⁻¹ *ᵥ (A *ᵥ a) := rfl
      _ = (A⁻¹ * A) *ᵥ a := by rw [Matrix.mulVec_mulVec]
      _ = 1 *ᵥ a := by rw [Matrix.nonsing_inv_mul A hA]
      _ = a := by simp
  have h_symm : A⁻¹ᵀ = A⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, hAt]
  have h_entry_eq : ∀ i j, A⁻¹ i j = A⁻¹ j i := by
    intro i j
    calc
      A⁻¹ i j = (A⁻¹ᵀ) j i := by rw [Matrix.transpose_apply]
      _ = A⁻¹ j i := by rw [h_symm]
  have h_row_symm : replicateRow Unit u * A⁻¹ = replicateRow Unit a := by
    ext i j
    rw [Matrix.mul_apply', Matrix.replicateRow_apply, ← h_inv, Matrix.mulVec_apply]
    simp [dotProduct, h_entry_eq, mul_comm]
  have h_entry : (replicateRow Unit u * A⁻¹ * replicateCol Unit ((-(τ / q)) • u)) default default = -τ := by
    rw [h_row_symm]
    rw [Matrix.replicateRow_mul_replicateCol_apply]
    rw [dotProduct_smul, smul_eq_mul, hq_def]
    calc
      (-(τ / q)) * q = -(τ / q * q) := by ring
      _ = -τ := by field_simp [hq_ne]
  have h_det_one_add : ((1 : Matrix Unit Unit ℝ) + replicateRow Unit u * A⁻¹ *
      replicateCol Unit ((-(τ / q)) • u)).det = 1 - τ := by
    rw [h_row_symm]
    have h_det := Matrix.det_unique ((1 : Matrix Unit Unit ℝ) + replicateRow Unit a *
      replicateCol Unit ((-(τ / q)) • u))
    have h_entry' : (replicateRow Unit a * replicateCol Unit ((-(τ / q)) • u)) default default = -τ := by
      rw [Matrix.replicateRow_mul_replicateCol_apply]
      rw [dotProduct_smul, smul_eq_mul, hq_def]
      calc
        (-(τ / q)) * q = -(τ / q * q) := by ring
        _ = -τ := by field_simp [hq_ne]
    rw [h_det, Matrix.add_apply, Matrix.one_apply_eq, h_entry']
    ring
  calc
    (σ • (A - (τ / q) • vecMulVec u u)).det = (σ ^ n) * (A - (τ / q) • vecMulVec u u).det := by
      rw [Matrix.det_smul, Fintype.card_fin]
    _ = (σ ^ n) * (A + (-(τ / q)) • vecMulVec u u).det := by
      rw [sub_eq_add_neg, neg_smul]
    _ = (σ ^ n) * (A + (replicateCol Unit ((-(τ / q)) • u) * replicateRow Unit u)).det := by
      rw [Matrix.vecMulVec_eq (ι := Unit) u u, ← Matrix.smul_mul, Matrix.replicateCol_smul]
    _ = (σ ^ n) * (A.det * (1 + replicateRow Unit u * A⁻¹ * replicateCol Unit ((-(τ / q)) • u)).det) := by
      rw [Matrix.det_add_mul (replicateCol Unit ((-(τ / q)) • u)) (replicateRow Unit u) hA]
    _ = (σ ^ n) * (A.det * (1 - τ)) := by
      rw [h_det_one_add]
    _ = σ ^ n * (1 - τ) * A.det := by ring

end AdversarialBco.Bit.Aux_sc_det

namespace AdversarialBco.Bit.Aux_sc_vol_alg


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius

theorem _root_.AdversarialBco.Bit.sc_vol_alg (d : ℕ) (β σ τ : ℝ) (hd : 2 ≤ d) (hβ0 : 0 ≤ β) (hβd : (d : ℝ) * β < 1)
    (hσ : σ = (d : ℝ) ^ 2 * (1 - β ^ 2) / ((d : ℝ) ^ 2 - 1))
    (hτ : τ = 2 * (1 - d * β) / (((d : ℝ) + 1) * (1 - β))) :
    σ = (1 - (1 - d * β) / ((d : ℝ) + 1)) * (1 + (1 - d * β) / ((d : ℝ) - 1)) ∧
      1 - τ = (1 - (1 - d * β) / ((d : ℝ) + 1)) / (1 + (1 - d * β) / ((d : ℝ) - 1)) := by
  subst hσ hτ
  have hd' : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have h_den1 : (d : ℝ) + 1 ≠ 0 := by linarith
  have h_den2 : (d : ℝ) - 1 ≠ 0 := by linarith
  have h_den3 : (d : ℝ) ^ 2 - 1 ≠ 0 := by
    nlinarith
  have hβ_lt_one : β < 1 := by
    -- from hβd: d*β < 1 and d ≥ 2, so β < 1/2 < 1
    nlinarith
  have h_den4 : 1 - β ≠ 0 := by linarith
  constructor
  · field_simp [h_den1, h_den2, h_den3]
    ring
  · have h_denom : (d : ℝ) - 1 + (1 - (d : ℝ) * β) ≠ 0 := by
      have : (d : ℝ) - 1 + (1 - (d : ℝ) * β) = (d : ℝ) * (1 - β) := by ring
      rw [this]
      have hdpos : 0 < (d : ℝ) := by exact_mod_cast (show 0 < d from by omega)
      have h1βpos : 0 < 1 - β := by linarith
      nlinarith
    field_simp [h_den1, h_den2, h_den4, h_denom]
    ring

end AdversarialBco.Bit.Aux_sc_vol_alg

namespace AdversarialBco.Bit.Aux_sc_vol_deriv


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius

theorem _root_.AdversarialBco.Bit.sc_vol_deriv (D s : ℝ) (hD : 2 ≤ D) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    HasDerivAt (fun x : ℝ => (D + 1) / 2 * Real.log (1 - x / (D + 1)) + (D - 1) / 2 * Real.log (1 + x / (D - 1)) +
      x ^ 2 / (2 * D)) (s * (1 / D - D / ((D + 1 - s) * (D - 1 + s)))) s := by
  have hDpos : 0 < D := by linarith
  have hDne0 : D ≠ 0 := by linarith
  have hDp1ne0 : D + 1 ≠ 0 := by linarith
  have hDm1ne0 : D - 1 ≠ 0 := by linarith
  have hDp1ms_pos : 0 < D + 1 - s := by
    have : s ≤ 1 := hs1
    linarith
  have hDm1ps_pos : 0 < D - 1 + s := by
    have : 2 ≤ D := hD
    linarith
  have hDp1ms_ne0 : D + 1 - s ≠ 0 := by linarith
  have hDm1ps_ne0 : D - 1 + s ≠ 0 := by linarith
  have hlog1_ne0 : 1 - s / (D + 1) ≠ 0 := by
    have : 1 - s / (D + 1) = (D + 1 - s) / (D + 1) := by
      field_simp [hDp1ne0]
    rw [this]
    exact div_ne_zero hDp1ms_ne0 hDp1ne0
  have hlog2_ne0 : 1 + s / (D - 1) ≠ 0 := by
    have : 1 + s / (D - 1) = (D - 1 + s) / (D - 1) := by
      field_simp [hDm1ne0]
    rw [this]
    exact div_ne_zero hDm1ps_ne0 hDm1ne0
  have h_deriv : HasDerivAt (fun x : ℝ => (D + 1) / 2 * Real.log (1 - x / (D + 1)) + (D - 1) / 2 * Real.log (1 + x / (D - 1)) +
      x ^ 2 / (2 * D)) (s * (1 / D - D / ((D + 1 - s) * (D - 1 + s)))) s := by
    have h1 : HasDerivAt (fun x : ℝ => (D + 1) / 2 * Real.log (1 - x / (D + 1))) (-(D + 1) / (2 * (D + 1 - s))) s := by
      have h_inner : HasDerivAt (fun x : ℝ => 1 - x / (D + 1)) (-(1 / (D + 1))) s := by
        have h_div : HasDerivAt (fun x : ℝ => x / (D + 1)) (1 / (D + 1)) s := by
          simpa using (hasDerivAt_id s).div_const (D + 1)
        have h_const : HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 s := hasDerivAt_const s (1 : ℝ)
        have h_sub := HasDerivAt.sub h_const h_div
        -- h_sub : HasDerivAt ((fun _ => 1) - (fun x => x / (D + 1))) (0 - (1 / (D + 1))) s
        -- We need: HasDerivAt (fun x => 1 - x / (D + 1)) (-(1 / (D + 1))) s
        have h_inner' : (fun x : ℝ => 1 - x / (D + 1)) = ((fun _ : ℝ => (1 : ℝ)) - fun x : ℝ => x / (D + 1)) := by
          ext x; rfl
        have h_deriv' : (-(1 / (D + 1))) = (0 : ℝ) - (1 / (D + 1)) := by ring
        rw [h_inner', h_deriv']
        exact h_sub
      have h_log : HasDerivAt (fun x : ℝ => Real.log (1 - x / (D + 1))) ((-(1 / (D + 1))) / (1 - s / (D + 1))) s :=
        HasDerivAt.log h_inner hlog1_ne0
      have h_const_mul : HasDerivAt (fun x : ℝ => (D + 1) / 2 * Real.log (1 - x / (D + 1)))
          ((D + 1) / 2 * ((-(1 / (D + 1))) / (1 - s / (D + 1)))) s :=
        HasDerivAt.const_mul ((D + 1) / 2) h_log
      convert h_const_mul using 1
      field_simp [hDp1ne0, hDp1ms_ne0]
    have h2 : HasDerivAt (fun x : ℝ => (D - 1) / 2 * Real.log (1 + x / (D - 1))) ((D - 1) / (2 * (D - 1 + s))) s := by
      have h_inner : HasDerivAt (fun x : ℝ => 1 + x / (D - 1)) (1 / (D - 1)) s := by
        have h_div : HasDerivAt (fun x : ℝ => x / (D - 1)) (1 / (D - 1)) s := by
          simpa using (hasDerivAt_id s).div_const (D - 1)
        have h_const : HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 s := hasDerivAt_const s (1 : ℝ)
        have h_add := HasDerivAt.add h_const h_div
        have h_inner' : (fun x : ℝ => 1 + x / (D - 1)) = ((fun _ : ℝ => (1 : ℝ)) + fun x : ℝ => x / (D - 1)) := by
          ext x; rfl
        have h_deriv' : (1 / (D - 1)) = (0 : ℝ) + (1 / (D - 1)) := by ring
        rw [h_inner', h_deriv']
        exact h_add
      have h_log : HasDerivAt (fun x : ℝ => Real.log (1 + x / (D - 1))) ((1 / (D - 1)) / (1 + s / (D - 1))) s :=
        HasDerivAt.log h_inner hlog2_ne0
      have h_const_mul : HasDerivAt (fun x : ℝ => (D - 1) / 2 * Real.log (1 + x / (D - 1)))
          ((D - 1) / 2 * ((1 / (D - 1)) / (1 + s / (D - 1)))) s :=
        HasDerivAt.const_mul ((D - 1) / 2) h_log
      convert h_const_mul using 1
      field_simp [hDm1ne0, hDm1ps_ne0]
    have h3 : HasDerivAt (fun x : ℝ => x ^ 2 / (2 * D)) (s / D) s := by
      have h_sq : HasDerivAt (fun x : ℝ => x ^ 2) (2 * s) s := by
        simpa using (hasDerivAt_pow 2 s)
      have h_div : HasDerivAt (fun x : ℝ => x ^ 2 / (2 * D)) ((2 * s) / (2 * D)) s :=
        HasDerivAt.div_const h_sq (2 * D)
      convert h_div using 1
      field_simp [hDne0]
    have h_sum12 : HasDerivAt (fun x : ℝ => (D + 1) / 2 * Real.log (1 - x / (D + 1)) + (D - 1) / 2 * Real.log (1 + x / (D - 1)))
        (-(D + 1) / (2 * (D + 1 - s)) + (D - 1) / (2 * (D - 1 + s))) s :=
      HasDerivAt.add h1 h2
    have h_total : HasDerivAt (fun x : ℝ => (D + 1) / 2 * Real.log (1 - x / (D + 1)) + (D - 1) / 2 * Real.log (1 + x / (D - 1)) +
        x ^ 2 / (2 * D)) ((-(D + 1) / (2 * (D + 1 - s)) + (D - 1) / (2 * (D - 1 + s))) + s / D) s :=
      HasDerivAt.add h_sum12 h3
    convert h_total using 1
    field_simp [hDne0, hDp1ms_ne0, hDm1ps_ne0]
    ring
  exact h_deriv

end AdversarialBco.Bit.Aux_sc_vol_deriv

namespace AdversarialBco.Bit.Aux_sc_vol_h


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius

theorem _root_.AdversarialBco.Bit.sc_vol_h (D t : ℝ) (hD : 2 ≤ D) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (D + 1) / 2 * Real.log (1 - t / (D + 1)) + (D - 1) / 2 * Real.log (1 + t / (D - 1)) ≤ -t ^ 2 / (2 * D) := by
  set h := fun x : ℝ => (D + 1) / 2 * Real.log (1 - x / (D + 1)) + (D - 1) / 2 * Real.log (1 + x / (D - 1)) + x ^ 2 / (2 * D) with hh
  have h0 : h 0 = 0 := by
    simp [h]
  have hDpos : 0 < D := by linarith
  have hderiv : ∀ x, 0 ≤ x → x ≤ 1 → HasDerivAt h (x * (1 / D - D / ((D + 1 - x) * (D - 1 + x)))) x := by
    intro x hx0 hx1
    simpa [h, hh] using AdversarialBco.Bit.sc_vol_deriv D x hD hx0 hx1
  have h_cont : ContinuousOn h (Set.Icc (0 : ℝ) 1) := by
    intro x hx
    have hx0 : 0 ≤ x := hx.1
    have hx1 : x ≤ 1 := hx.2
    exact (hderiv x hx0 hx1).continuousAt.continuousWithinAt
  have h_diff : DifferentiableOn ℝ h (interior (Set.Icc (0 : ℝ) 1)) := by
    rw [interior_Icc]
    intro x hx
    rcases hx with ⟨hx0, hx1⟩
    exact (hderiv x (by linarith) (by linarith)).differentiableAt.differentiableWithinAt
  have h_deriv_nonpos : ∀ x ∈ interior (Set.Icc (0 : ℝ) 1), deriv h x ≤ 0 := by
    rw [interior_Icc]
    intro x hx
    rcases hx with ⟨hx0, hx1⟩
    have hderiv_at := hderiv x (by linarith) (by linarith)
    rw [hderiv_at.deriv]
    have hpos_prod : 0 < (D + 1 - x) * (D - 1 + x) := by
      have h1 : 0 < D + 1 - x := by linarith
      have h2 : 0 < D - 1 + x := by linarith
      exact mul_pos h1 h2
    have hle : (D + 1 - x) * (D - 1 + x) ≤ D ^ 2 := by
      have : (D + 1 - x) * (D - 1 + x) = D ^ 2 - (1 - x) ^ 2 := by ring
      rw [this]
      nlinarith
    have h_inner_nonpos : 1 / D - D / ((D + 1 - x) * (D - 1 + x)) ≤ 0 := by
      have h_one_div_le : 1 / D ≤ D / ((D + 1 - x) * (D - 1 + x)) := by
        calc
          1 / D = D / (D ^ 2) := by field_simp [hDpos.ne']
          _ ≤ D / ((D + 1 - x) * (D - 1 + x)) :=
            div_le_div_of_nonneg_left (by linarith) hpos_prod hle
      linarith
    nlinarith
  have h_antitone : AntitoneOn h (Set.Icc (0 : ℝ) 1) :=
    antitoneOn_of_deriv_nonpos (convex_Icc (0 : ℝ) 1) h_cont h_diff h_deriv_nonpos
  have h0_mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> norm_num
  have ht_mem : t ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> linarith
  have h_ineq : h t ≤ h 0 := h_antitone h0_mem ht_mem (by linarith)
  have hgoal : h t ≤ 0 := by linarith
  unfold h at hgoal
  have htemp := add_le_add_right hgoal (-(t ^ 2 / (2 * D)))
  simpa [add_comm, add_left_comm, add_assoc, add_neg_cancel_right, zero_add, neg_div] using htemp

end AdversarialBco.Bit.Aux_sc_vol_h

namespace AdversarialBco.Bit.Aux_sc_volume


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius

theorem _root_.AdversarialBco.Bit.sc_volume (d : ℕ) (β σ τ : ℝ) (hd : 2 ≤ d) (hβ0 : 0 ≤ β) (hβd : (d : ℝ) * β < 1)
    (hσ : σ = (d : ℝ) ^ 2 * (1 - β ^ 2) / ((d : ℝ) ^ 2 - 1))
    (hτ : τ = 2 * (1 - d * β) / (((d : ℝ) + 1) * (1 - β))) :
    Real.sqrt (σ ^ d * (1 - τ)) ≤ Real.exp (-(1 - d * β) ^ 2 / (2 * d)) := by
  -- Cast d to ℝ for algebraic manipulations
  have hd_real : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hd_pos : 0 < (d : ℝ) := by linarith
  have hd_sub_one_pos : 0 < (d : ℝ) - 1 := by linarith
  have hd_add_one_pos : 0 < (d : ℝ) + 1 := by linarith
  have hd_ne_zero : (d : ℝ) ≠ 0 := by linarith
  have hd_sub_one_ne_zero : (d : ℝ) - 1 ≠ 0 := by linarith
  have hd_add_one_ne_zero : (d : ℝ) + 1 ≠ 0 := by linarith
  -- Define t = 1 - dβ
  set t := 1 - (d : ℝ) * β with ht_def
  have ht_pos : 0 < t := by
    rw [ht_def]
    linarith
  have ht_le_one : t ≤ 1 := by
    rw [ht_def]
    have h_nonneg : 0 ≤ (d : ℝ) * β := mul_nonneg (by exact_mod_cast (Nat.zero_le d)) hβ0
    linarith
  have ht_ne_zero : t ≠ 0 := by linarith
  -- Use the algebraic identities from sc_vol_alg
  rcases AdversarialBco.Bit.sc_vol_alg d β σ τ hd hβ0 hβd hσ hτ with ⟨hσ_eq, hτ_eq⟩
  -- Define a and b
  set a := 1 - t / ((d : ℝ) + 1) with ha_def
  set b := 1 + t / ((d : ℝ) - 1) with hb_def
  have ha_pos : 0 < a := by
    rw [ha_def]
    have hdiv : t / ((d : ℝ) + 1) < 1 := by
      refine (div_lt_one hd_add_one_pos).mpr ?_
      have : 1 < (d : ℝ) + 1 := by linarith
      linarith
    linarith
  have hb_pos : 0 < b := by
    rw [hb_def]
    have hdiv : 0 < t / ((d : ℝ) - 1) := div_pos ht_pos hd_sub_one_pos
    linarith
  have ha_ne_zero : a ≠ 0 := by linarith
  have hb_ne_zero : b ≠ 0 := by linarith
  have hσ_eq' : σ = a * b := by
    rw [hσ_eq, ha_def, hb_def]
  have h_one_minus_tau : 1 - τ = a / b := by
    rw [hτ_eq, ha_def, hb_def]
  -- The product is positive
  have h_prod_pos : 0 < σ ^ d * (1 - τ) := by
    rw [hσ_eq', h_one_minus_tau]
    have h_sigma_pos : 0 < a * b := mul_pos ha_pos hb_pos
    have h_pow_pos : 0 < (a * b) ^ d := pow_pos h_sigma_pos d
    have h_div_pos : 0 < a / b := div_pos ha_pos hb_pos
    exact mul_pos h_pow_pos h_div_pos
  have h_sigma_pow_ne_zero : σ ^ d ≠ 0 := by
    rw [hσ_eq']
    exact pow_ne_zero d (mul_ne_zero ha_ne_zero hb_ne_zero)
  have h_one_minus_tau_ne_zero : 1 - τ ≠ 0 := by
    rw [h_one_minus_tau]
    exact div_ne_zero ha_ne_zero hb_ne_zero
  -- Express log of the product in terms of a and b
  have h_log_prod : Real.log (σ ^ d * (1 - τ)) = ((d : ℝ) + 1) * Real.log a + ((d : ℝ) - 1) * Real.log b := by
    calc
      Real.log (σ ^ d * (1 - τ)) = Real.log (σ ^ d) + Real.log (1 - τ) := by
        rw [Real.log_mul h_sigma_pow_ne_zero h_one_minus_tau_ne_zero]
      _ = (d : ℝ) * Real.log σ + Real.log (1 - τ) := by
        rw [Real.log_pow]
      _ = (d : ℝ) * Real.log (a * b) + Real.log (a / b) := by rw [hσ_eq', h_one_minus_tau]
      _ = (d : ℝ) * (Real.log a + Real.log b) + (Real.log a - Real.log b) := by
        rw [Real.log_mul ha_ne_zero hb_ne_zero, Real.log_div ha_ne_zero hb_ne_zero]
      _ = ((d : ℝ) + 1) * Real.log a + ((d : ℝ) - 1) * Real.log b := by ring
  -- Apply sc_vol_h with D = d
  have h_sc_vol_h := AdversarialBco.Bit.sc_vol_h (d : ℝ) t hd_real (by linarith) ht_le_one
  -- h_sc_vol_h : ((d : ℝ) + 1) / 2 * Real.log a + ((d : ℝ) - 1) / 2 * Real.log b ≤ -t ^ 2 / (2 * (d : ℝ))
  rw [← ha_def, ← hb_def] at h_sc_vol_h
  -- h_sc_vol_h : ((d : ℝ) + 1) / 2 * Real.log a + ((d : ℝ) - 1) / 2 * Real.log b ≤ -t ^ 2 / (2 * (d : ℝ))
  -- Multiply both sides by 2
  have h_ineq : ((d : ℝ) + 1) * Real.log a + ((d : ℝ) - 1) * Real.log b ≤ -t ^ 2 / (d : ℝ) := by
    have h := h_sc_vol_h
    calc
      ((d : ℝ) + 1) * Real.log a + ((d : ℝ) - 1) * Real.log b
          = 2 * (((d : ℝ) + 1) / 2 * Real.log a + ((d : ℝ) - 1) / 2 * Real.log b) := by ring
      _ ≤ 2 * (-t ^ 2 / (2 * (d : ℝ))) := mul_le_mul_of_nonneg_left h (by norm_num)
      _ = -t ^ 2 / (d : ℝ) := by ring
  -- Therefore log(σ^d * (1-τ)) ≤ -t^2 / d
  have h_log_le : Real.log (σ ^ d * (1 - τ)) ≤ -t ^ 2 / (d : ℝ) := by
    linarith
  -- Now use the sqrt-exp relationship: sqrt(x) = exp(log(x)/2) for x > 0
  have h_sqrt_eq : Real.sqrt (σ ^ d * (1 - τ)) = Real.exp (Real.log (σ ^ d * (1 - τ)) / 2) := by
    rw [Real.sqrt_eq_rpow (σ ^ d * (1 - τ))]
    rw [Real.rpow_def_of_pos h_prod_pos]
    ring_nf
  rw [h_sqrt_eq]
  -- Apply exp to both sides of the log inequality
  have h_exp_le : Real.exp (Real.log (σ ^ d * (1 - τ)) / 2) ≤ Real.exp ((-t ^ 2 / (d : ℝ)) / 2) := by
    apply Real.exp_le_exp.mpr
    have hpos : (0 : ℝ) ≤ 1/2 := by norm_num
    calc
      Real.log (σ ^ d * (1 - τ)) / 2 = Real.log (σ ^ d * (1 - τ)) * (1/2) := by ring
      _ ≤ (-t ^ 2 / (d : ℝ)) * (1/2) := mul_le_mul_of_nonneg_right h_log_le hpos
      _ = (-t ^ 2 / (d : ℝ)) / 2 := by ring
  -- Simplify the RHS
  have h_rhs_simp : Real.exp ((-t ^ 2 / (d : ℝ)) / 2) = Real.exp (-(1 - (d : ℝ) * β) ^ 2 / (2 * (d : ℝ))) := by
    rw [ht_def]
    ring_nf
  rw [h_rhs_simp] at h_exp_le
  -- The goal has (2 * d) where d : ℕ is coerced to ℝ; h_exp_le has (2 * (d : ℝ))
  simpa [ht_def, mul_comm, mul_left_comm, mul_assoc] using h_exp_le

end AdversarialBco.Bit.Aux_sc_volume

