/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import Mathlib
public import AdversarialBco.Bit.ShallowCut

@[expose] public section

/-!
# Lemmas of Procedure ELL-R, the rounded ellipsoid of BL's projection calls

An ellipsoid is `E(A, a) = {x : (x - a) ⬝ᵥ (A⁻¹ *ᵥ (x - a)) ≤ 1}` with `A` positive definite, a ball
`B̄(z, ρ) = {x : (x - z) ⬝ᵥ (x - z) ≤ ρ²}`; quadratic forms are written `v ⬝ᵥ (A *ᵥ v)`.

* Lemma CC: `pb_cc_loewner`, the two Loewner bounds of the central-cut update
  `σ (1 - τ) A ⪯ σ (A - τ (Aa)(Aa)ᵀ/(aᵀAa)) ⪯ σ A`; `pb_cc_det_bound`, the determinant factor
  `(d²/(d² - 1))^d (1 - 2/(d + 1)) = (d²/(d² - 1))^{d-1} (d/(d + 1))² ≤ e^{-1/(d+1)}`; `pb_det_le_of_loewner`,
  `B ⪯ A` gives `det B ≤ det A`; `pb_cc_incl`, the half ellipsoid cut through the centre lies in the updated
  ellipsoid (`sc_incl` at depth 0); `pb_cc_posDef`, the updated matrix stays positive definite.
* Lemma BALL: `pb_ball_sym`, a ball `B̄(z, ρ)` inside `E(A, a)` gives `B̄(a, ρ)` inside it; `pb_ball_quad`,
  then `ρ² |v|² ≤ vᵀAv`; `pb_ball_det`, then `det A ≥ ρ^{2d}`.
* Lemma ABS: `pb_abs_posDef` (i); `pb_support_le`, `pb_support_witness` (the support function of an
  ellipsoid) and `pb_abs_sqrt` lead to `pb_abs_incl` (ii); `pb_abs_det` (iii).
* Lemma SQ: `pb_sq_isqrt` (the integer square root of `⌊Y²⌋`), `pb_sq_b_norm` (`|Ac|² ≤ Λ cᵀAc`),
  `pb_sq_main` (`t ≥ 1` and `|b̃ - b| ≤ 4 Λ^{1/2}/(ρ 2^q)`).
* Lemma CAP and the count of the projection theorem: `pb_cap_gamma`, `pb_cap_d2`, `pb_cap_count`, `pb_cap_general`
  (`γ^k ≤ 2^{6λ+2}` for `k ≤ 2d(d + 1)λ + 1`), `pb_cap_lam` (the two bounds on `lam - 1`), `pb_ell_count` and
  `pb_ell_det_contra` (the volume count that ends the iteration).

Each lemma sits in a namespace
`AdversarialBco.Bit.Aux_<name>` with its helpers, the lemma itself at `AdversarialBco.Bit.<name>`.
-/
open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius

namespace AdversarialBco.Bit.Aux_pb_abs_posDef


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius

theorem _root_.AdversarialBco.Bit.pb_abs_posDef {n : ℕ} (Ms Mt : Matrix (Fin n) (Fin n) ℝ) (hMt : Mtᵀ = Mt) (lam ρ DA : ℝ)
    (hball : ∀ v : Fin n → ℝ, ρ ^ 2 * (v ⬝ᵥ v) ≤ v ⬝ᵥ (Ms *ᵥ v))
    (hD : ∀ v : Fin n → ℝ, |v ⬝ᵥ ((Mt - lam ^ 2 • Ms) *ᵥ v)| ≤ DA * (v ⬝ᵥ v)) (hDA : DA < lam ^ 2 * ρ ^ 2) :
    Mt.PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨?_, ?_⟩
  · rw [Matrix.isHermitian_iff_isSymm]
    exact hMt
  · intro x hx
    have hpos_dot : 0 < x ⬝ᵥ x := by
      have h_nonneg : 0 ≤ x ⬝ᵥ x := by
        rw [dotProduct]
        refine Finset.sum_nonneg (fun i _ => ?_)
        nlinarith [sq_nonneg (x i)]
      have h_ne_zero : x ⬝ᵥ x ≠ 0 :=
        mt (dotProduct_self_eq_zero.mp ·) hx
      exact lt_of_le_of_ne h_nonneg (Ne.symm h_ne_zero)
    have h_decomp : x ⬝ᵥ (Mt *ᵥ x) = lam ^ 2 * (x ⬝ᵥ (Ms *ᵥ x)) + x ⬝ᵥ ((Mt - lam ^ 2 • Ms) *ᵥ x) := by
      calc
        x ⬝ᵥ (Mt *ᵥ x) = x ⬝ᵥ (((lam ^ 2 • Ms) + (Mt - lam ^ 2 • Ms)) *ᵥ x) := by
          rw [add_comm, sub_add_cancel]
        _ = x ⬝ᵥ ((lam ^ 2 • Ms) *ᵥ x + (Mt - lam ^ 2 • Ms) *ᵥ x) := by
          rw [add_mulVec]
        _ = x ⬝ᵥ ((lam ^ 2 • Ms) *ᵥ x) + x ⬝ᵥ ((Mt - lam ^ 2 • Ms) *ᵥ x) := by
          rw [dotProduct_add]
        _ = x ⬝ᵥ (lam ^ 2 • (Ms *ᵥ x)) + x ⬝ᵥ ((Mt - lam ^ 2 • Ms) *ᵥ x) := by
          rw [smul_mulVec]
        _ = (lam ^ 2 • (x ⬝ᵥ (Ms *ᵥ x))) + x ⬝ᵥ ((Mt - lam ^ 2 • Ms) *ᵥ x) := by
          rw [dotProduct_smul]
        _ = lam ^ 2 * (x ⬝ᵥ (Ms *ᵥ x)) + x ⬝ᵥ ((Mt - lam ^ 2 • Ms) *ᵥ x) := by
          rw [smul_eq_mul]
    have h_target : 0 < x ⬝ᵥ (Mt *ᵥ x) := by
      rw [h_decomp]
      have h_lower : lam ^ 2 * ρ ^ 2 * (x ⬝ᵥ x) - DA * (x ⬝ᵥ x) ≤
          lam ^ 2 * (x ⬝ᵥ (Ms *ᵥ x)) + x ⬝ᵥ ((Mt - lam ^ 2 • Ms) *ᵥ x) := by
        have h1 : lam ^ 2 * ρ ^ 2 * (x ⬝ᵥ x) ≤ lam ^ 2 * (x ⬝ᵥ (Ms *ᵥ x)) := by
          nlinarith [hball x]
        have h2 : -DA * (x ⬝ᵥ x) ≤ x ⬝ᵥ ((Mt - lam ^ 2 • Ms) *ᵥ x) := by
          have habs := hD x
          have h_abs := abs_le.mp habs
          nlinarith
        nlinarith
      have h_pos : 0 < lam ^ 2 * ρ ^ 2 * (x ⬝ᵥ x) - DA * (x ⬝ᵥ x) := by
        nlinarith
      nlinarith
    simpa [TrivialStar.star_trivial] using h_target

end AdversarialBco.Bit.Aux_pb_abs_posDef

namespace AdversarialBco.Bit.Aux_pb_abs_sqrt


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius

theorem _root_.AdversarialBco.Bit.pb_abs_sqrt (a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (hba : b ≤ a ^ 2) :
    a - b / a ≤ Real.sqrt (a ^ 2 - b) := by
  set s := Real.sqrt (a ^ 2 - b) with hs
  have hs_nonneg : 0 ≤ s := Real.sqrt_nonneg _
  have h_nonneg_sq : 0 ≤ a ^ 2 - b := by linarith
  have hs_sq : s ^ 2 = a ^ 2 - b := Real.sq_sqrt h_nonneg_sq
  have h_mul : a * (a - b / a) ≤ a * s := by
    have h_left : a * (a - b / a) = a ^ 2 - b := by
      field_simp [ha.ne.symm]
    rw [h_left, ← hs_sq]
    have h_s_le_a : s ≤ a := by
      calc
        s = Real.sqrt (a ^ 2 - b) := rfl
        _ ≤ Real.sqrt (a ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
        _ = a := Real.sqrt_sq (by linarith)
    nlinarith
  exact le_of_mul_le_mul_left h_mul ha

end AdversarialBco.Bit.Aux_pb_abs_sqrt

namespace AdversarialBco.Bit.Aux_pb_support_witness


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius

theorem _root_.AdversarialBco.Bit.pb_support_witness {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) (a x : Fin n → ℝ)
    (hx : 1 < (x - a) ⬝ᵥ (A⁻¹ *ᵥ (x - a))) :
    ∃ v : Fin n → ℝ, v ⬝ᵥ a + Real.sqrt (v ⬝ᵥ (A *ᵥ v)) < v ⬝ᵥ x := by
  set y := x - a with hy
  set v := A⁻¹ *ᵥ y with hv
  have hκ : 1 < y ⬝ᵥ v := hx
  have hdet : IsUnit A.det :=
    IsUnit.mk0 _ hA.det_pos.ne'
  have h_mul_inv : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A hdet
  have h_inv_mul : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A hdet
  have h_mulVec : A *ᵥ v = y := by
    rw [hv, Matrix.mulVec_mulVec, h_mul_inv, Matrix.one_mulVec]
  have h_dot1 : v ⬝ᵥ (A *ᵥ v) = y ⬝ᵥ v := by
    rw [h_mulVec, dotProduct_comm]
  have h_dot2 : v ⬝ᵥ x - v ⬝ᵥ a = y ⬝ᵥ v := by
    rw [← dotProduct_sub, hy, hv, dotProduct_comm]
  have h_sqrt : Real.sqrt (v ⬝ᵥ (A *ᵥ v)) < y ⬝ᵥ v := by
    rw [h_dot1]
    exact (Real.sqrt_lt_self_iff.mpr hκ)
  refine ⟨v, ?_⟩
  linarith

end AdversarialBco.Bit.Aux_pb_support_witness

namespace AdversarialBco.Bit.Aux_pb_support_le


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius

theorem _root_.AdversarialBco.Bit.pb_support_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) (a x v : Fin n → ℝ)
    (hx : (x - a) ⬝ᵥ (A⁻¹ *ᵥ (x - a)) ≤ 1) : v ⬝ᵥ x ≤ v ⬝ᵥ a + Real.sqrt (v ⬝ᵥ (A *ᵥ v)) := by
  have h_dot_sub : v ⬝ᵥ (x - a) = v ⬝ᵥ x - v ⬝ᵥ a := by
    rw [dotProduct_sub]
  have h_nonneg : 0 ≤ v ⬝ᵥ (A *ᵥ v) := by
    have h := hA.posSemidef.dotProduct_mulVec_nonneg v
    simpa using h
  have h_cs := sc_incl_cs A hA v (x - a)
  -- h_cs : (v ⬝ᵥ (x - a)) ^ 2 ≤ (v ⬝ᵥ (A *ᵥ v)) * ((x - a) ⬝ᵥ (A⁻¹ *ᵥ (x - a)))
  have h_mul : (v ⬝ᵥ (A *ᵥ v)) * ((x - a) ⬝ᵥ (A⁻¹ *ᵥ (x - a))) ≤ v ⬝ᵥ (A *ᵥ v) := by
    nlinarith
  have h_sq : (v ⬝ᵥ (x - a)) ^ 2 ≤ v ⬝ᵥ (A *ᵥ v) := by
    nlinarith
  have h_abs : v ⬝ᵥ (x - a) ≤ |v ⬝ᵥ (x - a)| := le_abs_self _
  have h_sqrt : |v ⬝ᵥ (x - a)| ≤ Real.sqrt (v ⬝ᵥ (A *ᵥ v)) :=
    Real.abs_le_sqrt h_sq
  have h_le : v ⬝ᵥ (x - a) ≤ Real.sqrt (v ⬝ᵥ (A *ᵥ v)) := by
    linarith
  linarith

end AdversarialBco.Bit.Aux_pb_support_le

namespace AdversarialBco.Bit.Aux_pb_abs_incl


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius

theorem _root_.AdversarialBco.Bit.pb_abs_incl {n : ℕ} (Ms Mt : Matrix (Fin n) (Fin n) ℝ) (hMs : Ms.PosDef) (hMt : Mt.PosDef)
    (cs ct : Fin n → ℝ) (lam ρ DA Dc : ℝ) (hlam : 1 ≤ lam) (hρ : 0 < ρ)
    (hball : ∀ v : Fin n → ℝ, ρ ^ 2 * (v ⬝ᵥ v) ≤ v ⬝ᵥ (Ms *ᵥ v))
    (hD : ∀ v : Fin n → ℝ, |v ⬝ᵥ ((Mt - lam ^ 2 • Ms) *ᵥ v)| ≤ DA * (v ⬝ᵥ v)) (hDA0 : 0 ≤ DA)
    (hDA : DA < lam ^ 2 * ρ ^ 2) (hc : (ct - cs) ⬝ᵥ (ct - cs) ≤ Dc ^ 2) (hDc : 0 ≤ Dc)
    (hsum : Dc + DA / (lam * ρ) ≤ (lam - 1) * ρ) (x : Fin n → ℝ) (hx : (x - cs) ⬝ᵥ (Ms⁻¹ *ᵥ (x - cs)) ≤ 1) :
    (x - ct) ⬝ᵥ (Mt⁻¹ *ᵥ (x - ct)) ≤ 1 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨v, hv⟩ := AdversarialBco.Bit.pb_support_witness Mt hMt ct x hcon
  have hle := AdversarialBco.Bit.pb_support_le Ms hMs cs x v hx
  have hq0 : 0 ≤ v ⬝ᵥ v := Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)
  rcases eq_or_lt_of_le hq0 with hq00 | hqpos
  · have hv0 : v = 0 := dotProduct_self_eq_zero.mp hq00.symm
    subst hv0
    simp at hv
  have hMs0 : 0 ≤ v ⬝ᵥ (Ms *ᵥ v) := le_trans (mul_nonneg (sq_nonneg ρ) hq0) (hball v)
  have hs2 : Real.sqrt (v ⬝ᵥ (Ms *ᵥ v)) ^ 2 = v ⬝ᵥ (Ms *ᵥ v) := Real.sq_sqrt hMs0
  have hsρ : ρ * Real.sqrt (v ⬝ᵥ v) ≤ Real.sqrt (v ⬝ᵥ (Ms *ᵥ v)) := by
    rw [← Real.sqrt_sq hρ.le, ← Real.sqrt_mul (sq_nonneg _)]
    exact Real.sqrt_le_sqrt (hball v)
  -- Cauchy and Schwarz for the centre shift
  have hcs : |v ⬝ᵥ (ct - cs)| ≤ Real.sqrt (v ⬝ᵥ v) * Dc := by
    have h1 : (v ⬝ᵥ (ct - cs)) ^ 2 ≤ (v ⬝ᵥ v) * ((ct - cs) ⬝ᵥ (ct - cs)) := by
      have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ v (ct - cs)
      simpa only [dotProduct, sq] using this
    have h2 : (v ⬝ᵥ (ct - cs)) ^ 2 ≤ (Real.sqrt (v ⬝ᵥ v) * Dc) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hq0]
      exact le_trans h1 (mul_le_mul_of_nonneg_left hc hq0)
    calc |v ⬝ᵥ (ct - cs)| = Real.sqrt ((v ⬝ᵥ (ct - cs)) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt ((Real.sqrt (v ⬝ᵥ v) * Dc) ^ 2) := Real.sqrt_le_sqrt h2
      _ = Real.sqrt (v ⬝ᵥ v) * Dc := Real.sqrt_sq (by positivity)
  -- the quadratic form of Mt from below
  have hMt_low : lam ^ 2 * Real.sqrt (v ⬝ᵥ (Ms *ᵥ v)) ^ 2 - DA * (v ⬝ᵥ v) ≤ v ⬝ᵥ (Mt *ᵥ v) := by
    have h := (abs_le.mp (hD v)).1
    rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul] at h
    rw [hs2]; linarith
  have hsqpos : 0 < Real.sqrt (v ⬝ᵥ v) := Real.sqrt_pos.mpr hqpos
  have hspos : 0 < Real.sqrt (v ⬝ᵥ (Ms *ᵥ v)) := lt_of_lt_of_le (mul_pos hρ hsqpos) hsρ
  have hlam0 : 0 < lam := by linarith
  have ha : 0 < lam * Real.sqrt (v ⬝ᵥ (Ms *ᵥ v)) := mul_pos hlam0 hspos
  have hb0 : 0 ≤ DA * (v ⬝ᵥ v) := mul_nonneg hDA0 hq0
  have hba : DA * (v ⬝ᵥ v) ≤ (lam * Real.sqrt (v ⬝ᵥ (Ms *ᵥ v))) ^ 2 := by
    have h1 : DA * (v ⬝ᵥ v) ≤ lam ^ 2 * ρ ^ 2 * (v ⬝ᵥ v) := mul_le_mul_of_nonneg_right hDA.le hq0
    have h2 : ρ ^ 2 * (v ⬝ᵥ v) ≤ Real.sqrt (v ⬝ᵥ (Ms *ᵥ v)) ^ 2 := by rw [hs2]; exact hball v
    have h3 : lam ^ 2 * (ρ ^ 2 * (v ⬝ᵥ v)) ≤ lam ^ 2 * Real.sqrt (v ⬝ᵥ (Ms *ᵥ v)) ^ 2 :=
      mul_le_mul_of_nonneg_left h2 (sq_nonneg lam)
    rw [mul_pow]; linarith
  have hsq := AdversarialBco.Bit.pb_abs_sqrt (lam * Real.sqrt (v ⬝ᵥ (Ms *ᵥ v))) (DA * (v ⬝ᵥ v)) ha hb0 hba
  have hMt_sqrt : lam * Real.sqrt (v ⬝ᵥ (Ms *ᵥ v)) - DA * (v ⬝ᵥ v) / (lam * Real.sqrt (v ⬝ᵥ (Ms *ᵥ v))) ≤
      Real.sqrt (v ⬝ᵥ (Mt *ᵥ v)) := by
    refine le_trans hsq (Real.sqrt_le_sqrt ?_)
    rw [mul_pow]; linarith [hMt_low]
  have hfrac : DA * (v ⬝ᵥ v) / (lam * Real.sqrt (v ⬝ᵥ (Ms *ᵥ v))) ≤ DA / (lam * ρ) * Real.sqrt (v ⬝ᵥ v) := by
    rw [div_le_iff₀ ha]
    have hq' : Real.sqrt (v ⬝ᵥ v) * Real.sqrt (v ⬝ᵥ v) = v ⬝ᵥ v := Real.mul_self_sqrt hq0
    have e : DA / (lam * ρ) * Real.sqrt (v ⬝ᵥ v) * (lam * (ρ * Real.sqrt (v ⬝ᵥ v))) = DA * (v ⬝ᵥ v) := by
      have hlr : lam * ρ ≠ 0 := by positivity
      rw [show DA / (lam * ρ) * Real.sqrt (v ⬝ᵥ v) * (lam * (ρ * Real.sqrt (v ⬝ᵥ v))) =
          DA * (Real.sqrt (v ⬝ᵥ v) * Real.sqrt (v ⬝ᵥ v)) * ((lam * ρ) / (lam * ρ)) by ring,
        div_self hlr, mul_one, hq']
    calc DA * (v ⬝ᵥ v) = DA / (lam * ρ) * Real.sqrt (v ⬝ᵥ v) * (lam * (ρ * Real.sqrt (v ⬝ᵥ v))) := e.symm
      _ ≤ DA / (lam * ρ) * Real.sqrt (v ⬝ᵥ v) * (lam * Real.sqrt (v ⬝ᵥ (Ms *ᵥ v))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_left hsρ hlam0.le
  have hl1 : (lam - 1) * (ρ * Real.sqrt (v ⬝ᵥ v)) ≤ (lam - 1) * Real.sqrt (v ⬝ᵥ (Ms *ᵥ v)) :=
    mul_le_mul_of_nonneg_left hsρ (by linarith)
  have hdot : v ⬝ᵥ ct = v ⬝ᵥ cs + v ⬝ᵥ (ct - cs) := by rw [dotProduct_sub]; ring
  have hcs' := (abs_le.mp hcs).1
  have hmargin : 0 ≤ Real.sqrt (v ⬝ᵥ v) * ((lam - 1) * ρ - Dc - DA / (lam * ρ)) :=
    mul_nonneg hsqpos.le (by linarith)
  have key : v ⬝ᵥ cs + Real.sqrt (v ⬝ᵥ (Ms *ᵥ v)) ≤ v ⬝ᵥ ct + Real.sqrt (v ⬝ᵥ (Mt *ᵥ v)) := by
    nlinarith [hdot, hcs', hMt_sqrt, hfrac, hl1, hmargin]
  linarith

end AdversarialBco.Bit.Aux_pb_abs_incl

namespace AdversarialBco.Bit.Aux_pb_cc_loewner


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius

theorem _root_.AdversarialBco.Bit.pb_cc_loewner {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) (a : Fin n → ℝ)
    (ha : a ≠ 0) (σ τ : ℝ) (hσ : 0 ≤ σ) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) (v : Fin n → ℝ) :
    σ * (1 - τ) * (v ⬝ᵥ (A *ᵥ v)) ≤
        v ⬝ᵥ ((σ • (A - (τ / (a ⬝ᵥ (A *ᵥ a))) • vecMulVec (A *ᵥ a) (A *ᵥ a))) *ᵥ v) ∧
      v ⬝ᵥ ((σ • (A - (τ / (a ⬝ᵥ (A *ᵥ a))) • vecMulVec (A *ᵥ a) (A *ᵥ a))) *ᵥ v) ≤ σ * (v ⬝ᵥ (A *ᵥ v)) := by
  set q := a ⬝ᵥ (A *ᵥ a) with hq_def
  set u := A *ᵥ a with hu_def
  have hq_pos : 0 < q := by
    have h := hA.dotProduct_mulVec_pos ha
    simpa [RCLike.conj_to_real] using h
  have hA_det_unit : IsUnit A.det := by
    rcases (Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit with h
    exact h
  have hu_dot : u ⬝ᵥ (A⁻¹ *ᵥ u) = q := by
    calc
      u ⬝ᵥ (A⁻¹ *ᵥ u) = (A *ᵥ a) ⬝ᵥ (A⁻¹ *ᵥ (A *ᵥ a)) := rfl
      _ = (A *ᵥ a) ⬝ᵥ ((A⁻¹ * A) *ᵥ a) := by rw [Matrix.mulVec_mulVec]
      _ = (A *ᵥ a) ⬝ᵥ (1 *ᵥ a) := by rw [Matrix.nonsing_inv_mul A hA_det_unit]
      _ = (A *ᵥ a) ⬝ᵥ a := by rw [Matrix.one_mulVec]
      _ = a ⬝ᵥ (A *ᵥ a) := by rw [dotProduct_comm]
      _ = q := by rw [hq_def]
  have h_cauchy : (u ⬝ᵥ v)^2 ≤ (v ⬝ᵥ (A *ᵥ v)) * q := by
    have h := sc_incl_cs A hA v u
    -- h : (v ⬝ᵥ u)^2 ≤ (v ⬝ᵥ (A *ᵥ v)) * (u ⬝ᵥ (A⁻¹ *ᵥ u))
    -- but we need (u ⬝ᵥ v)^2, not (v ⬝ᵥ u)^2
    -- dot product is commutative, so they're equal
    rw [dotProduct_comm v u] at h
    rw [hu_dot] at h
    -- now h : (u ⬝ᵥ v)^2 ≤ (v ⬝ᵥ (A *ᵥ v)) * q
    exact h
  have h_mid_expr : v ⬝ᵥ ((σ • (A - (τ / q) • vecMulVec u u)) *ᵥ v) = σ * (v ⬝ᵥ (A *ᵥ v) - (τ / q) * (u ⬝ᵥ v)^2) := by
    calc
      v ⬝ᵥ ((σ • (A - (τ / q) • vecMulVec u u)) *ᵥ v)
          = ((σ • (A - (τ / q) • vecMulVec u u)) *ᵥ v) ⬝ᵥ v := by rw [dotProduct_comm]
      _ = (σ • ((A - (τ / q) • vecMulVec u u) *ᵥ v)) ⬝ᵥ v := by rw [Matrix.smul_mulVec]
      _ = σ * (((A - (τ / q) • vecMulVec u u) *ᵥ v) ⬝ᵥ v) := by
        rw [smul_dotProduct]
        simp
      _ = σ * ((A *ᵥ v - ((τ / q) • vecMulVec u u) *ᵥ v) ⬝ᵥ v) := by rw [Matrix.sub_mulVec]
      _ = σ * ((A *ᵥ v) ⬝ᵥ v - (((τ / q) • vecMulVec u u) *ᵥ v) ⬝ᵥ v) := by rw [sub_dotProduct]
      _ = σ * ((A *ᵥ v) ⬝ᵥ v - ((τ / q) • (vecMulVec u u *ᵥ v)) ⬝ᵥ v) := by rw [Matrix.smul_mulVec]
      _ = σ * ((A *ᵥ v) ⬝ᵥ v - (τ / q) * ((vecMulVec u u *ᵥ v) ⬝ᵥ v)) := by
        rw [smul_dotProduct]
        simp
      _ = σ * ((A *ᵥ v) ⬝ᵥ v - (τ / q) * (((u ⬝ᵥ v) • u) ⬝ᵥ v)) := by
        rw [Matrix.vecMulVec_mulVec]
        simp
      _ = σ * ((A *ᵥ v) ⬝ᵥ v - (τ / q) * ((u ⬝ᵥ v) * (u ⬝ᵥ v))) := by
        rw [smul_dotProduct]
        simp
      _ = σ * ((A *ᵥ v) ⬝ᵥ v - (τ / q) * (u ⬝ᵥ v)^2) := by ring
      _ = σ * (v ⬝ᵥ (A *ᵥ v) - (τ / q) * (u ⬝ᵥ v)^2) := by rw [dotProduct_comm (A *ᵥ v) v]
  rw [h_mid_expr]
  set M := v ⬝ᵥ (A *ᵥ v) with hM_def
  set N := (u ⬝ᵥ v)^2 with hN_def
  have h_ineq : (τ / q) * N ≤ τ * M := by
    have h : N ≤ M * q := h_cauchy
    calc
      (τ / q) * N ≤ (τ / q) * (M * q) := mul_le_mul_of_nonneg_left h (div_nonneg hτ0 (by linarith))
      _ = τ * M := by field_simp [hq_pos.ne.symm]
  have h_nonneg_sq : 0 ≤ N := by
    rw [hN_def]
    apply pow_two_nonneg
  have h_nonneg_τq : 0 ≤ τ / q := div_nonneg hτ0 (by linarith)
  have h_nonneg_prod : 0 ≤ (τ / q) * N := mul_nonneg h_nonneg_τq h_nonneg_sq
  constructor
  · -- σ*(1-τ)*M ≤ σ*(M - (τ/q)*N)
    have h : σ * ((τ / q) * N) ≤ σ * (τ * M) := mul_le_mul_of_nonneg_left h_ineq hσ
    linarith
  · -- σ*(M - (τ/q)*N) ≤ σ*M
    nlinarith

end AdversarialBco.Bit.Aux_pb_cc_loewner

namespace AdversarialBco.Bit.Aux_pb_cc_det_bound


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius

theorem _root_.AdversarialBco.Bit.pb_cc_det_bound (d : ℕ) (hd : 2 ≤ d) :
    ((d : ℝ) ^ 2 / ((d : ℝ) ^ 2 - 1)) ^ d * (1 - 2 / ((d : ℝ) + 1)) =
        ((d : ℝ) ^ 2 / ((d : ℝ) ^ 2 - 1)) ^ (d - 1) * ((d : ℝ) / ((d : ℝ) + 1)) ^ 2 ∧
      ((d : ℝ) ^ 2 / ((d : ℝ) ^ 2 - 1)) ^ d * (1 - 2 / ((d : ℝ) + 1)) ≤ Real.exp (-1 / ((d : ℝ) + 1)) := by
  have hd' : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hdpos_nat : 0 < d := by omega
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hdpos_nat
  have hdpos' : (0 : ℝ) < (d : ℝ) + 1 := by nlinarith
  have hd1 : 1 ≤ d := by omega
  have h_denom_ne_zero : (d : ℝ) ^ 2 - 1 ≠ 0 := by
    nlinarith
  have h_denom2_ne_zero : (d : ℝ) + 1 ≠ 0 := by nlinarith
  -- Part 1: identity
  have h_eq : ((d : ℝ) ^ 2 / ((d : ℝ) ^ 2 - 1)) ^ d * (1 - 2 / ((d : ℝ) + 1)) =
      ((d : ℝ) ^ 2 / ((d : ℝ) ^ 2 - 1)) ^ (d - 1) * ((d : ℝ) / ((d : ℝ) + 1)) ^ 2 := by
    set s := (d : ℝ) ^ 2 / ((d : ℝ) ^ 2 - 1) with hs
    have h_pow : s ^ d = s ^ (d - 1) * s := by
      calc
        s ^ d = s ^ ((d - 1) + 1) := by rw [Nat.sub_add_cancel hd1]
        _ = s ^ (d - 1) * s := by rw [pow_succ]
    calc
      s ^ d * (1 - 2 / ((d : ℝ) + 1)) = (s ^ (d - 1) * s) * (1 - 2 / ((d : ℝ) + 1)) := by rw [h_pow]
      _ = s ^ (d - 1) * (s * (1 - 2 / ((d : ℝ) + 1))) := by ring
      _ = s ^ (d - 1) * ((d : ℝ) / ((d : ℝ) + 1)) ^ 2 := by
        dsimp [s]
        field_simp [h_denom_ne_zero, h_denom2_ne_zero]
        ring
  -- Part 2: inequality
  have h_ineq : ((d : ℝ) ^ 2 / ((d : ℝ) ^ 2 - 1)) ^ d * (1 - 2 / ((d : ℝ) + 1)) ≤ Real.exp (-1 / ((d : ℝ) + 1)) := by
    set σ := (d : ℝ) ^ 2 / ((d : ℝ) ^ 2 - 1) with hσ_def
    set τ := 2 / ((d : ℝ) + 1) with hτ_def
    have hσ_eq : σ = (d : ℝ) ^ 2 * (1 - (0 : ℝ) ^ 2) / ((d : ℝ) ^ 2 - 1) := by
      dsimp [σ]
      ring
    have hτ_eq : τ = 2 * (1 - (d : ℝ) * (0 : ℝ)) / (((d : ℝ) + 1) * (1 - (0 : ℝ))) := by
      dsimp [τ]
      field_simp [h_denom2_ne_zero]
      ring
    have hβ0 : (0 : ℝ) ≤ 0 := le_refl _
    have hβd : (d : ℝ) * (0 : ℝ) < 1 := by nlinarith
    have h_sc := sc_volume d 0 σ τ hd hβ0 hβd hσ_eq hτ_eq
    have h_sc_simp : Real.sqrt (σ ^ d * (1 - τ)) ≤ Real.exp (-1 / (2 * (d : ℝ))) := by
      simpa [hσ_def, hτ_def] using h_sc
    have h_nonneg : 0 ≤ σ ^ d * (1 - τ) := by
      have hσ_nonneg : 0 ≤ σ := by
        dsimp [σ]
        refine div_nonneg (pow_two_nonneg _) ?_
        nlinarith
      have hτ_le_one : τ ≤ 1 := by
        dsimp [τ]
        refine (div_le_one ?_).mpr ?_
        · nlinarith
        · nlinarith
      have h_pow_nonneg : 0 ≤ σ ^ d := pow_nonneg hσ_nonneg _
      have h_one_minus_τ_nonneg : 0 ≤ 1 - τ := by nlinarith
      exact mul_nonneg h_pow_nonneg h_one_minus_τ_nonneg
    have h_sq_ineq : σ ^ d * (1 - τ) ≤ Real.exp (-1 / (d : ℝ)) := by
      have h_sqrt_sq : (Real.sqrt (σ ^ d * (1 - τ))) ^ 2 = σ ^ d * (1 - τ) := Real.sq_sqrt h_nonneg
      have h_sq : (Real.sqrt (σ ^ d * (1 - τ))) ^ 2 ≤ (Real.exp (-1 / (2 * (d : ℝ)))) ^ 2 := by
        have hA : 0 ≤ Real.sqrt (σ ^ d * (1 - τ)) := Real.sqrt_nonneg _
        have hB : 0 ≤ Real.exp (-1 / (2 * (d : ℝ))) := (Real.exp_pos _).le
        rw [sq_le_sq, abs_of_nonneg hA, abs_of_nonneg hB]
        exact h_sc_simp
      have h_right : (Real.exp (-1 / (2 * (d : ℝ)))) ^ 2 = Real.exp (-1 / (d : ℝ)) := by
        calc
          (Real.exp (-1 / (2 * (d : ℝ)))) ^ 2 = Real.exp ((2 : ℝ) * (-1 / (2 * (d : ℝ)))) := by
            simpa using (Real.exp_nat_mul (-1 / (2 * (d : ℝ))) 2).symm
          _ = Real.exp (-1 / (d : ℝ)) := by
            field_simp [hdpos.ne.symm]
      nlinarith
    have h_exp_le : Real.exp (-1 / (d : ℝ)) ≤ Real.exp (-1 / ((d : ℝ) + 1)) := by
      apply Real.exp_le_exp.mpr
      have h_one_div : 1 / ((d : ℝ) + 1) ≤ 1 / (d : ℝ) := by
        refine (one_div_le_one_div hdpos' hdpos).mpr ?_
        nlinarith
      simpa [neg_div] using neg_le_neg h_one_div
    calc
      ((d : ℝ) ^ 2 / ((d : ℝ) ^ 2 - 1)) ^ d * (1 - 2 / ((d : ℝ) + 1)) = σ ^ d * (1 - τ) := by
        simp [σ, τ]
      _ ≤ Real.exp (-1 / (d : ℝ)) := h_sq_ineq
      _ ≤ Real.exp (-1 / ((d : ℝ) + 1)) := h_exp_le
  exact And.intro h_eq h_ineq

end AdversarialBco.Bit.Aux_pb_cc_det_bound

namespace AdversarialBco.Bit.Aux_pb_det_le_of_loewner


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius
open scoped MatrixOrder

theorem _root_.AdversarialBco.Bit.pb_det_le_of_loewner {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (hB : B.PosDef) (h : ∀ v : Fin n → ℝ, v ⬝ᵥ (B *ᵥ v) ≤ v ⬝ᵥ (A *ᵥ v)) : B.det ≤ A.det := by
  -- Step 1: A - B is positive semidefinite
  have h_psd : (A - B).PosSemidef := by
    rw [posSemidef_iff_dotProduct_mulVec]
    refine ⟨hA.isHermitian.sub hB.isHermitian, ?_⟩
    intro x
    rw [sub_mulVec, dotProduct_sub]
    have hx := h x
    simpa [star] using sub_nonneg.mpr hx
  -- Step 2: Let S = sqrt(A)
  set S := CFC.sqrt A with hS_def
  have hS_nonneg : 0 ≤ A := hA.posSemidef.nonneg
  have hS_sq : S * S = A := by
    rw [hS_def]
    have h := CFC.sq_sqrt A hS_nonneg
    rw [sq] at h
    exact h
  -- S is positive semidefinite
  have hS_psd : S.PosSemidef := by
    rw [hS_def]
    exact nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)
  -- S is Hermitian
  have hS_herm : S.IsHermitian := hS_psd.isHermitian
  -- S is invertible: since det(S)^2 = det(A) > 0, det(S) ≠ 0
  have hS_det_ne_zero : S.det ≠ 0 := by
    have h_det_pos : 0 < A.det := hA.det_pos
    have h_eq : S.det ^ 2 = A.det := by
      calc
        S.det ^ 2 = S.det * S.det := by ring
        _ = (S * S).det := by rw [Matrix.det_mul]
        _ = A.det := by rw [hS_sq]
    intro hzero
    rw [hzero] at h_eq
    simp at h_eq
    linarith
  have hS_det_unit : IsUnit S.det := (isUnit_iff_ne_zero (a := S.det)).mpr hS_det_ne_zero
  have hS_mul_inv : S * S⁻¹ = 1 := by rw [Matrix.mul_nonsing_inv S hS_det_unit]
  have hS_inv_mul : S⁻¹ * S = 1 := by rw [Matrix.nonsing_inv_mul S hS_det_unit]
  -- S⁻¹ is also Hermitian
  have hS_inv_herm : S⁻¹.IsHermitian := hS_herm.inv
  -- Step 3: Let X = S⁻¹ * B * S⁻¹
  set X := S⁻¹ * B * S⁻¹ with hX_def
  -- X is positive semidefinite
  have hX_psd : X.PosSemidef := by
    rw [hX_def]
    have h := hB.posSemidef.conjTranspose_mul_mul_same S⁻¹
    rw [hS_inv_herm.eq] at h
    exact h
  -- Step 4: I - X is positive semidefinite
  have h_one_sub_X_psd : (1 - X).PosSemidef := by
    rw [hX_def]
    have h_temp : S⁻¹ * A * S⁻¹ = 1 := by
      calc
        S⁻¹ * A * S⁻¹ = S⁻¹ * (S * S) * S⁻¹ := by rw [hS_sq]
        _ = (S⁻¹ * (S * S)) * S⁻¹ := by rw [Matrix.mul_assoc]
        _ = ((S⁻¹ * S) * S) * S⁻¹ := by rw [← Matrix.mul_assoc]
        _ = (1 * S) * S⁻¹ := by rw [hS_inv_mul]
        _ = S * S⁻¹ := by simp
        _ = 1 := by rw [hS_mul_inv]
    have h_eq : 1 - S⁻¹ * B * S⁻¹ = S⁻¹ * (A - B) * S⁻¹ := by
      calc
        1 - S⁻¹ * B * S⁻¹ = (S⁻¹ * A * S⁻¹) - S⁻¹ * B * S⁻¹ := by rw [h_temp]
        _ = S⁻¹ * A * S⁻¹ - S⁻¹ * B * S⁻¹ := rfl
        _ = S⁻¹ * (A - B) * S⁻¹ := by
          rw [← sub_mul, ← mul_sub]
    rw [h_eq]
    have h := h_psd.conjTranspose_mul_mul_same S⁻¹
    rw [hS_inv_herm.eq] at h
    exact h
  -- X is Hermitian
  have hX_herm : X.IsHermitian := hX_psd.isHermitian
  -- Step 5: Eigenvalues of X are between 0 and 1
  have h_eigen_nonneg : ∀ i, 0 ≤ hX_herm.eigenvalues i := by
    intro i
    exact hX_psd.eigenvalues_nonneg i
  have h_eigen_le_one : ∀ i, hX_herm.eigenvalues i ≤ 1 := by
    intro i
    -- For each eigenvector v_i, we have X v_i = λ_i v_i and (1 - X) v_i = (1 - λ_i) v_i
    -- Since 1 - X is positive semidefinite, 0 ≤ v_i^T (1 - X) v_i = 1 - λ_i, so λ_i ≤ 1
    let v_i := hX_herm.eigenvectorBasis i
    have h_mulVec : X *ᵥ (v_i : Fin n → ℝ) = (hX_herm.eigenvalues i : ℝ) • (v_i : Fin n → ℝ) := by
      simpa using hX_herm.mulVec_eigenvectorBasis i
    have h_mulVec_sub : (1 - X) *ᵥ (v_i : Fin n → ℝ) = ((1 : ℝ) - (hX_herm.eigenvalues i : ℝ)) • (v_i : Fin n → ℝ) := by
      calc
        (1 - X) *ᵥ (v_i : Fin n → ℝ) = 1 *ᵥ (v_i : Fin n → ℝ) - X *ᵥ (v_i : Fin n → ℝ) := by rw [sub_mulVec]
        _ = (v_i : Fin n → ℝ) - (hX_herm.eigenvalues i : ℝ) • (v_i : Fin n → ℝ) := by simp [h_mulVec]
        _ = ((1 : ℝ) - (hX_herm.eigenvalues i : ℝ)) • (v_i : Fin n → ℝ) := by simp [sub_smul]
    have h_nonneg : 0 ≤ star (v_i : Fin n → ℝ) ⬝ᵥ ((1 - X) *ᵥ (v_i : Fin n → ℝ)) :=
      h_one_sub_X_psd.dotProduct_mulVec_nonneg (v_i : Fin n → ℝ)
    have h_dot : star (v_i : Fin n → ℝ) ⬝ᵥ ((1 - X) *ᵥ (v_i : Fin n → ℝ)) = (1 - hX_herm.eigenvalues i : ℝ) * ((v_i : Fin n → ℝ) ⬝ᵥ (v_i : Fin n → ℝ)) := by
      rw [h_mulVec_sub]
      simp [dotProduct_smul, star]
    have h_norm_sq : (v_i : Fin n → ℝ) ⬝ᵥ (v_i : Fin n → ℝ) = 1 := by
      have h_ortho := hX_herm.eigenvectorBasis.orthonormal
      have h_norm : ‖v_i‖ = 1 := h_ortho.1 i
      have h_inner_sq : RCLike.re (inner (𝕜 := ℝ) (v_i : EuclideanSpace ℝ (Fin n)) (v_i : EuclideanSpace ℝ (Fin n))) = ‖v_i‖ ^ 2 :=
        inner_self_eq_norm_sq _
      have h_inner_eq : inner (𝕜 := ℝ) (v_i : EuclideanSpace ℝ (Fin n)) (v_i : EuclideanSpace ℝ (Fin n)) = (v_i : Fin n → ℝ) ⬝ᵥ (v_i : Fin n → ℝ) := by
        rw [EuclideanSpace.inner_eq_star_dotProduct]
        simp [star]
      rw [h_inner_eq] at h_inner_sq
      rw [h_norm] at h_inner_sq
      simp at h_inner_sq
      exact h_inner_sq
    rw [h_dot] at h_nonneg
    rw [h_norm_sq] at h_nonneg
    linarith
  -- Step 6: det(X) = product of eigenvalues
  have h_det_prod : X.det = ∏ i, (hX_herm.eigenvalues i : ℝ) := by
    simpa using hX_herm.det_eq_prod_eigenvalues
  -- Step 7: det(X) ≤ 1
  have h_det_X_le_one : X.det ≤ 1 := by
    rw [h_det_prod]
    -- Since each eigenvalue is in [0, 1], the product is ≤ 1
    -- We prove this by induction on Finset.univ
    have h_prod : (∏ i, (hX_herm.eigenvalues i : ℝ)) = ((Finset.univ : Finset (Fin n)).prod fun i => (hX_herm.eigenvalues i : ℝ)) := by simp
    rw [h_prod]
    have h_nonneg_prod : ∀ (s : Finset (Fin n)), 0 ≤ s.prod (fun i => (hX_herm.eigenvalues i : ℝ)) := by
      intro s
      apply Finset.prod_nonneg
      intro i _
      exact h_eigen_nonneg i
    have h_le_one_prod : ∀ (s : Finset (Fin n)), s.prod (fun i => (hX_herm.eigenvalues i : ℝ)) ≤ 1 := by
      intro s
      induction' s using Finset.induction_on with i s his ih
      · simp
      · rw [Finset.prod_insert his]
        have hi_nonneg := h_eigen_nonneg i
        have hi_le_one := h_eigen_le_one i
        have h_nonneg_s := h_nonneg_prod s
        have h_mul : (hX_herm.eigenvalues i : ℝ) * s.prod (fun i => (hX_herm.eigenvalues i : ℝ)) ≤ 1 * 1 :=
          mul_le_mul hi_le_one ih h_nonneg_s (by norm_num)
        apply h_mul.trans
        simp
    exact h_le_one_prod Finset.univ
  -- Step 8: B = S * X * S
  have hB_eq : B = S * X * S := by
    rw [hX_def]
    calc
      B = 1 * B * 1 := by simp
      _ = (S * S⁻¹) * B * (S⁻¹ * S) := by rw [hS_mul_inv, hS_inv_mul]
      _ = S * (S⁻¹ * B * S⁻¹) * S := by
        simp [Matrix.mul_assoc]
      _ = S * X * S := rfl
  -- Step 9: det(B) = det(S)^2 * det(X) ≤ det(S)^2 = det(A)
  have h_det_B : B.det = (S.det)^2 * X.det := by
    rw [hB_eq]
    simp [Matrix.det_mul, pow_two, mul_comm, mul_assoc]
  have h_det_A : A.det = (S.det)^2 := by
    rw [← hS_sq]
    simp [Matrix.det_mul, pow_two]
  rw [h_det_B, h_det_A]
  have h_det_S_sq_nonneg : 0 ≤ (S.det)^2 := pow_two_nonneg _
  calc
    (S.det)^2 * X.det ≤ (S.det)^2 * 1 := mul_le_mul_of_nonneg_left h_det_X_le_one h_det_S_sq_nonneg
    _ = (S.det)^2 := by simp

end AdversarialBco.Bit.Aux_pb_det_le_of_loewner

namespace AdversarialBco.Bit.Aux_pb_abs_det


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius

theorem _root_.AdversarialBco.Bit.pb_abs_det {n : ℕ} (Ms Mt : Matrix (Fin n) (Fin n) ℝ) (hMs : Ms.PosDef) (hMt : Mt.PosDef)
    (lam ρ DA : ℝ) (hlam : 1 ≤ lam) (hρ : 0 < ρ) (hball : ∀ v : Fin n → ℝ, ρ ^ 2 * (v ⬝ᵥ v) ≤ v ⬝ᵥ (Ms *ᵥ v))
    (hD : ∀ v : Fin n → ℝ, |v ⬝ᵥ ((Mt - lam ^ 2 • Ms) *ᵥ v)| ≤ DA * (v ⬝ᵥ v)) (hDA0 : 0 ≤ DA) :
    Mt.det ≤ (lam ^ 2 + DA / ρ ^ 2) ^ n * Ms.det := by
  have hρ2 : 0 < ρ ^ 2 := by positivity
  have hc : 0 < lam ^ 2 + DA / ρ ^ 2 := by positivity
  have hcM : ((lam ^ 2 + DA / ρ ^ 2) • Ms).PosDef := hMs.smul hc
  have hle : ∀ v : Fin n → ℝ, v ⬝ᵥ (Mt *ᵥ v) ≤ v ⬝ᵥ (((lam ^ 2 + DA / ρ ^ 2) • Ms) *ᵥ v) := by
    intro v
    have h1 := le_trans (le_abs_self _) (hD v)
    rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul] at h1
    rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
    have h2 : v ⬝ᵥ v ≤ v ⬝ᵥ (Ms *ᵥ v) / ρ ^ 2 := by
      rw [le_div_iff₀ hρ2]; linarith [hball v]
    have h3 : DA * (v ⬝ᵥ v) ≤ DA * (v ⬝ᵥ (Ms *ᵥ v) / ρ ^ 2) := mul_le_mul_of_nonneg_left h2 hDA0
    have h4 : DA * (v ⬝ᵥ (Ms *ᵥ v) / ρ ^ 2) = DA / ρ ^ 2 * (v ⬝ᵥ (Ms *ᵥ v)) := by ring
    nlinarith
  have := AdversarialBco.Bit.pb_det_le_of_loewner _ _ hcM hMt hle
  rwa [Matrix.det_smul, Fintype.card_fin] at this

end AdversarialBco.Bit.Aux_pb_abs_det

namespace AdversarialBco.Bit.Aux_pb_ball_sym


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius

theorem _root_.AdversarialBco.Bit.pb_ball_sym {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) (a z : Fin n → ℝ) (ρ : ℝ)
    (h : ∀ x : Fin n → ℝ, (x - z) ⬝ᵥ (x - z) ≤ ρ ^ 2 → (x - a) ⬝ᵥ (A⁻¹ *ᵥ (x - a)) ≤ 1) :
    ∀ x : Fin n → ℝ, (x - a) ⬝ᵥ (x - a) ≤ ρ ^ 2 → (x - a) ⬝ᵥ (A⁻¹ *ᵥ (x - a)) ≤ 1 := by
  intro x hx
  set w := x - a with hw
  set M := A⁻¹ with hM
  have hM_posSemidef : M.PosSemidef := hA.inv.posSemidef
  have hM_nonneg : ∀ v : Fin n → ℝ, 0 ≤ v ⬝ᵥ (M *ᵥ v) := by
    intro v
    simpa using hM_posSemidef.dotProduct_mulVec_nonneg v
  have hpar : ∀ u v : Fin n → ℝ, (u + v) ⬝ᵥ (M *ᵥ (u + v)) + (u - v) ⬝ᵥ (M *ᵥ (u - v)) = 2 * ((u ⬝ᵥ (M *ᵥ u)) + (v ⬝ᵥ (M *ᵥ v))) := by
    intro u v
    calc
      (u + v) ⬝ᵥ (M *ᵥ (u + v)) + (u - v) ⬝ᵥ (M *ᵥ (u - v))
          = (u + v) ⬝ᵥ (M *ᵥ u + M *ᵥ v) + (u - v) ⬝ᵥ (M *ᵥ u - M *ᵥ v) := by
        simp [mulVec_add, mulVec_sub]
      _ = ((u + v) ⬝ᵥ (M *ᵥ u) + (u + v) ⬝ᵥ (M *ᵥ v)) + ((u - v) ⬝ᵥ (M *ᵥ u) - (u - v) ⬝ᵥ (M *ᵥ v)) := by
        simp [dotProduct_add, dotProduct_sub]
      _ = (u ⬝ᵥ (M *ᵥ u) + v ⬝ᵥ (M *ᵥ u) + (u ⬝ᵥ (M *ᵥ v) + v ⬝ᵥ (M *ᵥ v))) + (u ⬝ᵥ (M *ᵥ u) - v ⬝ᵥ (M *ᵥ u) - (u ⬝ᵥ (M *ᵥ v) - v ⬝ᵥ (M *ᵥ v))) := by
        simp [add_assoc]
      _ = 2 * (u ⬝ᵥ (M *ᵥ u)) + 2 * (v ⬝ᵥ (M *ᵥ v)) := by ring
      _ = 2 * ((u ⬝ᵥ (M *ᵥ u)) + (v ⬝ᵥ (M *ᵥ v))) := by ring
  set p := z + w with hp
  set q := z - w with hq
  have hp_sub_z : p - z = w := by
    rw [hp]
    abel
  have hq_sub_z : q - z = -w := by
    rw [hq]
    abel
  have hp_dist : (p - z) ⬝ᵥ (p - z) ≤ ρ ^ 2 := by
    rw [hp_sub_z]
    rw [hw]
    exact hx
  have hq_dist : (q - z) ⬝ᵥ (q - z) ≤ ρ ^ 2 := by
    rw [hq_sub_z]
    have : (-w) ⬝ᵥ (-w) = w ⬝ᵥ w := by simp
    rw [this]
    rw [hw]
    exact hx
  have hp_val : (p - a) ⬝ᵥ (M *ᵥ (p - a)) ≤ 1 := by
    simpa [hM] using h p hp_dist
  have hq_val : (q - a) ⬝ᵥ (M *ᵥ (q - a)) ≤ 1 := by
    simpa [hM] using h q hq_dist
  set u₁ := p - a with hu₁
  set u₂ := a - q with hu₂
  have h_sum : u₁ + u₂ = (2 : ℝ) • w := by
    rw [hu₁, hu₂, hp, hq, hw]
    ext i
    simp
    ring
  have h_diff : u₁ - u₂ = (2 : ℝ) • (z - a) := by
    rw [hu₁, hu₂, hp, hq]
    ext i
    simp
    ring
  have h_par_app := hpar u₁ u₂
  rw [h_sum, h_diff] at h_par_app
  have h_sq_smul : ∀ (v : Fin n → ℝ) (t : ℝ), (t • v) ⬝ᵥ (M *ᵥ (t • v)) = t ^ 2 * (v ⬝ᵥ (M *ᵥ v)) := by
    intro v t
    simp [mulVec_smul, dotProduct_smul]
    ring
  have h_par_simp : 4 * (w ⬝ᵥ (M *ᵥ w)) + 4 * ((z - a) ⬝ᵥ (M *ᵥ (z - a))) = 2 * ((u₁ ⬝ᵥ (M *ᵥ u₁)) + (u₂ ⬝ᵥ (M *ᵥ u₂))) := by
    have h1 : ((2 : ℝ) • w) ⬝ᵥ (M *ᵥ ((2 : ℝ) • w)) = 4 * (w ⬝ᵥ (M *ᵥ w)) := by
      calc
        ((2 : ℝ) • w) ⬝ᵥ (M *ᵥ ((2 : ℝ) • w)) = (2 : ℝ) ^ 2 * (w ⬝ᵥ (M *ᵥ w)) := h_sq_smul w (2 : ℝ)
        _ = 4 * (w ⬝ᵥ (M *ᵥ w)) := by norm_num
    have h2 : ((2 : ℝ) • (z - a)) ⬝ᵥ (M *ᵥ ((2 : ℝ) • (z - a))) = 4 * ((z - a) ⬝ᵥ (M *ᵥ (z - a))) := by
      calc
        ((2 : ℝ) • (z - a)) ⬝ᵥ (M *ᵥ ((2 : ℝ) • (z - a))) = (2 : ℝ) ^ 2 * ((z - a) ⬝ᵥ (M *ᵥ (z - a))) := h_sq_smul (z - a) (2 : ℝ)
        _ = 4 * ((z - a) ⬝ᵥ (M *ᵥ (z - a))) := by norm_num
    calc
      4 * (w ⬝ᵥ (M *ᵥ w)) + 4 * ((z - a) ⬝ᵥ (M *ᵥ (z - a)))
          = (((2 : ℝ) • w) ⬝ᵥ (M *ᵥ ((2 : ℝ) • w))) + (((2 : ℝ) • (z - a)) ⬝ᵥ (M *ᵥ ((2 : ℝ) • (z - a)))) := by rw [h1, h2]
      _ = 2 * ((u₁ ⬝ᵥ (M *ᵥ u₁)) + (u₂ ⬝ᵥ (M *ᵥ u₂))) := by simpa using h_par_app
  have h_nonneg_za : 0 ≤ (z - a) ⬝ᵥ (M *ᵥ (z - a)) := hM_nonneg (z - a)
  have h_ineq : 2 * (w ⬝ᵥ (M *ᵥ w)) ≤ (u₁ ⬝ᵥ (M *ᵥ u₁)) + (u₂ ⬝ᵥ (M *ᵥ u₂)) := by
    linarith
  have hu₂_eq : u₂ ⬝ᵥ (M *ᵥ u₂) = (q - a) ⬝ᵥ (M *ᵥ (q - a)) := by
    rw [hu₂]
    calc
      (a - q) ⬝ᵥ (M *ᵥ (a - q)) = (-(q - a)) ⬝ᵥ (M *ᵥ (-(q - a))) := by abel
      _ = (-(q - a)) ⬝ᵥ (-(M *ᵥ (q - a))) := by rw [mulVec_neg]
      _ = (q - a) ⬝ᵥ (M *ᵥ (q - a)) := by simp
  rw [hu₁, hu₂_eq] at h_ineq
  have h_bound : (u₁ ⬝ᵥ (M *ᵥ u₁)) + (q - a) ⬝ᵥ (M *ᵥ (q - a)) ≤ 2 := by
    linarith
  have h_final : w ⬝ᵥ (M *ᵥ w) ≤ 1 := by
    linarith
  rw [hw, hM]
  exact h_final

end AdversarialBco.Bit.Aux_pb_ball_sym

namespace AdversarialBco.Bit.Aux_pb_ball_quad


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius

theorem _root_.AdversarialBco.Bit.pb_ball_quad {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) (a : Fin n → ℝ) (ρ : ℝ)
    (hρ : 0 < ρ) (h : ∀ x : Fin n → ℝ, (x - a) ⬝ᵥ (x - a) ≤ ρ ^ 2 → (x - a) ⬝ᵥ (A⁻¹ *ᵥ (x - a)) ≤ 1)
    (v : Fin n → ℝ) : ρ ^ 2 * (v ⬝ᵥ v) ≤ v ⬝ᵥ (A *ᵥ v) := by
  -- nonnegativity of v·Av from positive semidefiniteness
  have h_nonneg_Av : 0 ≤ v ⬝ᵥ (A *ᵥ v) := by
    have := hA.posSemidef.dotProduct_mulVec_nonneg v
    simpa using this
  -- nonnegativity of v·v
  have h_nonneg_vv : 0 ≤ v ⬝ᵥ v := by
    have := dotProduct_star_self_nonneg v
    simpa using this
  by_cases hv0 : v = 0
  · subst hv0; simp
  · have hvv_pos : 0 < v ⬝ᵥ v := by
      by_contra hge
      push Not at hge
      have hzero : v ⬝ᵥ v = 0 := by linarith
      exact hv0 (dotProduct_self_eq_zero.mp hzero)
    -- Cauchy-Schwarz: (v·v)^2 ≤ (v·Av)(v·A⁻¹v) via hA.inv
    have h_cs : (v ⬝ᵥ v) ^ 2 ≤ (v ⬝ᵥ (A *ᵥ v)) * (v ⬝ᵥ (A⁻¹ *ᵥ v)) := by
      have hcs := hA.inv.star_dotProduct_mulVec_mul_le v (A *ᵥ v)
      -- Over ℝ, star = id
      have hcs' : (v ⬝ᵥ (A⁻¹ *ᵥ (A *ᵥ v))) * (v ⬝ᵥ (A⁻¹ *ᵥ (A *ᵥ v))) ≤
          (v ⬝ᵥ (A⁻¹ *ᵥ v)) * ((A *ᵥ v) ⬝ᵥ (A⁻¹ *ᵥ (A *ᵥ v))) := by
        simpa using hcs
      -- A⁻¹ * A = 1
      haveI : Invertible A := hA.isUnit.invertible
      have h_inv_mul : A⁻¹ * A = 1 :=
        Matrix.inv_mul_of_invertible A
      -- Simplify A⁻¹ *ᵥ (A *ᵥ v) = (A⁻¹ * A) *ᵥ v = 1 *ᵥ v = v
      have hcs'' : (v ⬝ᵥ v) * (v ⬝ᵥ v) ≤ (v ⬝ᵥ (A⁻¹ *ᵥ v)) * ((A *ᵥ v) ⬝ᵥ v) := by
        simpa [Matrix.mulVec_mulVec, h_inv_mul, Matrix.one_mulVec] using hcs'
      -- Symmetry of dot product: (A *ᵥ v) ⬝ᵥ v = v ⬝ᵥ (A *ᵥ v)
      rw [dotProduct_comm (A *ᵥ v) v] at hcs''
      -- hcs'': (v·v) * (v·v) ≤ (v·(A⁻¹·v)) * (v·(A·v))
      -- Use commutativity to reorder RHS
      rw [mul_comm (v ⬝ᵥ (A⁻¹ *ᵥ v)) (v ⬝ᵥ (A *ᵥ v))] at hcs''
      -- hcs'': (v·v) * (v·v) ≤ (v·(A·v)) * (v·(A⁻¹·v))
      -- Goal: (v·v)^2 ≤ (v·(A·v)) * (v·(A⁻¹·v))
      simpa [sq] using hcs''
    -- from hypothesis h with scaled vector
    have h_inv : ρ ^ 2 * (v ⬝ᵥ (A⁻¹ *ᵥ v)) ≤ v ⬝ᵥ v := by
      set s := Real.sqrt (v ⬝ᵥ v) with hs
      have hs_pos : 0 < s := Real.sqrt_pos.mpr hvv_pos
      have hs_sq : s ^ 2 = v ⬝ᵥ v := Real.sq_sqrt h_nonneg_vv
      set x := a + (ρ / s) • v with hx
      have hx_sub_a : x - a = (ρ / s) • v := by
        simp [hx, add_sub_cancel_left]
      have h_norm_sq : (x - a) ⬝ᵥ (x - a) = ρ ^ 2 := by
        rw [hx_sub_a]
        calc
          ((ρ / s) • v) ⬝ᵥ ((ρ / s) • v) = (ρ / s) * (v ⬝ᵥ ((ρ / s) • v)) := by
            simp [smul_dotProduct]
          _ = (ρ / s) * ((ρ / s) * (v ⬝ᵥ v)) := by simp [dotProduct_smul]
          _ = (ρ ^ 2 / s ^ 2) * (v ⬝ᵥ v) := by ring
          _ = (ρ ^ 2 / (v ⬝ᵥ v)) * (v ⬝ᵥ v) := by rw [hs_sq]
          _ = ρ ^ 2 := by field_simp [hvv_pos.ne']
      have hx_bound : (x - a) ⬝ᵥ (x - a) ≤ ρ ^ 2 := by rw [h_norm_sq]
      have hx_result := h x hx_bound
      -- hx_result : (x - a) ⬝ᵥ (A⁻¹ *ᵥ (x - a)) ≤ 1
      rw [hx_sub_a] at hx_result
      -- ((ρ / s) • v) ⬝ᵥ (A⁻¹ *ᵥ ((ρ / s) • v)) ≤ 1
      have h_simp : ((ρ / s) • v) ⬝ᵥ (A⁻¹ *ᵥ ((ρ / s) • v)) =
          (ρ ^ 2 / (v ⬝ᵥ v)) * (v ⬝ᵥ (A⁻¹ *ᵥ v)) := by
        calc
          ((ρ / s) • v) ⬝ᵥ (A⁻¹ *ᵥ ((ρ / s) • v)) =
              ((ρ / s) • v) ⬝ᵥ ((ρ / s) • (A⁻¹ *ᵥ v)) := by
            simp [Matrix.mulVec_smul]
          _ = (ρ / s) * (v ⬝ᵥ ((ρ / s) • (A⁻¹ *ᵥ v))) := by simp [smul_dotProduct]
          _ = (ρ / s) * ((ρ / s) * (v ⬝ᵥ (A⁻¹ *ᵥ v))) := by simp [dotProduct_smul]
          _ = (ρ ^ 2 / s ^ 2) * (v ⬝ᵥ (A⁻¹ *ᵥ v)) := by ring
          _ = (ρ ^ 2 / (v ⬝ᵥ v)) * (v ⬝ᵥ (A⁻¹ *ᵥ v)) := by rw [hs_sq]
      rw [h_simp] at hx_result
      -- (ρ^2 / (v·v)) * (v·A⁻¹v) ≤ 1
      -- Rewrite as (ρ^2 * (v·A⁻¹v)) / (v·v) ≤ 1 and use div_le_one
      have h_mul : ρ ^ 2 * (v ⬝ᵥ (A⁻¹ *ᵥ v)) ≤ v ⬝ᵥ v := by
        have htemp : (ρ ^ 2 * (v ⬝ᵥ (A⁻¹ *ᵥ v))) / (v ⬝ᵥ v) ≤ 1 := by
          calc
            (ρ ^ 2 * (v ⬝ᵥ (A⁻¹ *ᵥ v))) / (v ⬝ᵥ v) =
                (ρ ^ 2 / (v ⬝ᵥ v)) * (v ⬝ᵥ (A⁻¹ *ᵥ v)) := by ring
            _ ≤ 1 := hx_result
        exact (div_le_one hvv_pos).mp htemp
      exact h_mul
    -- combine: ρ^2 * (v·v)^2 ≤ (v·Av) * (v·v)
    have h_combined : ρ ^ 2 * (v ⬝ᵥ v) ^ 2 ≤ (v ⬝ᵥ (A *ᵥ v)) * (v ⬝ᵥ v) := by
      nlinarith
    -- divide by v·v > 0
    nlinarith

end AdversarialBco.Bit.Aux_pb_ball_quad

namespace AdversarialBco.Bit.Aux_pb_ball_det


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius

theorem _root_.AdversarialBco.Bit.pb_ball_det {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (h : ∀ v : Fin n → ℝ, ρ ^ 2 * (v ⬝ᵥ v) ≤ v ⬝ᵥ (A *ᵥ v)) : ρ ^ (2 * n) ≤ A.det := by
  have h_herm : A.IsHermitian := hA.isHermitian
  have h_det : A.det = ∏ i : Fin n, (h_herm.eigenvalues i : ℝ) := by
    simpa using h_herm.det_eq_prod_eigenvalues
  rw [h_det]
  have h_sq_nonneg : 0 ≤ ρ ^ 2 := by
    nlinarith
  have h_eigen_ge : ∀ i : Fin n, ρ ^ 2 ≤ (h_herm.eigenvalues i : ℝ) := by
    intro i
    have h_unit : inner ℝ (h_herm.eigenvectorBasis i) (h_herm.eigenvectorBasis i) = 1 :=
      OrthonormalBasis.inner_eq_one _ _
    have h_inner_eq : (h_herm.eigenvectorBasis i).ofLp ⬝ᵥ (h_herm.eigenvectorBasis i).ofLp = 1 := by
      rw [EuclideanSpace.inner_eq_star_dotProduct] at h_unit
      simpa using h_unit
    have h_mulVec : A.mulVec (h_herm.eigenvectorBasis i).ofLp =
        (h_herm.eigenvalues i : ℝ) • (h_herm.eigenvectorBasis i).ofLp :=
      h_herm.mulVec_eigenvectorBasis i
    have h_dot : (h_herm.eigenvectorBasis i).ofLp ⬝ᵥ A.mulVec (h_herm.eigenvectorBasis i).ofLp =
        (h_herm.eigenvalues i : ℝ) := by
      rw [h_mulVec, dotProduct_smul, smul_eq_mul, h_inner_eq, mul_one]
    have h_bound := h ((h_herm.eigenvectorBasis i).ofLp)
    rw [h_inner_eq, h_dot] at h_bound
    simpa [mul_one] using h_bound
  have h_prod : (∏ i : Fin n, ρ ^ 2) ≤ (∏ i : Fin n, (h_herm.eigenvalues i : ℝ)) := by
    refine Finset.prod_le_prod₀ (by
      intro i _
      nlinarith) (by
      intro i _
      exact h_eigen_ge i)
  have h_prod_const : (∏ i : Fin n, ρ ^ 2) = (ρ ^ 2) ^ n := by
    simp
  rw [h_prod_const] at h_prod
  have h_pow_mul : ρ ^ (2 * n) = (ρ ^ 2) ^ n := by
    rw [pow_mul]
  rw [h_pow_mul]
  exact h_prod

end AdversarialBco.Bit.Aux_pb_ball_det

namespace AdversarialBco.Bit.Aux_pb_sq_isqrt


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius

theorem _root_.AdversarialBco.Bit.pb_sq_isqrt (Y : ℝ) (hY : 4 ≤ Y) :
    2 ≤ Nat.sqrt ⌊Y ^ 2⌋₊ ∧ Y / 2 < (Nat.sqrt ⌊Y ^ 2⌋₊ : ℝ) ∧ (Nat.sqrt ⌊Y ^ 2⌋₊ : ℝ) ≤ Y ∧
      Y - (Nat.sqrt ⌊Y ^ 2⌋₊ : ℝ) < 2 := by
  set X := ⌊Y ^ 2⌋₊ with hX
  set t := Nat.sqrt X with ht
  have hY_nonneg : 0 ≤ Y := by linarith
  have hYsq_nonneg : 0 ≤ Y ^ 2 := pow_two_nonneg Y
  have hX_le_Ysq : (X : ℝ) ≤ Y ^ 2 := Nat.floor_le hYsq_nonneg
  have hYsq_lt_Xp1 : Y ^ 2 < (X : ℝ) + 1 := Nat.lt_floor_add_one (Y ^ 2)
  have htsq_le_X : (t : ℝ) ^ 2 ≤ (X : ℝ) := by
    have h := Nat.sqrt_le X
    -- h : t * t ≤ X in ℕ
    have h' : (t ^ 2 : ℕ) ≤ X := by
      -- Nat.sqrt_le X gives t * t ≤ X, and t * t = t ^ 2
      simpa [pow_two] using h
    exact mod_cast h'
  have hX_lt_tp1_sq : (X : ℝ) < ((t : ℕ).succ : ℝ) ^ 2 := by
    have h := Nat.lt_succ_sqrt' X
    -- h : X < t.succ ^ 2 in ℕ
    exact mod_cast h
  have h_t_le_Y : (t : ℝ) ≤ Y := by
    have h_sq : (t : ℝ) ^ 2 ≤ Y ^ 2 := by
      nlinarith
    have ht_nonneg : 0 ≤ (t : ℝ) := Nat.cast_nonneg _
    nlinarith
  have h_Y_sub_t_lt_two : Y - (t : ℝ) < 2 := by
    by_contra! hle
    -- hle : 2 ≤ Y - (t : ℝ), i.e., (t : ℝ) ≤ Y - 2
    have hle' : (t : ℝ) ≤ Y - 2 := by linarith
    have h_nonneg_Y_sub_one : 0 ≤ Y - 1 := by linarith
    have h_nonneg_t_succ : 0 ≤ ((t : ℕ).succ : ℝ) := Nat.cast_nonneg _
    have h_sq_le : ((t : ℕ).succ : ℝ) ^ 2 ≤ (Y - 1) ^ 2 := by
      have h_t_succ_le : ((t : ℕ).succ : ℝ) ≤ Y - 1 := by
        -- (t : ℝ) + 1 ≤ Y - 1
        have hcast : ((t : ℕ).succ : ℝ) = (t : ℝ) + 1 := by simp
        rw [hcast]
        linarith
      nlinarith
    have h_Y_sub_one_sq_le : (Y - 1) ^ 2 ≤ Y ^ 2 - 1 := by
      nlinarith
    have h_lt : Y ^ 2 - 1 < ((t : ℕ).succ : ℝ) ^ 2 := by
      linarith
    linarith
  have h_t_gt_Y_div_two : Y / 2 < (t : ℝ) := by
    have h : Y - 2 < (t : ℝ) := by linarith
    have h_ineq : Y / 2 ≤ Y - 2 := by
      nlinarith
    linarith
  have h_two_le_t : 2 ≤ t := by
    have h_t_gt_two : (2 : ℝ) < (t : ℝ) := by
      have h : Y - 2 < (t : ℝ) := by linarith
      have hY_minus_two_ge_two : (2 : ℝ) ≤ Y - 2 := by nlinarith
      linarith
    exact_mod_cast h_t_gt_two.le
  exact And.intro h_two_le_t (And.intro h_t_gt_Y_div_two (And.intro h_t_le_Y h_Y_sub_t_lt_two))

end AdversarialBco.Bit.Aux_pb_sq_isqrt

namespace AdversarialBco.Bit.Aux_pb_sq_b_norm


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius

theorem _root_.AdversarialBco.Bit.pb_sq_b_norm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) (Λ : ℝ)
    (hΛ : ∀ v : Fin n → ℝ, v ⬝ᵥ (A *ᵥ v) ≤ Λ * (v ⬝ᵥ v)) (c : Fin n → ℝ) :
    (A *ᵥ c) ⬝ᵥ (A *ᵥ c) ≤ Λ * (c ⬝ᵥ (A *ᵥ c)) := by
  set w := A *ᵥ c with hw_def
  have hA_symm : A.IsHermitian := hA.1
  have hA_nonneg : ∀ x : Fin n → ℝ, 0 ≤ x ⬝ᵥ (A *ᵥ x) := by
    intro x
    simpa using hA.posSemidef.dotProduct_mulVec_nonneg x
  have hB_symm : ∀ x y : Fin n → ℝ, x ⬝ᵥ (A *ᵥ y) = y ⬝ᵥ (A *ᵥ x) := by
    intro x y
    simpa using hA_symm.star_dotProduct_mulVec_comm x y
  have hw_dot_self : c ⬝ᵥ (A *ᵥ w) = w ⬝ᵥ w := by
    dsimp [w]
    simpa [hB_symm] using hB_symm c (A *ᵥ c)
  set a := w ⬝ᵥ (A *ᵥ w) with ha_def
  set b := w ⬝ᵥ w with hb_def
  set ccoeff := c ⬝ᵥ (A *ᵥ c) with hccoeff_def
  have h_quad_nonneg : ∀ t : ℝ, 0 ≤ a * (t * t) + (2 * b) * t + ccoeff := by
    intro t
    have h_expand : (c + t • w) ⬝ᵥ (A *ᵥ (c + t • w)) = a * (t * t) + (2 * b) * t + ccoeff := by
      calc
        (c + t • w) ⬝ᵥ (A *ᵥ (c + t • w))
            = (c + t • w) ⬝ᵥ (A *ᵥ c + A *ᵥ (t • w)) := by rw [mulVec_add]
        _ = (c + t • w) ⬝ᵥ (A *ᵥ c + t • (A *ᵥ w)) := by rw [mulVec_smul]
        _ = c ⬝ᵥ (A *ᵥ c + t • (A *ᵥ w)) + (t • w) ⬝ᵥ (A *ᵥ c + t • (A *ᵥ w)) := by rw [add_dotProduct]
        _ = (c ⬝ᵥ (A *ᵥ c) + c ⬝ᵥ (t • (A *ᵥ w))) + ((t • w) ⬝ᵥ (A *ᵥ c) + (t • w) ⬝ᵥ (t • (A *ᵥ w))) := by
          rw [dotProduct_add, dotProduct_add]
        _ = (c ⬝ᵥ (A *ᵥ c) + t * (c ⬝ᵥ (A *ᵥ w))) + (t * (w ⬝ᵥ (A *ᵥ c)) + (t * t) * (w ⬝ᵥ (A *ᵥ w))) := by
          simp [dotProduct_smul, smul_dotProduct, mul_assoc]
        _ = (c ⬝ᵥ (A *ᵥ c)) + t * (c ⬝ᵥ (A *ᵥ w) + w ⬝ᵥ (A *ᵥ c)) + t * t * (w ⬝ᵥ (A *ᵥ w)) := by ring
        _ = (c ⬝ᵥ (A *ᵥ c)) + t * (w ⬝ᵥ w + w ⬝ᵥ (A *ᵥ c)) + t * t * (w ⬝ᵥ (A *ᵥ w)) := by rw [hw_dot_self]
        _ = (c ⬝ᵥ (A *ᵥ c)) + t * (w ⬝ᵥ w + c ⬝ᵥ (A *ᵥ w)) + t * t * (w ⬝ᵥ (A *ᵥ w)) := by rw [hB_symm c w]
        _ = ccoeff + t * (b + b) + t * t * a := by
          simp [ha_def, hb_def, hccoeff_def, hw_dot_self]
        _ = a * (t * t) + (2 * b) * t + ccoeff := by ring
    rw [← h_expand]
    exact hA_nonneg (c + t • w)
  have h_discrim_nonpos : discrim a (2 * b) ccoeff ≤ 0 :=
    discrim_le_zero h_quad_nonneg
  have h_ineq : b * b ≤ a * ccoeff := by
    have h_discrim_eq : discrim a (2 * b) ccoeff = (2 * b) * (2 * b) - 4 * a * ccoeff := by
      simp [discrim, sq]
    rw [h_discrim_eq] at h_discrim_nonpos
    nlinarith
  have hΛ_w : w ⬝ᵥ (A *ᵥ w) ≤ Λ * (w ⬝ᵥ w) := hΛ w
  rw [← ha_def, ← hb_def] at hΛ_w
  have hb_nonneg : 0 ≤ b := by
    rw [hb_def]
    simpa using dotProduct_star_self_nonneg w
  have hccoeff_nonneg : 0 ≤ ccoeff := by
    rw [hccoeff_def]
    exact hA_nonneg c
  by_cases hb_zero : b = 0
  · rw [hb_zero]
    simp
    by_cases hn : Nonempty (Fin n)
    · -- n > 0: we can show Λ ≥ 0 using a basis vector
      have hΛ_nonneg : 0 ≤ Λ := by
        obtain ⟨i⟩ := hn
        let e : Fin n → ℝ := Pi.single i (1 : ℝ)
        have he_pos : e ⬝ᵥ e = 1 := by
          rw [dotProduct_single]
          simp [e]
        have he_nonzero : e ≠ 0 := by
          intro hzero
          have : e i = (0 : Fin n → ℝ) i := by rw [hzero]
          simp [e] at this
        have heAe_pos : 0 < e ⬝ᵥ (A *ᵥ e) :=
          hA.dotProduct_mulVec_pos he_nonzero
        have hΛ_e := hΛ e
        rw [he_pos] at hΛ_e
        linarith
      nlinarith
    · -- n = 0: Fin 0 → ℝ has only zero vector
      have hc_zero : c = 0 := by
        have hw_zero : w = 0 := by
          rw [← dotProduct_self_eq_zero, ← hb_def, hb_zero]
        have hc_zero' : A *ᵥ c = 0 := by rwa [hw_def] at hw_zero
        by_contra! hc_nonzero
        have hpos : 0 < c ⬝ᵥ (A *ᵥ c) := hA.dotProduct_mulVec_pos hc_nonzero
        rw [hc_zero'] at hpos
        simp at hpos
      rw [hccoeff_def, hc_zero]
      simp
  · have hb_pos : 0 < b := by
      by_contra! hle
      have : b = 0 := le_antisymm hle hb_nonneg
      exact hb_zero this
    nlinarith

end AdversarialBco.Bit.Aux_pb_sq_b_norm

namespace AdversarialBco.Bit.Aux_pb_sq_main


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius

theorem _root_.AdversarialBco.Bit.pb_sq_main {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) (ρ Λ : ℝ) (hρ : 0 < ρ)
    (hball : ∀ v : Fin n → ℝ, ρ ^ 2 * (v ⬝ᵥ v) ≤ v ⬝ᵥ (A *ᵥ v))
    (hΛ : ∀ v : Fin n → ℝ, v ⬝ᵥ (A *ᵥ v) ≤ Λ * (v ⬝ᵥ v)) (c : Fin n → ℤ) (hc : c ≠ 0) (q : ℕ)
    (hq : 4 / ρ ≤ 2 ^ q) :
    1 ≤ Nat.sqrt ⌊(fun i => (c i : ℝ)) ⬝ᵥ (A *ᵥ fun i => (c i : ℝ)) * 2 ^ (2 * q)⌋₊ ∧
      ((((2 : ℝ) ^ q / Nat.sqrt ⌊(fun i => (c i : ℝ)) ⬝ᵥ (A *ᵥ fun i => (c i : ℝ)) * 2 ^ (2 * q)⌋₊) -
            1 / Real.sqrt ((fun i => (c i : ℝ)) ⬝ᵥ (A *ᵥ fun i => (c i : ℝ)))) •
          (A *ᵥ fun i => (c i : ℝ))) ⬝ᵥ
        ((((2 : ℝ) ^ q / Nat.sqrt ⌊(fun i => (c i : ℝ)) ⬝ᵥ (A *ᵥ fun i => (c i : ℝ)) * 2 ^ (2 * q)⌋₊) -
            1 / Real.sqrt ((fun i => (c i : ℝ)) ⬝ᵥ (A *ᵥ fun i => (c i : ℝ)))) •
          (A *ᵥ fun i => (c i : ℝ))) ≤ (4 * Real.sqrt Λ / (ρ * 2 ^ q)) ^ 2 := by
  let cr : Fin n → ℝ := fun i => (c i : ℝ)
  have hcr_ne_zero : cr ≠ 0 := by
    intro h
    apply hc
    ext i
    have h_eq := congr_fun h i
    simpa [cr] using h_eq
  have hcr_dot_pos : 0 < cr ⬝ᵥ cr := by
    have h_nonneg : 0 ≤ cr ⬝ᵥ cr := by
      rw [dotProduct]
      refine Finset.sum_nonneg (fun i _ => ?_)
      nlinarith [sq_nonneg (cr i)]
    have h_ne_zero : cr ⬝ᵥ cr ≠ 0 :=
      mt (dotProduct_self_eq_zero (v := cr)).mp hcr_ne_zero
    exact lt_of_le_of_ne h_nonneg h_ne_zero.symm
  have h_one_le_dot : 1 ≤ cr ⬝ᵥ cr := by
    have h_exists : ∃ i, c i ≠ 0 := by
      contrapose! hc
      ext i
      exact hc i
    rcases h_exists with ⟨i, hi⟩
    have h_sq_ge_one : 1 ≤ cr i * cr i := by
      have h_abs_ge_one : (1 : ℝ) ≤ |cr i| := by
        have h_int_abs : 1 ≤ |c i| := Int.one_le_abs hi
        have : cr i = (c i : ℝ) := rfl
        rw [this]
        exact_mod_cast h_int_abs
      nlinarith [sq_abs (cr i)]
    rw [dotProduct]
    have h_sum : cr i * cr i ≤ ∑ j : Fin n, cr j * cr j :=
      Finset.single_le_sum (f := fun j => cr j * cr j)
        (fun j _ => by nlinarith [sq_nonneg (cr j)]) (Finset.mem_univ i)
    calc
      1 ≤ cr i * cr i := h_sq_ge_one
      _ ≤ ∑ j : Fin n, cr j * cr j := h_sum
  let s := cr ⬝ᵥ (A *ᵥ cr)
  have hs_pos : 0 < s := by
    have h_lower : ρ ^ 2 * (cr ⬝ᵥ cr) ≤ s := hball cr
    have h_pos : 0 < ρ ^ 2 * (cr ⬝ᵥ cr) := by positivity
    linarith
  have hs_nonneg : 0 ≤ s := le_of_lt hs_pos
  have hΛ_nonneg : 0 ≤ Λ := by
    have h_upper : s ≤ Λ * (cr ⬝ᵥ cr) := hΛ cr
    by_contra! hneg
    have : Λ * (cr ⬝ᵥ cr) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (le_of_lt hneg) (le_of_lt hcr_dot_pos)
    linarith
  let Y := Real.sqrt s * ((2 : ℝ) ^ q)
  have h_sqrt_s_ge_rho : ρ ≤ Real.sqrt s := by
    have h_rho_sq_le_s : ρ ^ 2 ≤ s := by
      have h_lower : ρ ^ 2 * (cr ⬝ᵥ cr) ≤ s := hball cr
      nlinarith
    have h_sq_le : ρ ^ 2 ≤ (Real.sqrt s) ^ 2 := by
      rw [Real.sq_sqrt hs_nonneg]
      exact h_rho_sq_le_s
    exact le_of_pow_le_pow_left₀ (by norm_num) (Real.sqrt_nonneg _) h_sq_le
  have hY_ge_four : 4 ≤ Y := by
    have h_q_ineq : (4 : ℝ) / ρ ≤ ((2 : ℝ) ^ q) := by exact_mod_cast hq
    have h_four_le_ρ_mul : 4 ≤ ρ * ((2 : ℝ) ^ q) := by
      have := (div_le_iff₀ hρ).mp h_q_ineq
      -- this gives 4 ≤ (2^q) * ρ
      simpa [mul_comm] using this
    have h_ρ_mul_le_Y : ρ * ((2 : ℝ) ^ q) ≤ Y := by
      dsimp [Y]
      gcongr
    linarith
  have hY_sq_eq : Y ^ 2 = s * ((2 : ℝ) ^ (2 * q)) := by
    calc
      Y ^ 2 = (Real.sqrt s) ^ 2 * (((2 : ℝ) ^ q) ^ 2) := by ring
      _ = s * (((2 : ℝ) ^ q) ^ 2) := by rw [Real.sq_sqrt hs_nonneg]
      _ = s * ((2 : ℝ) ^ (2 * q)) := by rw [← pow_mul, mul_comm q 2]
  let t : ℕ := Nat.sqrt ⌊Y ^ 2⌋₊
  have h_isqrt := pb_sq_isqrt Y hY_ge_four
  rcases h_isqrt with ⟨h2t, hYt_lt, htY, hYt_sub⟩
  have ht_nonneg : 0 ≤ (t : ℝ) := Nat.cast_nonneg _
  have ht_pos : 0 < (t : ℝ) := by
    have hY_pos : 0 < Y := by linarith
    linarith
  have h_one_le_t : 1 ≤ t := by
    have : 2 ≤ t := h2t
    omega
  have h_sqrt_s_pos : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs_pos
  have h_pow_pos : 0 < ((2 : ℝ) ^ q) := pow_pos (by norm_num) _
  have h_coeff_eq : ((2 : ℝ) ^ q / (t : ℝ) - 1 / Real.sqrt s) = (Y - (t : ℝ)) / ((t : ℝ) * Real.sqrt s) := by
    field_simp [ne_of_gt h_sqrt_s_pos, ne_of_gt ht_pos]
    ring
  have h_norm_bound : (A *ᵥ cr) ⬝ᵥ (A *ᵥ cr) ≤ Λ * s := pb_sq_b_norm A hA Λ hΛ cr
  have h_sq_norm : (((2 : ℝ) ^ q / (t : ℝ) - 1 / Real.sqrt s) • (A *ᵥ cr)) ⬝ᵥ
      (((2 : ℝ) ^ q / (t : ℝ) - 1 / Real.sqrt s) • (A *ᵥ cr)) ≤
      ((Y - (t : ℝ)) / (t : ℝ)) ^ 2 * Λ := by
    set x := ((2 : ℝ) ^ q / (t : ℝ) - 1 / Real.sqrt s) with hx
    have h_sq_expand : (x • (A *ᵥ cr)) ⬝ᵥ (x • (A *ᵥ cr)) = x ^ 2 * ((A *ᵥ cr) ⬝ᵥ (A *ᵥ cr)) := by
      calc
        (x • (A *ᵥ cr)) ⬝ᵥ (x • (A *ᵥ cr)) = x • ((A *ᵥ cr) ⬝ᵥ (x • (A *ᵥ cr))) := by
          rw [smul_dotProduct]
        _ = x • (x • ((A *ᵥ cr) ⬝ᵥ (A *ᵥ cr))) := by rw [dotProduct_smul]
        _ = (x * x) • ((A *ᵥ cr) ⬝ᵥ (A *ᵥ cr)) := by rw [smul_smul]
        _ = x ^ 2 * ((A *ᵥ cr) ⬝ᵥ (A *ᵥ cr)) := by ring
    rw [h_sq_expand, h_coeff_eq]
    have h_sq_eq : ((Y - (t : ℝ)) / ((t : ℝ) * Real.sqrt s)) ^ 2 =
        ((Y - (t : ℝ)) ^ 2) / ((t : ℝ) ^ 2 * s) := by
      calc
        ((Y - (t : ℝ)) / ((t : ℝ) * Real.sqrt s)) ^ 2 =
            (Y - (t : ℝ)) ^ 2 / (((t : ℝ) * Real.sqrt s) ^ 2) := by ring
        _ = (Y - (t : ℝ)) ^ 2 / ((t : ℝ) ^ 2 * (Real.sqrt s) ^ 2) := by ring
        _ = (Y - (t : ℝ)) ^ 2 / ((t : ℝ) ^ 2 * s) := by rw [Real.sq_sqrt hs_nonneg]
    rw [h_sq_eq]
    calc
      ((Y - (t : ℝ)) ^ 2 / ((t : ℝ) ^ 2 * s)) * ((A *ᵥ cr) ⬝ᵥ (A *ᵥ cr)) =
          ((Y - (t : ℝ)) ^ 2 / (t : ℝ) ^ 2) * (((A *ᵥ cr) ⬝ᵥ (A *ᵥ cr)) / s) := by ring
      _ ≤ ((Y - (t : ℝ)) ^ 2 / (t : ℝ) ^ 2) * ((Λ * s) / s) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        gcongr
      _ = ((Y - (t : ℝ)) ^ 2 / (t : ℝ) ^ 2) * Λ := by
        field_simp [ne_of_gt hs_pos]
      _ = ((Y - (t : ℝ)) / (t : ℝ)) ^ 2 * Λ := by ring
  have h_ratio_bound : (Y - (t : ℝ)) / (t : ℝ) ≤ 4 / (ρ * ((2 : ℝ) ^ q)) := by
    have hYt_nonneg : 0 ≤ Y - (t : ℝ) := by
      have : (t : ℝ) ≤ Y := htY
      linarith
    have h_bound1 : (Y - (t : ℝ)) / (t : ℝ) < 2 / (t : ℝ) :=
      div_lt_div_of_pos_right (by linarith) ht_pos
    have h_bound2 : 2 / (t : ℝ) < 4 / Y := by
      have hY_pos : 0 < Y := by linarith
      have h_ineq : Y / 2 < (t : ℝ) := hYt_lt
      have h_lt' : Y < 2 * (t : ℝ) := by linarith
      have h_inv : 1 / (2 * (t : ℝ)) < 1 / Y :=
        (one_div_lt_one_div (by positivity) hY_pos).mpr h_lt'
      calc
        2 / (t : ℝ) = 2 * (1 / (t : ℝ)) := by ring
        _ = 2 * (2 * (1 / (2 * (t : ℝ)))) := by ring
        _ = 4 * (1 / (2 * (t : ℝ))) := by ring
        _ < 4 * (1 / Y) := by gcongr
        _ = 4 / Y := by ring
    have h_bound3 : 4 / Y ≤ 4 / (ρ * ((2 : ℝ) ^ q)) := by
      have hY_ge_4ρ : Y ≥ ρ * ((2 : ℝ) ^ q) := by
        dsimp [Y]
        gcongr
      have hY_pos : 0 < Y := by linarith
      have h_denom_pos : 0 < ρ * ((2 : ℝ) ^ q) := by positivity
      have h_one_div : 1 / Y ≤ 1 / (ρ * ((2 : ℝ) ^ q)) :=
        (one_div_le_one_div hY_pos h_denom_pos).mpr hY_ge_4ρ
      calc
        4 / Y = 4 * (1 / Y) := by ring
        _ ≤ 4 * (1 / (ρ * ((2 : ℝ) ^ q))) := by gcongr
        _ = 4 / (ρ * ((2 : ℝ) ^ q)) := by ring
    have h_nonneg_ratio : 0 ≤ (Y - (t : ℝ)) / (t : ℝ) := div_nonneg hYt_nonneg (by linarith)
    have h_nonneg_target : 0 ≤ 4 / (ρ * ((2 : ℝ) ^ q)) := by positivity
    linarith
  have h_final : ((Y - (t : ℝ)) / (t : ℝ)) ^ 2 * Λ ≤ (4 * Real.sqrt Λ / (ρ * ((2 : ℝ) ^ q))) ^ 2 := by
    have h_sq_bound : ((Y - (t : ℝ)) / (t : ℝ)) ^ 2 ≤ (4 / (ρ * ((2 : ℝ) ^ q))) ^ 2 := by
      have h_nonneg_ratio : 0 ≤ (Y - (t : ℝ)) / (t : ℝ) := by
        have hYt_nonneg : 0 ≤ Y - (t : ℝ) := by
          have : (t : ℝ) ≤ Y := htY
          linarith
        exact div_nonneg hYt_nonneg (by linarith)
      have h_nonneg_target : 0 ≤ 4 / (ρ * ((2 : ℝ) ^ q)) := by positivity
      gcongr
    calc
      ((Y - (t : ℝ)) / (t : ℝ)) ^ 2 * Λ ≤ (4 / (ρ * ((2 : ℝ) ^ q))) ^ 2 * Λ := by
        nlinarith
      _ = (4 * Real.sqrt Λ / (ρ * ((2 : ℝ) ^ q))) ^ 2 := by
        calc
          (4 / (ρ * ((2 : ℝ) ^ q))) ^ 2 * Λ = ((4 / (ρ * ((2 : ℝ) ^ q))) ^ 2) * ((Real.sqrt Λ) ^ 2) := by
            rw [Real.sq_sqrt hΛ_nonneg]
          _ = (4 * Real.sqrt Λ / (ρ * ((2 : ℝ) ^ q))) ^ 2 := by ring
  let coeff : ℝ := ((2 : ℝ) ^ q / (t : ℝ) - 1 / Real.sqrt s)
  have h_left : 1 ≤ Nat.sqrt ⌊(fun i => (c i : ℝ)) ⬝ᵥ (A *ᵥ fun i => (c i : ℝ)) * 2 ^ (2 * q)⌋₊ := by
    have h_sqrt_eq : Nat.sqrt ⌊(fun i => (c i : ℝ)) ⬝ᵥ (A *ᵥ fun i => (c i : ℝ)) * 2 ^ (2 * q)⌋₊ = t := by
      dsimp [t, cr, s]
      rw [hY_sq_eq]
    rw [h_sqrt_eq]
    exact h_one_le_t
  have h_right : (coeff • (A *ᵥ fun i => (c i : ℝ))) ⬝ᵥ (coeff • (A *ᵥ fun i => (c i : ℝ))) ≤
      (4 * Real.sqrt Λ / (ρ * 2 ^ q)) ^ 2 := by
    have h_expr_eq : (coeff • (A *ᵥ fun i => (c i : ℝ))) ⬝ᵥ (coeff • (A *ᵥ fun i => (c i : ℝ))) =
        (coeff • (A *ᵥ cr)) ⬝ᵥ (coeff • (A *ᵥ cr)) := by
      dsimp [cr]
    rw [h_expr_eq]
    have h_coeff_eq' : coeff = ((2 : ℝ) ^ q / (t : ℝ) - 1 / Real.sqrt s) := rfl
    rw [h_coeff_eq']
    calc
      (((2 : ℝ) ^ q / (t : ℝ) - 1 / Real.sqrt s) • (A *ᵥ cr)) ⬝ᵥ
          (((2 : ℝ) ^ q / (t : ℝ) - 1 / Real.sqrt s) • (A *ᵥ cr)) ≤
          ((Y - (t : ℝ)) / (t : ℝ)) ^ 2 * Λ := h_sq_norm
      _ ≤ (4 * Real.sqrt Λ / (ρ * ((2 : ℝ) ^ q))) ^ 2 := h_final
      _ = (4 * Real.sqrt Λ / (ρ * 2 ^ q)) ^ 2 := by simp
  -- Now combine h_left and h_right to get the final goal
  -- The goal is: 1 ≤ ... ∧ (coeff' • ...) ⬝ᵥ ... ≤ ...
  -- where coeff' is the long expression involving Nat.sqrt
  -- We have h_left: 1 ≤ ...
  -- And we need to show the right part equals (coeff • ...) ⬝ᵥ ...
  -- Let's use `simpa [coeff, t, cr, s, hY_sq_eq]` using `h_right`
  simpa [coeff, t, cr, s, hY_sq_eq] using And.intro h_left h_right

end AdversarialBco.Bit.Aux_pb_sq_main

namespace AdversarialBco.Bit.Aux_pb_cap_gamma


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius

theorem _root_.AdversarialBco.Bit.pb_cap_gamma (d : ℕ) (hd : 2 ≤ d) :
    (d : ℝ) * (2 * d + 1) ^ 2 / (4 * ((d : ℝ) + 1) ^ 2 * ((d : ℝ) - 1)) + 1 / (128 * d * ((d : ℝ) + 1)) ≤
      Real.exp (1 / ((d : ℝ) ^ 2 - 1) + 33 / (128 * d * ((d : ℝ) + 1))) := by
  -- cast the natural number inequality to ℝ
  have hd_real : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hpos : 0 < (d : ℝ) := by linarith
  have hpos_sq_sub_one : 0 < (d : ℝ) ^ 2 - 1 := by
    nlinarith
  have hpos_d_plus_one : 0 < (d : ℝ) + 1 := by linarith
  have hpos_d_minus_one : 0 < (d : ℝ) - 1 := by linarith
  have hpos_128d : 0 < 128 * (d : ℝ) * ((d : ℝ) + 1) := by positivity
  have hpos_128d' : 0 < 128 * d * ((d : ℝ) + 1) := by positivity
  have hterm_nonneg : 0 ≤ 1 / (128 * d * ((d : ℝ) + 1)) :=
    div_nonneg (by norm_num) (by positivity)
  -- define κ for readability
  set κ := (d : ℝ) * (2 * (d : ℝ) + 1) ^ 2 / (4 * ((d : ℝ) + 1) ^ 2 * ((d : ℝ) - 1)) with hκ_def
  -- algebraic identity: κ = (1 + 1/(d²-1)) * (1 + 1/(4d(d+1)))
  have hkappa_eq : κ = (1 + 1 / ((d : ℝ) ^ 2 - 1)) * (1 + 1 / (4 * (d : ℝ) * ((d : ℝ) + 1))) := by
    dsimp [κ]
    field_simp [hpos_sq_sub_one.ne.symm, hpos_d_plus_one.ne.symm, hpos_d_minus_one.ne.symm, hpos.ne.symm]
    ring
  -- each factor is ≥ 1
  have hfactor1_ge_one : 1 ≤ 1 + 1 / ((d : ℝ) ^ 2 - 1) := by
    have : 0 ≤ 1 / ((d : ℝ) ^ 2 - 1) := div_nonneg (by norm_num) (by linarith)
    linarith
  have hfactor2_ge_one : 1 ≤ 1 + 1 / (4 * (d : ℝ) * ((d : ℝ) + 1)) := by
    have : 0 ≤ 1 / (4 * (d : ℝ) * ((d : ℝ) + 1)) := div_nonneg (by norm_num) (by positivity)
    linarith
  -- κ ≥ 1
  have hkappa_ge_one : 1 ≤ κ := by
    rw [hkappa_eq]
    have hprod_ge_one : 1 * 1 ≤ (1 + 1 / ((d : ℝ) ^ 2 - 1)) * (1 + 1 / (4 * (d : ℝ) * ((d : ℝ) + 1))) :=
      mul_le_mul hfactor1_ge_one hfactor2_ge_one (by positivity) (by linarith)
    linarith
  -- γ ≤ κ * (1 + 1/(128d(d+1)))
  have h_gamma_le_kappa_mul : κ + 1 / (128 * d * ((d : ℝ) + 1)) ≤ κ * (1 + 1 / (128 * d * ((d : ℝ) + 1))) := by
    nlinarith
  -- bound each factor by its exponential
  have hfactor1_exp : 1 + 1 / ((d : ℝ) ^ 2 - 1) ≤ Real.exp (1 / ((d : ℝ) ^ 2 - 1)) := by
    have := Real.add_one_le_exp (1 / ((d : ℝ) ^ 2 - 1))
    linarith
  have hfactor2_exp : 1 + 1 / (4 * (d : ℝ) * ((d : ℝ) + 1)) ≤ Real.exp (1 / (4 * (d : ℝ) * ((d : ℝ) + 1))) := by
    have := Real.add_one_le_exp (1 / (4 * (d : ℝ) * ((d : ℝ) + 1)))
    linarith
  -- κ ≤ exp(1/(d²-1)) * exp(1/(4d(d+1)))
  have hkappa_le_exp_prod : κ ≤ Real.exp (1 / ((d : ℝ) ^ 2 - 1)) * Real.exp (1 / (4 * (d : ℝ) * ((d : ℝ) + 1))) := by
    rw [hkappa_eq]
    have h_nonneg_factor1 : 0 ≤ 1 + 1 / ((d : ℝ) ^ 2 - 1) := by linarith
    have h_nonneg_factor2 : 0 ≤ 1 + 1 / (4 * (d : ℝ) * ((d : ℝ) + 1)) := by linarith
    exact mul_le_mul hfactor1_exp hfactor2_exp h_nonneg_factor2 (by linarith)
  -- exp product = exp of sum
  have hexp_prod : Real.exp (1 / ((d : ℝ) ^ 2 - 1)) * Real.exp (1 / (4 * (d : ℝ) * ((d : ℝ) + 1))) =
      Real.exp (1 / ((d : ℝ) ^ 2 - 1) + 1 / (4 * (d : ℝ) * ((d : ℝ) + 1))) := by
    rw [Real.exp_add]
  -- combine: κ ≤ exp(1/(d²-1) + 1/(4d(d+1)))
  have hkappa_le_exp_sum : κ ≤ Real.exp (1 / ((d : ℝ) ^ 2 - 1) + 1 / (4 * (d : ℝ) * ((d : ℝ) + 1))) := by
    linarith
  -- bound the third factor by its exponential
  have hfactor3_exp : 1 + 1 / (128 * d * ((d : ℝ) + 1)) ≤ Real.exp (1 / (128 * d * ((d : ℝ) + 1))) := by
    have := Real.add_one_le_exp (1 / (128 * d * ((d : ℝ) + 1)))
    linarith
  have h_nonneg_factor3 : 0 ≤ 1 + 1 / (128 * d * ((d : ℝ) + 1)) := by linarith
  -- now: γ ≤ κ * (1 + 1/(128d(d+1))) ≤ exp(...) * exp(1/(128d(d+1))) = exp(... + ...)
  have h_gamma_le_exp : κ + 1 / (128 * d * ((d : ℝ) + 1)) ≤
      Real.exp (1 / ((d : ℝ) ^ 2 - 1) + 1 / (4 * (d : ℝ) * ((d : ℝ) + 1))) *
      Real.exp (1 / (128 * d * ((d : ℝ) + 1))) := by
    have h_mul : κ * (1 + 1 / (128 * d * ((d : ℝ) + 1))) ≤
        Real.exp (1 / ((d : ℝ) ^ 2 - 1) + 1 / (4 * (d : ℝ) * ((d : ℝ) + 1))) *
        Real.exp (1 / (128 * d * ((d : ℝ) + 1))) := by
      exact mul_le_mul hkappa_le_exp_sum hfactor3_exp h_nonneg_factor3 (by positivity)
    linarith
  -- exp(a) * exp(b) = exp(a + b)
  have hfinal : Real.exp (1 / ((d : ℝ) ^ 2 - 1) + 1 / (4 * (d : ℝ) * ((d : ℝ) + 1))) *
      Real.exp (1 / (128 * d * ((d : ℝ) + 1))) =
      Real.exp ((1 / ((d : ℝ) ^ 2 - 1) + 1 / (4 * (d : ℝ) * ((d : ℝ) + 1))) + 1 / (128 * d * ((d : ℝ) + 1))) := by
    simp [Real.exp_add]
  -- simplify the exponent: 1/(d²-1) + 1/(4d(d+1)) + 1/(128d(d+1)) = 1/(d²-1) + 33/(128d(d+1))
  have hexp_simplify : (1 / ((d : ℝ) ^ 2 - 1) + 1 / (4 * (d : ℝ) * ((d : ℝ) + 1))) + 1 / (128 * d * ((d : ℝ) + 1)) =
      1 / ((d : ℝ) ^ 2 - 1) + 33 / (128 * d * ((d : ℝ) + 1)) := by
    field_simp [hpos_sq_sub_one.ne.symm, hpos_d_plus_one.ne.symm, hpos.ne.symm]
    ring
  rw [hfinal, hexp_simplify] at h_gamma_le_exp
  exact h_gamma_le_exp

end AdversarialBco.Bit.Aux_pb_cap_gamma

namespace AdversarialBco.Bit.Aux_pb_cap_d2


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius

theorem _root_.AdversarialBco.Bit.pb_cap_d2 (L : ℕ) : ((3203 : ℝ) / 2304) ^ (12 * L + 1) ≤ 2 ^ (6 * L + 2) := by
  have h1 : ((3203 : ℝ) / 2304) ^ 12 ≤ (64 : ℝ) := by
    norm_num
  have h2 : ((3203 : ℝ) / 2304) ≤ (4 : ℝ) := by
    norm_num
  calc
    ((3203 : ℝ) / 2304) ^ (12 * L + 1)
        = ((3203 : ℝ) / 2304) ^ (12 * L) * ((3203 : ℝ) / 2304) := by rw [pow_succ]
    _ = (((3203 : ℝ) / 2304) ^ 12) ^ L * ((3203 : ℝ) / 2304) := by rw [← pow_mul]
    _ ≤ (64 : ℝ) ^ L * (4 : ℝ) := by
      gcongr
    _ = ((2 : ℝ) ^ 6) ^ L * (2 : ℝ) ^ 2 := by norm_num
    _ = (2 : ℝ) ^ (6 * L) * (2 : ℝ) ^ 2 := by rw [← pow_mul]
    _ = (2 : ℝ) ^ (6 * L + 2) := by rw [pow_add]

end AdversarialBco.Bit.Aux_pb_cap_d2

namespace AdversarialBco.Bit.Aux_pb_cap_count


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius

theorem _root_.AdversarialBco.Bit.pb_cap_count (d L : ℕ) (hd : 3 ≤ d) :
    (2 * (d : ℝ) * ((d : ℝ) + 1) * L + 1) * (1 / ((d : ℝ) ^ 2 - 1) + 33 / (128 * d * ((d : ℝ) + 1))) ≤
      (6 * (L : ℝ) + 2) * Real.log 2 := by
  have hd' : (3 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hlog : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hdpos' : 0 < (d : ℝ) - 1 := by linarith
  have hdsqpos : 0 < (d : ℝ) ^ 2 - 1 := by nlinarith
  have hdenompos : 0 < 128 * (d : ℝ) * ((d : ℝ) + 1) := by nlinarith
  have hbound1 : 2 * (d : ℝ) / ((d : ℝ) - 1) ≤ 3 := by
    rw [div_le_iff₀ hdpos']
    nlinarith
  have hbound2 : 1 / ((d : ℝ) ^ 2 - 1) ≤ 1/8 := by
    rw [div_le_iff₀ hdsqpos]
    nlinarith
  have hbound3 : 33 / (128 * (d : ℝ) * ((d : ℝ) + 1)) ≤ 33/1536 := by
    rw [div_le_iff₀ hdenompos]
    nlinarith
  have hL : 0 ≤ (L : ℝ) := by exact_mod_cast Nat.zero_le L
  have h_expand : (2 * (d : ℝ) * ((d : ℝ) + 1) * (L : ℝ) + 1) * (1 / ((d : ℝ) ^ 2 - 1) + 33 / (128 * (d : ℝ) * ((d : ℝ) + 1))) =
      (2 * (d : ℝ) / ((d : ℝ) - 1)) * (L : ℝ) + (33/64 : ℝ) * (L : ℝ) + 1 / ((d : ℝ) ^ 2 - 1) + 33 / (128 * (d : ℝ) * ((d : ℝ) + 1)) := by
    field_simp [hdsqpos.ne.symm, hdenompos.ne.symm, hdpos'.ne.symm]
    ring_nf
  rw [h_expand]
  have h_sum : (2 * (d : ℝ) / ((d : ℝ) - 1)) * (L : ℝ) + (33/64 : ℝ) * (L : ℝ) + 1 / ((d : ℝ) ^ 2 - 1) + 33 / (128 * (d : ℝ) * ((d : ℝ) + 1)) ≤
      3 * (L : ℝ) + (33/64 : ℝ) * (L : ℝ) + 1/8 + 33/1536 := by
    nlinarith
  have h_final : 3 * (L : ℝ) + (33/64 : ℝ) * (L : ℝ) + 1/8 + 33/1536 ≤ (6 * (L : ℝ) + 2) * Real.log 2 := by
    nlinarith
  linarith

end AdversarialBco.Bit.Aux_pb_cap_count

namespace AdversarialBco.Bit.Aux_pb_cap_general


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius

theorem _root_.AdversarialBco.Bit.pb_cap_general (d L k : ℕ) (hd : 2 ≤ d) (hk : k ≤ 2 * d * (d + 1) * L + 1) :
    ((d : ℝ) * (2 * d + 1) ^ 2 / (4 * ((d : ℝ) + 1) ^ 2 * ((d : ℝ) - 1)) + 1 / (128 * d * ((d : ℝ) + 1))) ^ k ≤
      2 ^ (6 * L + 2) := by
  set γ := (d : ℝ) * (2 * d + 1) ^ 2 / (4 * ((d : ℝ) + 1) ^ 2 * ((d : ℝ) - 1)) + 1 / (128 * d * ((d : ℝ) + 1)) with hγ
  set N := 2 * d * (d + 1) * L + 1 with hN
  have hd' : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hd_pos : 0 < (d : ℝ) := by linarith
  have hγ_ge_one : 1 ≤ γ := by
    have hpos_denom : 0 < 4 * ((d : ℝ) + 1) ^ 2 * ((d : ℝ) - 1) := by
      have hd1_pos : 0 < (d : ℝ) - 1 := by linarith
      positivity
    have h_first_ge_one : 1 ≤ (d : ℝ) * (2 * d + 1) ^ 2 / (4 * ((d : ℝ) + 1) ^ 2 * ((d : ℝ) - 1)) := by
      refine (one_le_div hpos_denom).mpr ?_
      nlinarith
    have h_second_nonneg : 0 ≤ 1 / (128 * d * ((d : ℝ) + 1)) := by
      positivity
    linarith
  have hγ_nonneg : 0 ≤ γ := by linarith
  have h_pow_le : γ ^ k ≤ γ ^ N :=
    pow_le_pow_right₀ hγ_ge_one hk
  by_cases hd2 : d = 2
  · subst hd2
    have hγ2 : γ = (3203 : ℝ) / 2304 := by
      dsimp [γ]
      norm_num
    have hN2 : N = 12 * L + 1 := by
      omega
    rw [hγ2] at h_pow_le ⊢
    rw [hN2] at h_pow_le
    have h_pb_cap_d2 := pb_cap_d2 L
    exact le_trans h_pow_le h_pb_cap_d2
  · have hd3 : 3 ≤ d := by
      omega
    set x := 1 / ((d : ℝ) ^ 2 - 1) + 33 / (128 * d * ((d : ℝ) + 1)) with hx
    have hγ_le_exp : γ ≤ Real.exp x := by
      rw [hγ, hx]
      exact pb_cap_gamma d hd
    have h_exp_pow : (Real.exp x) ^ N = Real.exp ((N : ℝ) * x) := by
      rw [← Real.exp_nat_mul x N]
    have h_γN_le_expN : γ ^ N ≤ (Real.exp x) ^ N :=
      pow_le_pow_left₀ hγ_nonneg hγ_le_exp N
    have h_expN_le_expNx : (Real.exp x) ^ N ≤ Real.exp ((N : ℝ) * x) := by
      rw [h_exp_pow]
    have h_Nx_bound : (N : ℝ) * x ≤ (6 * (L : ℝ) + 2) * Real.log 2 := by
      rw [hx]
      have h := pb_cap_count d L hd3
      have hN_cast : (N : ℝ) = 2 * (d : ℝ) * ((d : ℝ) + 1) * (L : ℝ) + 1 := by
        dsimp [N]
        push_cast
        ring_nf
      rw [hN_cast]
      exact h
    have h_expNx_le_exp_bound : Real.exp ((N : ℝ) * x) ≤ Real.exp ((6 * (L : ℝ) + 2) * Real.log 2) :=
      Real.exp_le_exp.mpr h_Nx_bound
    have h_exp_bound_eq : Real.exp ((6 * (L : ℝ) + 2) * Real.log 2) = (2 : ℝ) ^ (6 * L + 2) := by
      calc
        Real.exp ((6 * (L : ℝ) + 2) * Real.log 2) = Real.exp (Real.log 2 * (6 * (L : ℝ) + 2)) := by ring
        _ = (2 : ℝ) ^ (6 * (L : ℝ) + 2) := by
          rw [Real.rpow_def_of_pos (by norm_num : 0 < (2 : ℝ))]
        _ = (2 : ℝ) ^ ((6 * L + 2 : ℕ) : ℝ) := by simp
        _ = (2 : ℝ) ^ (6 * L + 2 : ℕ) := by rw [Real.rpow_natCast]
    have h_exp_bound_le : Real.exp ((6 * (L : ℝ) + 2) * Real.log 2) ≤ (2 : ℝ) ^ (6 * L + 2) := by
      rw [h_exp_bound_eq]
    exact le_trans h_pow_le (le_trans h_γN_le_expN (le_trans h_expN_le_expNx (le_trans h_expNx_le_exp_bound h_exp_bound_le)))

end AdversarialBco.Bit.Aux_pb_cap_general

namespace AdversarialBco.Bit.Aux_pb_cap_lam


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius

theorem _root_.AdversarialBco.Bit.pb_cap_lam (d : ℕ) (hd : 1 ≤ d) :
    1 / (2 * (2 * (d : ℝ) + 1) ^ 2) ≤ Real.sqrt ((2 * (d : ℝ) + 1) ^ 2 / (4 * d * ((d : ℝ) + 1))) - 1 ∧
      1 / (10 * (d : ℝ) * ((d : ℝ) + 1)) ≤ 1 / (2 * (2 * (d : ℝ) + 1) ^ 2) := by
  have hd' : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hd_nonneg : 0 ≤ (d : ℝ) := by linarith
  set a := (2 * (d : ℝ) + 1) ^ 2 with ha_def
  set b := 4 * (d : ℝ) * ((d : ℝ) + 1) with hb_def
  have ha_pos : 0 < a := by
    dsimp [a]
    positivity
  have hb_pos : 0 < b := by
    dsimp [b]
    positivity
  have ha_eq_b_add_one : a = b + 1 := by
    dsimp [a, b]
    ring
  have h_first : 1 / (2 * a) ≤ Real.sqrt (a / b) - 1 := by
    have h_target : Real.sqrt (a / b) ≥ 1 + 1 / (2 * a) := by
      have h_sqrt_nonneg : 0 ≤ Real.sqrt (a / b) := Real.sqrt_nonneg _
      have h_sq_ineq : (1 + 1 / (2 * a)) ^ 2 ≤ (Real.sqrt (a / b)) ^ 2 := by
        rw [Real.sq_sqrt (by positivity : 0 ≤ a / b)]
        have h_diff_nonneg : 0 ≤ a / b - (1 + 1 / (2 * a)) ^ 2 := by
          rw [ha_eq_b_add_one]
          field_simp [ha_pos.ne.symm, hb_pos.ne.symm]
          ring_nf
          nlinarith
        linarith
      exact le_of_sq_le_sq h_sq_ineq h_sqrt_nonneg
    linarith
  have h_second : 1 / (10 * (d : ℝ) * ((d : ℝ) + 1)) ≤ 1 / (2 * (2 * (d : ℝ) + 1) ^ 2) := by
    have hpos1 : 0 < 10 * (d : ℝ) * ((d : ℝ) + 1) := by positivity
    have hpos2 : 0 < 2 * (2 * (d : ℝ) + 1) ^ 2 := by positivity
    have hineq : 2 * (2 * (d : ℝ) + 1) ^ 2 ≤ 10 * (d : ℝ) * ((d : ℝ) + 1) := by
      nlinarith
    exact ((one_div_le_one_div hpos1 hpos2).mpr hineq)
  exact And.intro h_first h_second

end AdversarialBco.Bit.Aux_pb_cap_lam

namespace AdversarialBco.Bit.Aux_pb_ell_count


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius

theorem _root_.AdversarialBco.Bit.pb_ell_count (d L : ℕ) (hd : 1 ≤ d) (R ρ : ℝ) (hρ : 0 < ρ) (hR0 : 0 < R)
    (hR : R / ρ ≤ 2 ^ L) :
    2 * d * Real.log (R / ρ) < 95 / (128 * ((d : ℝ) + 1)) * (2 * d * ((d : ℝ) + 1) * L + 1) := by
  have hpos : 0 < R / ρ := div_pos hR0 hρ
  have hlog_le : Real.log (R / ρ) ≤ Real.log ((2 : ℝ) ^ L) :=
    Real.log_le_log hpos hR
  have hlog_pow : Real.log ((2 : ℝ) ^ L) = (L : ℝ) * Real.log 2 := by
    rw [Real.log_pow]
  have hlog_le' : Real.log (R / ρ) ≤ (L : ℝ) * Real.log 2 := by
    linarith
  have hlog2_lt : 2 * Real.log 2 < 95/64 := by
    have h := Real.log_two_lt_d9
    linarith
  by_cases hL0 : (L : ℝ) = 0
  · -- L = 0: then R/ρ ≤ 1, so log(R/ρ) ≤ 0, LHS ≤ 0 < RHS
    have hL0' : L = 0 := by exact_mod_cast hL0
    subst hL0'
    have hR_le_one : R / ρ ≤ 1 := by simpa using hR
    have hlog_nonpos : Real.log (R / ρ) ≤ 0 :=
      Real.log_nonpos (by linarith) hR_le_one
    have hLHS_nonpos : 2 * (d : ℝ) * Real.log (R / ρ) ≤ 0 := by nlinarith
    have hRHS_pos : 0 < 95 / (128 * ((d : ℝ) + 1)) * (2 * (d : ℝ) * ((d : ℝ) + 1) * (0 : ℝ) + 1) := by
      positivity
    nlinarith
  · -- L > 0: then d*L > 0 and we can multiply inequalities
    have hL_pos : 0 < (L : ℝ) := by
      by_contra! h
      exact hL0 (by linarith)
    have hd_pos : 0 < (d : ℝ) := by exact_mod_cast (Nat.one_pos.trans_le hd)
    have h_dL_pos : 0 < (d : ℝ) * (L : ℝ) := mul_pos hd_pos hL_pos
    have h_mul : 2 * (d : ℝ) * Real.log (R / ρ) ≤ 2 * (d : ℝ) * ((L : ℝ) * Real.log 2) := by
      nlinarith
    have h_ineq : 2 * (d : ℝ) * ((L : ℝ) * Real.log 2) < (95/64) * (d : ℝ) * (L : ℝ) := by
      calc
        2 * (d : ℝ) * ((L : ℝ) * Real.log 2) = ((d : ℝ) * (L : ℝ)) * (2 * Real.log 2) := by ring
        _ < ((d : ℝ) * (L : ℝ)) * (95/64) := mul_lt_mul_of_pos_left hlog2_lt h_dL_pos
        _ = (95/64) * (d : ℝ) * (L : ℝ) := by ring
    have h_denom_ne_zero : 128 * ((d : ℝ) + 1) ≠ 0 := by positivity
    have hRHS_simp : 95 / (128 * ((d : ℝ) + 1)) * (2 * (d : ℝ) * ((d : ℝ) + 1) * (L : ℝ) + 1) =
        (95/64) * (d : ℝ) * (L : ℝ) + 95 / (128 * ((d : ℝ) + 1)) := by
      field_simp [h_denom_ne_zero]
      ring
    have h_extra_pos : 0 < 95 / (128 * ((d : ℝ) + 1)) := by
      positivity
    have h_final : (95/64) * (d : ℝ) * (L : ℝ) <
        95 / (128 * ((d : ℝ) + 1)) * (2 * (d : ℝ) * ((d : ℝ) + 1) * (L : ℝ) + 1) := by
      rw [hRHS_simp]
      nlinarith
    nlinarith

end AdversarialBco.Bit.Aux_pb_ell_count

namespace AdversarialBco.Bit.Aux_pb_ell_det_contra


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius

theorem _root_.AdversarialBco.Bit.pb_ell_det_contra (d L : ℕ) (hd : 1 ≤ d) (R ρ D : ℝ) (hρ : 0 < ρ) (hR0 : 0 < R)
    (hR : R / ρ ≤ 2 ^ L)
    (hD : D ≤ R ^ (2 * d) * Real.exp (-(95 / (128 * ((d : ℝ) + 1)) * (2 * d * ((d : ℝ) + 1) * L + 1)))) :
    D < ρ ^ (2 * d) := by
  set W := 95 / (128 * ((d : ℝ) + 1)) * (2 * d * ((d : ℝ) + 1) * L + 1) with hW
  have hposR_pow : 0 < R ^ (2 * d) := pow_pos hR0 _
  have hposρ_pow : 0 < ρ ^ (2 * d) := pow_pos hρ _
  have hpos_exp : 0 < Real.exp (-W) := Real.exp_pos _
  have hpos_prod : 0 < R ^ (2 * d) * Real.exp (-W) := mul_pos hposR_pow hpos_exp
  have h_log_ineq : 2 * (d : ℝ) * Real.log (R / ρ) < W := by
    have h := pb_ell_count d L hd R ρ hρ hR0 hR
    simpa [hW] using h
  have h_main : R ^ (2 * d) * Real.exp (-W) < ρ ^ (2 * d) := by
    have h_log_lt : Real.log (R ^ (2 * d) * Real.exp (-W)) < Real.log (ρ ^ (2 * d)) := by
      calc
        Real.log (R ^ (2 * d) * Real.exp (-W)) = Real.log (R ^ (2 * d)) + Real.log (Real.exp (-W)) := by
          refine Real.log_mul (ne_of_gt hposR_pow) (ne_of_gt hpos_exp)
        _ = Real.log (R ^ (2 * d)) + (-W) := by simp
        _ = ((2 * d : ℕ) : ℝ) * Real.log R + (-W) := by simp [Real.log_pow]
        _ = (2 * (d : ℝ)) * Real.log R + (-W) := by push_cast; ring
        _ < (2 * (d : ℝ)) * Real.log ρ := by
          have hlogdiv : Real.log (R / ρ) = Real.log R - Real.log ρ :=
            Real.log_div (ne_of_gt hR0) (ne_of_gt hρ)
          have htemp := h_log_ineq
          rw [hlogdiv] at htemp
          linarith
        _ = Real.log (ρ ^ (2 * d)) := by simp [Real.log_pow]
    exact (Real.log_lt_log_iff hpos_prod hposρ_pow).mp h_log_lt
  linarith

end AdversarialBco.Bit.Aux_pb_ell_det_contra

namespace AdversarialBco.Bit.Aux_pb_cc_incl


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius

theorem _root_.AdversarialBco.Bit.pb_cc_incl {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) (a c x : Fin n → ℝ)
    (ha : a ≠ 0) (d : ℕ) (hd : 2 ≤ d) (hx : (x - c) ⬝ᵥ (A⁻¹ *ᵥ (x - c)) ≤ 1) (hcut : a ⬝ᵥ (x - c) ≤ 0) :
    (x - (c - (1 / ((d : ℝ) + 1) / Real.sqrt (a ⬝ᵥ (A *ᵥ a))) • (A *ᵥ a))) ⬝ᵥ
        ((((d : ℝ) ^ 2 / ((d : ℝ) ^ 2 - 1)) • (A - (2 / ((d : ℝ) + 1) / (a ⬝ᵥ (A *ᵥ a))) •
          vecMulVec (A *ᵥ a) (A *ᵥ a)))⁻¹ *ᵥ
          (x - (c - (1 / ((d : ℝ) + 1) / Real.sqrt (a ⬝ᵥ (A *ᵥ a))) • (A *ᵥ a)))) ≤ 1 := by
  have hd_real : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hβ0 : (0 : ℝ) ≤ (0 : ℝ) := le_refl _
  have hβd : (d : ℝ) * (0 : ℝ) < 1 := by
    calc
      (d : ℝ) * (0 : ℝ) = (0 : ℝ) := by ring
      _ < 1 := by norm_num
  have hcut' : a ⬝ᵥ (x - c) ≤ (0 : ℝ) * Real.sqrt (a ⬝ᵥ (A *ᵥ a)) := by
    simpa [zero_mul] using hcut
  apply sc_incl A hA a c x ha (d : ℝ) (0 : ℝ) (1 / ((d : ℝ) + 1)) ((d : ℝ) ^ 2 / ((d : ℝ) ^ 2 - 1))
    (2 / ((d : ℝ) + 1)) hd_real hβ0 hβd ?_ ?_ ?_ hx hcut'
  · ring
  · ring
  · ring

end AdversarialBco.Bit.Aux_pb_cc_incl

namespace AdversarialBco.Bit.Aux_pb_cc_posDef


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius

theorem _root_.AdversarialBco.Bit.pb_cc_posDef {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) (a : Fin n → ℝ)
    (ha : a ≠ 0) (d : ℕ) (hd : 2 ≤ d) :
    (((d : ℝ) ^ 2 / ((d : ℝ) ^ 2 - 1)) • (A - (2 / ((d : ℝ) + 1) / (a ⬝ᵥ (A *ᵥ a))) •
      vecMulVec (A *ᵥ a) (A *ᵥ a))).PosDef := by
  set σ := (d : ℝ) ^ 2 / ((d : ℝ) ^ 2 - 1) with hσ_def
  set τ := 2 / ((d : ℝ) + 1) with hτ_def
  have hσ_pos : 0 < σ := by
    rw [hσ_def]
    have hd_sq_pos : 0 < (d : ℝ) ^ 2 := by
      have hd_pos : 0 < (d : ℝ) := by exact_mod_cast (Nat.one_le_of_lt (Nat.lt_of_lt_of_le (by norm_num : 1 < 2) hd))
      positivity
    have h_denom_pos : 0 < (d : ℝ) ^ 2 - 1 := by
      have hd_sq_ge_4 : (4 : ℝ) ≤ (d : ℝ) ^ 2 := by
        have hd' : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
        nlinarith
      nlinarith
    positivity
  have hτ_lt_one : τ < 1 := by
    rw [hτ_def]
    have hd_pos : 0 < (d : ℝ) + 1 := by
      have : 0 < (d : ℕ) := Nat.one_le_of_lt (Nat.lt_of_lt_of_le (by norm_num : 1 < 2) hd)
      have hd' : (0 : ℝ) < (d : ℝ) := by exact_mod_cast this
      linarith
    apply (div_lt_one hd_pos).mpr
    have hd' : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  -- Note: the inner expression is A - (τ / c) • vecMulVec (A*ᵥa) (A*ᵥa) where c = a ⬝ᵥ (A*ᵥa)
  -- But τ is defined as 2/(d+1), and we need τ / (a ⬝ᵥ (A *ᵥ a))
  -- The target has: (2 / ((d : ℝ) + 1) / (a ⬝ᵥ (A *ᵥ a)))
  -- This equals τ / (a ⬝ᵥ (A *ᵥ a))
  have hτ_div : (2 / ((d : ℝ) + 1) / (a ⬝ᵥ (A *ᵥ a))) = τ / (a ⬝ᵥ (A *ᵥ a)) := by
    rw [hτ_def]
  rw [hσ_def, hτ_div]
  exact sc_posDef A hA a ha σ τ hσ_pos hτ_lt_one

end AdversarialBco.Bit.Aux_pb_cc_posDef
