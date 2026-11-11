/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.Df2SIFactsSurr
public import AdversarialBco.Poly.Df2SIFactsArith

@[expose] public section

/-!
# prop:s-sc and prop:lower on the generic surrogate

For `e` convex and `K`-Lipschitz with `K = 8/ε`, `A S` inverse to each other with `|v| ≤ (2σ²)^{1/2} |S v|`, and the
facts of the parameters:
* `core_x4` (X4, prop:s-sc in the quadratic form): `λ² |S(x - y)|² ≤ 1/L` gives
  `s''(x)(v, v) ≤ 2 s''(y)(v, v) + δ |S v|²`, from `surr_sc` and the tail of the shift;
* `core_x3` (X3, prop:lower): `E e(μ + A g) - s(μ) ≤ (2/λ) E s''(μ)(A g, A g) + 2 δ d/λ`, from `surr_mean` at
  `ρ² = (2 - λ)/λ`, Taylor at `μ` with `core_x4` near `μ` and the bound of `s''` off it.
-/

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal

namespace AdversarialBco.Poly.SIF

variable {d : ℕ}

/-- The second derivative of a convex `C²` function is nonnegative on the diagonal. -/
theorem hess_nonneg (f : EuclideanSpace ℝ (Fin d) → ℝ) (hf : ContDiff ℝ 2 f) (hc : ConvexOn ℝ Set.univ f)
    (z v : EuclideanSpace ℝ (Fin d)) : 0 ≤ fderiv ℝ (fderiv ℝ f) z v v := by
  have h := (Layer2.gradM_hessM f z (WithLp.ofLp v)).2
  rw [WithLp.toLp_ofLp] at h
  rw [← h]
  exact Layer2.sq_nonneg_of_psd (Layer2.hess_psd f hf hc z) _

/-- `‖g‖²` is integrable under the standard Gaussian. -/
theorem integrable_norm_sq :
    Integrable (fun g : EuclideanSpace ℝ (Fin d) => ‖g‖ ^ 2) (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
  (IsGaussian.memLp_two_id (μ := stdGaussian (EuclideanSpace ℝ (Fin d)))).integrable_norm_pow' (p := 2)

/-- `E ‖g‖² = d`. -/
theorem integral_norm_sq :
    ∫ g : EuclideanSpace ℝ (Fin d), ‖g‖ ^ 2 ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) = d := by
  have h := integral_sq_mulVec (d := d) 1 1
  simp only [Matrix.one_mulVec, Matrix.transpose_one, Matrix.one_mul, Matrix.trace_one, Fintype.card_fin,
    Layer2.sq_one] at h
  rw [← h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  show ‖g‖ ^ 2 = _
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Real.norm_eq_abs, sq_abs, dotProduct]
  simp only [pow_two]

/-- The tail of the shift: `‖c‖² L ≤ 21/10` gives `P(log 2 - ‖c‖²/2 < ⟪c, g⟫) ≤ δ³/2` at `L = 36 log(1/δ)`. -/
theorem shift_prob (c : EuclideanSpace ℝ (Fin d)) (L de : ℝ) (hL : 504 ≤ L) (hLde : L = 36 * Real.log (1 / de))
    (hd0 : 0 < de) (hd1 : de ≤ 1) (hc : ‖c‖ ^ 2 * L ≤ 21 / 10) :
    (stdGaussian (EuclideanSpace ℝ (Fin d))).real {g | Real.log 2 - ‖c‖ ^ 2 / 2 < ⟪c, g⟫} ≤ de ^ 3 / 2 := by
  rcases eq_or_lt_of_le (sq_nonneg ‖c‖) with h | h
  · have hc0 : c = 0 := by
      have : ‖c‖ = 0 := by nlinarith [norm_nonneg c]
      exact norm_eq_zero.mp this
    have hempty : {g : EuclideanSpace ℝ (Fin d) | Real.log 2 - ‖c‖ ^ 2 / 2 < ⟪c, g⟫} = ∅ := by
      ext g
      simp only [hc0, norm_zero, inner_zero_left, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
      have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
      norm_num
      linarith
    rw [hempty, measureReal_empty]
    positivity
  · obtain ⟨hb0, hbL⟩ := tail_exponent_arith L (‖c‖ ^ 2) hL h hc
    have ht := inner_tail c (Real.log 2 - ‖c‖ ^ 2 / 2) hb0
    have he := exp_Le_arith de L hd0 hd1 hLde
    calc _ ≤ Real.exp (-((Real.log 2 - ‖c‖ ^ 2 / 2) ^ 2 / (2 * ‖c‖ ^ 2))) / 2 := ht
      _ ≤ Real.exp (-(L / 10)) / 2 := by gcongr
      _ ≤ de ^ 3 / 2 := by gcongr

/-- X4 in the quadratic form. -/
theorem core_x4 (e : EuclideanSpace ℝ (Fin d) → ℝ) (K : ℝ≥0) (he : LipschitzWith K e)
    (hc : ConvexOn ℝ Set.univ e) (μ : EuclideanSpace ℝ (Fin d))
    (A S : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) (hAS : ∀ x, A (S x) = x)
    (lam σ2 L de n eps : ℝ) (hK : (K : ℝ) = 8 / eps) (h0 : 0 < lam) (hl : lam ≤ 1 / 100) (hσ0 : 0 ≤ σ2)
    (hσ : σ2 ≤ 1 / 4) (hnorm : ∀ v, ‖v‖ ≤ Real.sqrt (2 * σ2) * ‖S v‖) (hL : 504 ≤ L)
    (hLde : L = 36 * Real.log (1 / de)) (hd0 : 0 < de) (hd4 : 4 * de ≤ 1) (heps : 0 < eps) (hen : 1 / eps ≤ n)
    (hnd : n * de ≤ 1) (x y : EuclideanSpace ℝ (Fin d)) (hxy : lam ^ 2 * ‖S (x - y)‖ ^ 2 ≤ 1 / L)
    (v : EuclideanSpace ℝ (Fin d)) :
    fderiv ℝ (fderiv ℝ (df2Surr e μ A lam)) x v v ≤
      2 * fderiv ℝ (fderiv ℝ (df2Surr e μ A lam)) y v v + de * ‖S v‖ ^ 2 := by
  have h1 : lam < 1 := by linarith
  have hsc := surr_sc e K he hc μ A S hAS lam h0 h1 x y v
  have hL0 : 0 < L := by linarith
  have hcn : ‖(lam / ((1 - lam) * Real.sqrt (1 / 2))) • S (x - y)‖ ^ 2 * L ≤ 21 / 10 := by
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, div_pow, mul_pow,
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    have hN : lam ^ 2 * ‖S (x - y)‖ ^ 2 * L ≤ 1 := by
      rw [le_div_iff₀ hL0] at hxy; linarith
    have h1l : (99 / 100 : ℝ) ≤ 1 - lam := by linarith
    have key : lam ^ 2 / ((1 - lam) ^ 2 * (1 / 2)) * ‖S (x - y)‖ ^ 2 * L =
        2 * (lam ^ 2 * ‖S (x - y)‖ ^ 2 * L) / (1 - lam) ^ 2 := by
      field_simp
    rw [key, div_le_iff₀ (by positivity)]
    nlinarith
  have hq := shift_prob _ L de hL hLde hd0 (by linarith) hcn
  have hq0 := measureReal_nonneg (μ := stdGaussian (EuclideanSpace ℝ (Fin d)))
    (s := {g | Real.log 2 - ‖(lam / ((1 - lam) * Real.sqrt (1 / 2))) • S (x - y)‖ ^ 2 / 2 <
      ⟪(lam / ((1 - lam) * Real.sqrt (1 / 2))) • S (x - y), g⟫})
  have hconst := x4_const_arith lam eps σ2 de n ‖v‖ ‖S v‖ _ h0 (by linarith) heps hen hnd hd0 hd4 hσ0 hσ
    (norm_nonneg _) (hnorm v) (norm_nonneg _) hq0 hq
  rw [hK] at hsc
  linarith

set_option maxHeartbeats 1000000 in
/-- X3 on the generic surrogate. -/
theorem core_x3 (hd : 1 ≤ d) (e : EuclideanSpace ℝ (Fin d) → ℝ) (K : ℝ≥0) (he : LipschitzWith K e)
    (hc : ConvexOn ℝ Set.univ e) (μ : EuclideanSpace ℝ (Fin d))
    (A S : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) (hAS : ∀ x, A (S x) = x)
    (hSA : ∀ x, S (A x) = x) (lam σ2 L de n eps : ℝ) (hK : (K : ℝ) = 8 / eps)
    (hlam : lam = 1 / (725 * d * L ^ 2)) (hσ : σ2 = 1 / (8 * L))
    (hnorm : ∀ v, ‖v‖ ≤ Real.sqrt (2 * σ2) * ‖S v‖) (hL : 504 ≤ L) (hLde : L = 36 * Real.log (1 / de))
    (hd0 : 0 < de) (hd128 : 128 * de ≤ 1) (heps : 0 < eps) (hen : 1 / eps ≤ n) (hnd : n * de ≤ 1) :
    ∫ g, e (μ + A g) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) - df2Surr e μ A lam μ ≤
      2 / lam * ∫ g, fderiv ℝ (fderiv ℝ (df2Surr e μ A lam)) μ (A g) (A g)
          ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) + 2 * de * d / lam := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hL0 : 0 < L := by linarith
  have h0 : 0 < lam := by rw [hlam]; positivity
  have hl : lam ≤ 1 / 100 := by
    rw [hlam, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have h1 : lam < 1 := by linarith
  have h1l : 0 < 1 - lam := by linarith
  have hσ0 : 0 ≤ σ2 := by rw [hσ]; positivity
  have hσ4 : σ2 ≤ 1 / 4 := by rw [hσ, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hd4 : 4 * de ≤ 1 := by linarith
  have hde1 : de ≤ 1 := by linarith
  set s := df2Surr e μ A lam with hs
  have hs2 : ContDiff ℝ 2 s := surr_contDiff e K he μ A S hAS hSA lam h0 h1
  set ρ2 : ℝ := (2 - lam) / lam with hρ2
  have hρ20 : 0 < ρ2 := by rw [hρ2]; apply div_pos <;> linarith
  set ρ := Real.sqrt ρ2 with hρ
  have hρsq : ρ ^ 2 = ρ2 := Real.sq_sqrt hρ20.le
  have hρ1 : (1 - lam) ^ 2 + lam ^ 2 * ρ ^ 2 = 1 := by rw [hρsq, hρ2]; field_simp; ring
  have hmean := surr_mean e K he μ A lam ρ h0 h1 (Real.sqrt_nonneg _) hρ1
  set M : ℝ := lam * K * Real.sqrt (2 * σ2) / (1 - lam) with hM
  have hM0 : 0 ≤ M := by rw [hM]; exact div_nonneg (by positivity) h1l.le
  set T : ℝ := 1 / (L * lam ^ 2 * ρ2) with hT
  set H := fderiv ℝ (fderiv ℝ s) μ with hH
  set Q : EuclideanSpace ℝ (Fin d) → ℝ := fun g => H (A g) (A g) with hQ
  have hQ0 : ∀ g, 0 ≤ Q g := fun g => hess_nonneg s hs2 (surr_convex e K he hc μ A lam h0) μ (A g)
  set D := (fderiv ℝ s μ).comp (ρ • A) with hD
  set B : Set (EuclideanSpace ℝ (Fin d)) := {g | T < ‖g‖ ^ 2} with hB
  -- the pointwise bound
  have hpt : ∀ g, s (μ + ρ • A g) ≤ s μ + D g + ρ2 * Q g + de / 2 * ρ2 * ‖g‖ ^ 2 +
      M / 2 * ρ2 * B.indicator (fun g => ‖g‖ ^ 2) g := by
    intro g
    set v := ρ • A g with hv
    have hSv : ‖S v‖ ^ 2 = ρ2 * ‖g‖ ^ 2 := by
      rw [hv, map_smul, hSA, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, hρsq]
    have hHv : H v v = ρ2 * Q g := by
      rw [hv, ← hρsq]; simp only [map_smul, smul_apply, smul_eq_mul, hQ]; ring
    have hDv : fderiv ℝ s μ v = D g := by
      simp only [hD, hv, ContinuousLinearMap.comp_apply, smul_apply]
    by_cases hTg : T < ‖g‖ ^ 2
    · rw [Set.indicator_of_mem (show g ∈ B from hTg)]
      have hbd : ∀ t ∈ Set.Icc (0 : ℝ) 1, fderiv ℝ (fderiv ℝ s) (μ + t • v) v v ≤ M * ‖S v‖ ^ 2 := by
        intro t _
        have hb := surr_hess_bound e K he hc μ A S hAS hSA lam h0 h1 (μ + t • v) v v
        have hc0 : 0 ≤ lam * K / (1 - lam) := div_nonneg (by positivity) h1l.le
        calc _ ≤ |fderiv ℝ (fderiv ℝ s) (μ + t • v) v v| := le_abs_self _
          _ ≤ lam * K / (1 - lam) * (‖v‖ * ‖S v‖) := hb
          _ ≤ lam * K / (1 - lam) * (Real.sqrt (2 * σ2) * ‖S v‖ * ‖S v‖) := by
              gcongr; exact hnorm v
          _ = M * ‖S v‖ ^ 2 := by rw [hM]; ring
      have ht := Layer2.taylor_upper s hs2 μ v _ hbd
      rw [hDv, hSv] at ht
      have := hQ0 g
      have : 0 ≤ ‖g‖ ^ 2 := sq_nonneg _
      have : 0 ≤ de / 2 * ρ2 * ‖g‖ ^ 2 := by positivity
      have : 0 ≤ ρ2 * Q g := mul_nonneg hρ20.le (hQ0 g)
      nlinarith
    · rw [Set.indicator_of_notMem (show g ∉ B from hTg)]
      have hTg' : lam ^ 2 * ‖S v‖ ^ 2 ≤ 1 / L := by
        replace hTg := not_lt.mp hTg
        rw [hT, le_div_iff₀ (by positivity)] at hTg
        rw [hSv, le_div_iff₀ hL0]
        calc lam ^ 2 * (ρ2 * ‖g‖ ^ 2) * L = ‖g‖ ^ 2 * (L * lam ^ 2 * ρ2) := by ring
          _ ≤ 1 := hTg
      have hbd : ∀ t ∈ Set.Icc (0 : ℝ) 1,
          fderiv ℝ (fderiv ℝ s) (μ + t • v) v v ≤ 2 * H v v + de * ‖S v‖ ^ 2 := by
        intro t ht
        have hx : lam ^ 2 * ‖S ((μ + t • v) - μ)‖ ^ 2 ≤ 1 / L := by
          rw [add_sub_cancel_left, map_smul, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
          have ht2 : t ^ 2 ≤ 1 := by nlinarith [ht.1, ht.2]
          calc lam ^ 2 * (t ^ 2 * ‖S v‖ ^ 2) ≤ lam ^ 2 * (1 * ‖S v‖ ^ 2) := by gcongr
            _ = lam ^ 2 * ‖S v‖ ^ 2 := by ring
            _ ≤ 1 / L := hTg'
        exact core_x4 e K he hc μ A S hAS lam σ2 L de n eps hK h0 hl hσ0 hσ4 hnorm hL hLde hd0 hd4 heps hen hnd
          _ _ hx v
      have ht := Layer2.taylor_upper s hs2 μ v _ hbd
      rw [hDv, hHv, hSv] at ht
      linarith
  -- integrability
  have iL : Integrable (fun g => s (μ + ρ • A g)) (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    have := integrable_comp_affine s K (surr_lipschitzWith e K he μ A lam h0) μ (ρ • A)
    simpa only [smul_apply] using this
  have iD : Integrable (fun g => D g) (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
    D.integrable_comp IsGaussian.integrable_id
  have iQ : Integrable Q (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    refine Integrable.mono' (integrable_norm_sq.const_mul (‖H‖ * ‖A‖ ^ 2)) ?_ (Filter.Eventually.of_forall fun g => ?_)
    · exact ((H.continuous.comp A.continuous).clm_apply A.continuous).aestronglyMeasurable
    · have hAg : ‖A g‖ ≤ ‖A‖ * ‖g‖ := A.le_opNorm g
      have hH0 := norm_nonneg H
      have hAg0 := norm_nonneg (A g)
      calc ‖Q g‖ ≤ ‖H‖ * ‖A g‖ * ‖A g‖ := H.le_opNorm₂ (A g) (A g)
        _ ≤ ‖H‖ * (‖A‖ * ‖g‖) * (‖A‖ * ‖g‖) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hAg hH0) hAg hAg0 (by positivity)
        _ = ‖H‖ * ‖A‖ ^ 2 * ‖g‖ ^ 2 := by ring
  have iN := integrable_norm_sq (d := d)
  have hBm : MeasurableSet B := measurableSet_lt measurable_const (continuous_norm.pow 2).measurable
  have iI : Integrable (B.indicator fun g => ‖g‖ ^ 2) (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
    iN.indicator hBm
  have i1 : Integrable (fun g => s μ + D g) (stdGaussian (EuclideanSpace ℝ (Fin d))) := (integrable_const _).add iD
  have i2 : Integrable (fun g => s μ + D g + ρ2 * Q g) (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
    i1.add (iQ.const_mul _)
  have i3 : Integrable (fun g => s μ + D g + ρ2 * Q g + de / 2 * ρ2 * ‖g‖ ^ 2)
      (stdGaussian (EuclideanSpace ℝ (Fin d))) := i2.add (iN.const_mul _)
  have i4 : Integrable (fun g => s μ + D g + ρ2 * Q g + de / 2 * ρ2 * ‖g‖ ^ 2 +
      M / 2 * ρ2 * B.indicator (fun g => ‖g‖ ^ 2) g) (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
    i3.add (iI.const_mul _)
  have hmono := integral_mono iL i4 hpt
  rw [hmean, integral_add i3 (iI.const_mul _), integral_add i2 (iN.const_mul _), integral_add i1 (iQ.const_mul _),
    integral_add (integrable_const _) iD, integral_const, integral_const_mul, integral_const_mul, integral_const_mul,
    integral_norm_sq, integral_strongDual_stdGaussian D] at hmono
  simp only [probReal_univ, smul_eq_mul, one_mul, add_zero] at hmono
  -- the constants
  have htail := norm_sq_tail_integral (d := d) T
  have hIQ : 0 ≤ ∫ g, Q g ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := integral_nonneg hQ0
  have harith := x3_tail_arith d hd L lam eps σ2 de n hL hlam hσ heps hen hnd hd0 hd128 hLde
  rw [← hK] at harith
  have hρle : ρ2 ≤ 2 / lam := by rw [hρ2]; exact div_le_div_of_nonneg_right (by linarith) h0.le
  have e1 : ρ2 * ∫ g, Q g ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) ≤
      2 / lam * ∫ g, Q g ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := mul_le_mul_of_nonneg_right hρle hIQ
  have e2 : de / 2 * ρ2 * d ≤ de * d / lam := by
    calc de / 2 * ρ2 * d ≤ de / 2 * (2 / lam) * d :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hρle (by positivity)) (by positivity)
      _ = de * d / lam := by field_simp
  have e3 : M / 2 * ρ2 * ∫ g, B.indicator (fun g => ‖g‖ ^ 2) g ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) ≤
      de * d / lam := by
    calc _ ≤ M / 2 * ρ2 * (8 * Real.sqrt 2 ^ d * Real.exp (-(T / 8))) :=
          mul_le_mul_of_nonneg_left htail (by positivity)
      _ ≤ de * d / lam := by rw [hM, hT]; exact harith
  have hQeq : ∫ g, Q g ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) =
      ∫ g, fderiv ℝ (fderiv ℝ (df2Surr e μ A lam)) μ (A g) (A g) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := rfl
  have e4 : de * d / lam + de * d / lam = 2 * de * d / lam := by ring
  rw [← hQeq]
  linarith

end AdversarialBco.Poly.SIF
