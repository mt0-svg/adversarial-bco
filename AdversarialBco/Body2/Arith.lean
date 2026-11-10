/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Body2.Gauss1

@[expose] public section

/-!
# Real arithmetic of Theorem 3.1 and Proposition 2.2

The closing inequalities with explicit constants: the square of a sum (Proposition 3.5), the depth of the diluted law
(Proposition 2.2), the scale bound and the closing step of Theorem 3.1, and the steps of the proof of Proposition 2.2 (the bound on
`s_h`, the bound on `ι`, the mass outside `J`, the projection of the variance, the final bound).
-/

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal

section

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal

theorem AdversarialBco.Body2.core_sq_arith (ℓ P Q X Y α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (hℓ : 0 ≤ ℓ) (h : ℓ ≤ P + Q) (hP : P ^ 2 ≤ α * X) (hQ : Q ^ 2 ≤ β * Y) : ℓ ^ 2 ≤ (α + β) * (X + Y) := by
  have hsq : ℓ ^ 2 ≤ (P + Q) ^ 2 := by
    nlinarith
  have hpos : 0 < α * β := mul_pos hα hβ
  have h_cs : (P + Q) ^ 2 * (α * β) ≤ (α + β) * (β * P ^ 2 + α * Q ^ 2) := by
    have h_nonneg_sq : (α * Q - β * P) ^ 2 ≥ 0 := sq_nonneg _
    nlinarith
  have h_bound : β * P ^ 2 + α * Q ^ 2 ≤ α * β * (X + Y) := by
    nlinarith
  have h_main : (P + Q) ^ 2 ≤ (α + β) * (X + Y) := by
    have htemp : (P + Q) ^ 2 * (α * β) ≤ (α + β) * (X + Y) * (α * β) := by
      nlinarith
    exact le_of_mul_le_mul_right htemp hpos
  nlinarith
end

section

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal

theorem AdversarialBco.Body2.delta_arith (Fs Fb EF m h d : ℝ) (hd : 1 ≤ d) (hh : 0 < h) (hΔ : 0 < Fs - m) (hΔh : (Fs - m) / 2 ≤ h) (hmin : Fs ≤ Fb) (hS4 : Fb ≤ EF) (hS3 : EF ≤ Fs + h / (16 * d) * d) : 0 ≤ (1 - (Fs - m) / (4 * h)) * Fs + (Fs - m) / (4 * h) / 2 * Fb + (Fs - m) / (4 * h) / 2 * EF - m ∧ (1 - (Fs - m) / (4 * h)) * Fs + (Fs - m) / (4 * h) / 2 * Fb + (Fs - m) / (4 * h) / 2 * EF - m ≤ 65 / 64 * (Fs - m) := by
  set Δ := Fs - m with hΔdef
  have hΔpos : 0 < Δ := hΔ
  have hdpos : 0 < d := by linarith
  have hS3' : EF ≤ Fs + h / 16 := by
    have htemp : h / (16 * d) * d = h / 16 := by
      field_simp [hdpos.ne.symm]
    linarith
  have hq_nonneg : 0 ≤ (Δ / (4 * h)) / 2 := by
    have hdiv : 0 ≤ Δ / (4 * h) := div_nonneg (by linarith) (by linarith)
    nlinarith
  have h_expr_eq : (1 - (Fs - m) / (4 * h)) * Fs + (Fs - m) / (4 * h) / 2 * Fb + (Fs - m) / (4 * h) / 2 * EF - m = Δ + (Δ / (4 * h)) / 2 * (Fb - Fs) + (Δ / (4 * h)) / 2 * (EF - Fs) := by
    dsimp [Δ]
    ring
  rw [h_expr_eq]
  have h_lower : 0 ≤ Δ + (Δ / (4 * h)) / 2 * (Fb - Fs) + (Δ / (4 * h)) / 2 * (EF - Fs) := by
    have h1 : 0 ≤ Fb - Fs := by linarith
    have h2 : 0 ≤ EF - Fs := by linarith
    nlinarith
  have h_upper : Δ + (Δ / (4 * h)) / 2 * (Fb - Fs) + (Δ / (4 * h)) / 2 * (EF - Fs) ≤ 65 / 64 * Δ := by
    have hFb_le : Fb - Fs ≤ h / 16 := by linarith
    have hEF_le : EF - Fs ≤ h / 16 := by linarith
    have hq_bound_eq : (Δ / (4 * h)) / 2 * (h / 16) + (Δ / (4 * h)) / 2 * (h / 16) = Δ / 64 := by
      field_simp [hh.ne.symm]
      ring
    nlinarith
  exact And.intro h_lower h_upper
end

section

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal

theorem AdversarialBco.Body2.scale_arith2 (Λ μg μm h d T VG Vg Vb Vbg Vs : ℝ) (hΛ : Λ ≤ μg + μm) (hμg : 0 ≤ μg) (hμm : 0 ≤ μm) (hh : 0 < h) (hd : 1 ≤ d) (hT : 0 ≤ T) (hVg : 0 ≤ Vg) (hVbg : 0 ≤ Vbg) (hVs : 0 ≤ Vs) (hVgG : Vg ≤ VG) (hVbgb : Vbg ≤ Vb) (hcore : μg * (AdversarialBco.BodySpec.kappa / 32 * h / ((1 + T) * d)) ^ 2 ≤ (3 + 2 * AdversarialBco.BodySpec.kappa2 + 1 / (4 * d)) * (Vg + Vbg)) (hmoved : μm * h ^ 2 / 8 ≤ Vb + Vs) : Λ * h ^ 2 ≤ AdversarialBco.BodySpec.KS * (1 + T) ^ 2 * d ^ 2 * (VG + Vb + Vs) := by
  rcases AdversarialBco.Body2.kappa_bounds with ⟨hκ_low, hκ_high, hκ2_low, hκ2_high⟩
  have hκ_pos : 0 < AdversarialBco.BodySpec.kappa := by linarith
  have hκ2_nonneg : 0 ≤ AdversarialBco.BodySpec.kappa2 := by linarith
  have hd_pos : 0 < d := by linarith
  have hT1_pos : 0 < 1 + T := by linarith
  have hT1_nonneg : 0 ≤ 1 + T := by linarith
  have hT1_sq_ge_one : 1 ≤ (1 + T) ^ 2 := by
    have : 1 + T ≥ 1 := by linarith
    nlinarith
  have hd_sq_ge_one : 1 ≤ d ^ 2 := by
    nlinarith
  have hX_ge_8 : 8 ≤ (32 / AdversarialBco.BodySpec.kappa) ^ 2 * (13 / 4 + 2 * AdversarialBco.BodySpec.kappa2) * (1 + T) ^ 2 * d ^ 2 := by
    have h_denom_pos : 0 < (319 : ℝ) / 1000 := by norm_num
    have h_one_div_ge : 1 / (319 / 1000 : ℝ) ≤ 1 / AdversarialBco.BodySpec.kappa :=
      (one_div_le_one_div h_denom_pos hκ_pos).mpr hκ_high
    have h_div_sq_ge : (32 / (319 / 1000 : ℝ)) ^ 2 ≤ (32 / AdversarialBco.BodySpec.kappa) ^ 2 := by
      have h_div_ge : (32 : ℝ) / (319 / 1000) ≤ (32 : ℝ) / AdversarialBco.BodySpec.kappa := by
        have h32_nonneg : 0 ≤ (32 : ℝ) := by norm_num
        calc
          (32 : ℝ) / (319 / 1000) = (32 : ℝ) * (1 / (319 / 1000)) := by ring
          _ ≤ (32 : ℝ) * (1 / AdversarialBco.BodySpec.kappa) := mul_le_mul_of_nonneg_left h_one_div_ge h32_nonneg
          _ = (32 : ℝ) / AdversarialBco.BodySpec.kappa := by ring
      nlinarith
    have h_kappa2_term_ge : (4442 : ℝ) / 1000 ≤ 13 / 4 + 2 * AdversarialBco.BodySpec.kappa2 := by
      have h : 2 * (596 / 1000 : ℝ) ≤ 2 * AdversarialBco.BodySpec.kappa2 := mul_le_mul_of_nonneg_left hκ2_low (by norm_num)
      linarith
    have h_inner : (32 / (319 / 1000 : ℝ)) ^ 2 * (4442 / 1000 : ℝ) ≤
        (32 / AdversarialBco.BodySpec.kappa) ^ 2 * (13 / 4 + 2 * AdversarialBco.BodySpec.kappa2) := by
      refine mul_le_mul h_div_sq_ge h_kappa2_term_ge (by norm_num) ?_
      apply pow_two_nonneg
    have h_mid : (32 / (319 / 1000 : ℝ)) ^ 2 * (4442 / 1000 : ℝ) * 1 ≤
        (32 / AdversarialBco.BodySpec.kappa) ^ 2 * (13 / 4 + 2 * AdversarialBco.BodySpec.kappa2) * (1 + T) ^ 2 := by
      refine mul_le_mul h_inner hT1_sq_ge_one (by norm_num) ?_
      have hpos : 0 ≤ (32 / (319 / 1000 : ℝ)) ^ 2 * (4442 / 1000 : ℝ) := by
        apply mul_nonneg
        · apply pow_two_nonneg
        · norm_num
      have hpos2 : 0 ≤ (32 / AdversarialBco.BodySpec.kappa) ^ 2 * (13 / 4 + 2 * AdversarialBco.BodySpec.kappa2) := by
        apply mul_nonneg
        · apply pow_two_nonneg
        · linarith
      exact hpos2
    have h_prod_ge : (32 / (319 / 1000 : ℝ)) ^ 2 * (4442 / 1000 : ℝ) * 1 * 1 ≤
        (32 / AdversarialBco.BodySpec.kappa) ^ 2 * (13 / 4 + 2 * AdversarialBco.BodySpec.kappa2) * (1 + T) ^ 2 * d ^ 2 := by
      refine mul_le_mul h_mid hd_sq_ge_one (by norm_num) ?_
      have hpos : 0 ≤ (32 / (319 / 1000 : ℝ)) ^ 2 * (4442 / 1000 : ℝ) * 1 := by
        apply mul_nonneg
        · apply mul_nonneg; apply pow_two_nonneg; norm_num
        · norm_num
      have hpos2 : 0 ≤ (32 / AdversarialBco.BodySpec.kappa) ^ 2 * (13 / 4 + 2 * AdversarialBco.BodySpec.kappa2) * (1 + T) ^ 2 := by
        apply mul_nonneg
        · apply mul_nonneg; apply pow_two_nonneg; linarith
        · apply pow_two_nonneg
      exact hpos2
    have h_num_ge_8 : (8 : ℝ) ≤ (32 / (319 / 1000 : ℝ)) ^ 2 * (4442 / 1000 : ℝ) := by
      norm_num
    linarith
  set X := (32 / AdversarialBco.BodySpec.kappa) ^ 2 * (13 / 4 + 2 * AdversarialBco.BodySpec.kappa2) * (1 + T) ^ 2 * d ^ 2 with hX_def
  have hX_nonneg : 0 ≤ X := by
    rw [hX_def]
    apply mul_nonneg
    · apply mul_nonneg
      · apply mul_nonneg
        · apply pow_two_nonneg
        · have : 0 ≤ 13/4 + 2 * AdversarialBco.BodySpec.kappa2 := by linarith
          exact this
      · apply pow_two_nonneg
    · apply pow_two_nonneg
  have h_mu_g : μg * h ^ 2 ≤ X * (Vg + Vbg) := by
    rw [hX_def]
    have hcore_mul : μg * h ^ 2 ≤ (32 / AdversarialBco.BodySpec.kappa) ^ 2 * (1 + T) ^ 2 * d ^ 2 * (3 + 2 * AdversarialBco.BodySpec.kappa2 + 1 / (4 * d)) * (Vg + Vbg) := by
      have hκ_ne : AdversarialBco.BodySpec.kappa ≠ 0 := by linarith
      have hd_ne : d ≠ 0 := by linarith
      have hT1_ne : 1 + T ≠ 0 := by linarith
      field_simp [hκ_ne, hd_ne, hT1_ne] at hcore ⊢
      ring_nf at hcore ⊢
      nlinarith
    have hineq : (32 / AdversarialBco.BodySpec.kappa) ^ 2 * (1 + T) ^ 2 * d ^ 2 * (3 + 2 * AdversarialBco.BodySpec.kappa2 + 1 / (4 * d)) * (Vg + Vbg) ≤
        (32 / AdversarialBco.BodySpec.kappa) ^ 2 * (13 / 4 + 2 * AdversarialBco.BodySpec.kappa2) * (1 + T) ^ 2 * d ^ 2 * (Vg + Vbg) := by
      have h_factor_nonneg : 0 ≤ (32 / AdversarialBco.BodySpec.kappa) ^ 2 * (1 + T) ^ 2 * d ^ 2 := by
        apply mul_nonneg
        · apply mul_nonneg; apply pow_two_nonneg; apply pow_two_nonneg
        · apply pow_two_nonneg
      have h_sum_nonneg : 0 ≤ Vg + Vbg := by linarith
      have h_term_le : (3 + 2 * AdversarialBco.BodySpec.kappa2 + 1 / (4 * d)) ≤ (13 / 4 + 2 * AdversarialBco.BodySpec.kappa2) := by
        have h_frac : 1 / (4 * d) ≤ 1 / 4 := by
          have hpos : 0 < 4 * d := by linarith
          have hpos4 : 0 < (4 : ℝ) := by norm_num
          have hle : (4 : ℝ) ≤ 4 * d := by linarith
          exact (one_div_le_one_div hpos hpos4).mpr hle
        linarith
      have h_temp : (32 / AdversarialBco.BodySpec.kappa) ^ 2 * (1 + T) ^ 2 * d ^ 2 * (3 + 2 * AdversarialBco.BodySpec.kappa2 + 1 / (4 * d)) ≤
          (32 / AdversarialBco.BodySpec.kappa) ^ 2 * (1 + T) ^ 2 * d ^ 2 * (13 / 4 + 2 * AdversarialBco.BodySpec.kappa2) := by
        refine mul_le_mul_of_nonneg_left h_term_le h_factor_nonneg
      have h_temp' : (32 / AdversarialBco.BodySpec.kappa) ^ 2 * (1 + T) ^ 2 * d ^ 2 * (3 + 2 * AdversarialBco.BodySpec.kappa2 + 1 / (4 * d)) * (Vg + Vbg) ≤
          (32 / AdversarialBco.BodySpec.kappa) ^ 2 * (1 + T) ^ 2 * d ^ 2 * (13 / 4 + 2 * AdversarialBco.BodySpec.kappa2) * (Vg + Vbg) :=
        mul_le_mul_of_nonneg_right h_temp h_sum_nonneg
      simpa [mul_comm, mul_left_comm, mul_assoc] using h_temp'
    linarith
  have h_mu_m : μm * h ^ 2 ≤ X * (Vb + Vs) := by
    have hmoved' : μm * h ^ 2 ≤ 8 * (Vb + Vs) := by
      have : 0 ≤ (8 : ℝ) := by norm_num
      linarith
    have h8_le_X : (8 : ℝ) ≤ X := hX_ge_8
    have h_sum_nonneg : 0 ≤ Vb + Vs := by linarith
    have h_mul : 8 * (Vb + Vs) ≤ X * (Vb + Vs) := by
      nlinarith
    linarith
  have h_sum : Λ * h ^ 2 ≤ (μg + μm) * h ^ 2 := by
    have h_sq_nonneg : 0 ≤ h ^ 2 := pow_two_nonneg _
    exact mul_le_mul_of_nonneg_right hΛ h_sq_nonneg
  have h_comb : (μg + μm) * h ^ 2 ≤ X * (Vg + Vbg) + X * (Vb + Vs) := by
    linarith
  have h_Vg_Vbg_le : Vg + Vbg ≤ VG + Vb := by
    linarith
  have h_sum_le : X * (Vg + Vbg) + X * (Vb + Vs) ≤ X * (VG + Vb) + X * (Vb + Vs) := by
    have h_le : Vg + Vbg ≤ VG + Vb := h_Vg_Vbg_le
    have h_nonneg_X : 0 ≤ X := hX_nonneg
    have h1 : X * (Vg + Vbg) ≤ X * (VG + Vb) := mul_le_mul_of_nonneg_left h_le h_nonneg_X
    have h2 : X * (Vb + Vs) ≤ X * (Vb + Vs) := le_rfl
    linarith
  have h_mid : X * (VG + Vb) + X * (Vb + Vs) = X * (VG + 2 * Vb + Vs) := by ring
  rw [h_mid] at h_sum_le
  have h_final : X * (VG + 2 * Vb + Vs) ≤ 2 * X * (VG + Vb + Vs) := by
    have h_nonneg : 0 ≤ VG + Vs := by linarith
    have h_eq : 2 * X * (VG + Vb + Vs) = X * (2 * VG + 2 * Vb + 2 * Vs) := by ring
    rw [h_eq]
    refine mul_le_mul_of_nonneg_left ?_ hX_nonneg
    linarith
  have h_KS_eq : AdversarialBco.BodySpec.KS * (1 + T) ^ 2 * d ^ 2 = 2 * X := by
    rw [hX_def]
    rw [AdversarialBco.BodySpec.KS]
    ring
  have h_target : X * (Vg + Vbg) + X * (Vb + Vs) ≤ AdversarialBco.BodySpec.KS * (1 + T) ^ 2 * d ^ 2 * (VG + Vb + Vs) := by
    rw [h_KS_eq]
    linarith
  linarith
end

section

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal

theorem AdversarialBco.Body2.dil_arith2 (d T ℓ h Δs Δp Λ Vs Vb VG : ℝ) (hd : 1 ≤ d) (hT : 0 ≤ T) (hℓ : 0 < ℓ) (hh : 0 < h) (hΔ : 0 < Δs) (hΔh : Δs / 2 ≤ h) (hΛ : Δs / (2 * ℓ) ≤ h * Λ) (hscale : Λ * h ^ 2 ≤ AdversarialBco.BodySpec.KS * (1 + T) ^ 2 * d ^ 2 * (VG + Vb + Vs)) (hVs : 0 ≤ Vs) (hVb : 0 ≤ Vb) (hVG : 0 ≤ VG) (hΔp0 : 0 ≤ Δp) (hΔp : Δp ≤ 65 / 64 * Δs) : h * Δs / (2 * AdversarialBco.BodySpec.KS * (1 + T) ^ 2 * d ^ 2 * ℓ) ≤ Vs + Vb + VG ∧ Δp ^ 2 ≤ AdversarialBco.BodySpec.KD * (1 + T) ^ 2 * d ^ 2 * ℓ * ((1 - Δs / (4 * h)) * Vs + Δs / (4 * h) / 2 * Vb + Δs / (4 * h) / 2 * VG) := by
  set KS := AdversarialBco.BodySpec.KS with hKS
  set KD := AdversarialBco.BodySpec.KD with hKD
  set C := KS * (1 + T) ^ 2 * d ^ 2 with hC
  set V := Vs + Vb + VG with hV
  set q := Δs / (4 * h) with hq
  set I := (1 - q) * Vs + q / 2 * Vb + q / 2 * VG with hI
  have hKS_pos : 0 < KS := by
    have hκb := AdversarialBco.Body2.kappa_bounds
    rcases hκb with ⟨hκl, hκu, hκ2l, hκ2u⟩
    have hκ_pos : 0 < AdversarialBco.BodySpec.kappa := by linarith
    have hκ2_pos : 0 < AdversarialBco.BodySpec.kappa2 := by linarith
    have hnum_pos : 0 < 32 / AdversarialBco.BodySpec.kappa := div_pos (by norm_num) hκ_pos
    have hsq_pos : 0 < (32 / AdversarialBco.BodySpec.kappa) ^ 2 := pow_pos hnum_pos 2
    have hsum_pos : 0 < 13/4 + 2 * AdversarialBco.BodySpec.kappa2 := by linarith
    unfold KS
    exact mul_pos (mul_pos (by norm_num) hsq_pos) hsum_pos
  have hCpos : 0 < C := by
    unfold C
    positivity
  have hq_nonneg : 0 ≤ q := by
    rw [hq]
    exact div_nonneg (by linarith) (by linarith)
  have hq_le_half : q ≤ 1/2 := by
    rw [hq]
    field_simp [hh.ne']
    linarith
  have h_first : h * Δs / (2 * C * ℓ) ≤ V := by
    have hpos_2ℓ : 0 < 2 * ℓ := by linarith
    have htemp : h * Δs / (2 * ℓ) ≤ C * V := by
      calc
        h * Δs / (2 * ℓ) = h * (Δs / (2 * ℓ)) := by ring
        _ ≤ h * (h * Λ) := mul_le_mul_of_nonneg_left hΛ (by linarith)
        _ = h ^ 2 * Λ := by ring
        _ = Λ * h ^ 2 := by ring
        _ ≤ C * (VG + Vb + Vs) := hscale
        _ = C * V := by unfold V; ring
    have htemp' : h * Δs ≤ (C * V) * (2 * ℓ) := (div_le_iff₀ hpos_2ℓ).mp htemp
    have hpos_2Cℓ : 0 < 2 * C * ℓ := by positivity
    have hgoal : h * Δs ≤ V * (2 * C * ℓ) := by
      apply htemp'.trans
      rw [show (C * V) * (2 * ℓ) = V * (2 * C * ℓ) by ring]
    exact (div_le_iff₀ hpos_2Cℓ).mpr hgoal
  have hI_nonneg : 0 ≤ I := by
    have h1 : 0 ≤ 1 - q := by linarith
    have h2 : 0 ≤ q / 2 := div_nonneg hq_nonneg (by norm_num)
    unfold I
    nlinarith
  have hI_ge : I ≥ (q / 2) * V := by
    have h1 : (1 - q) * Vs ≥ (q / 2) * Vs := by
      have h_factor : 1 - q ≥ q / 2 := by linarith
      exact mul_le_mul_of_nonneg_right h_factor hVs
    have h2 : q / 2 * Vb ≥ 0 := mul_nonneg (div_nonneg hq_nonneg (by norm_num)) hVb
    have h3 : q / 2 * VG ≥ 0 := mul_nonneg (div_nonneg hq_nonneg (by norm_num)) hVG
    unfold I
    nlinarith
  have h_second : Δp ^ 2 ≤ KD * (1 + T) ^ 2 * d ^ 2 * ℓ * I := by
    have h_nonneg_bound : 0 ≤ (65/64) * Δs := mul_nonneg (by norm_num) (by linarith)
    have hΔp_sq : Δp ^ 2 ≤ ((65/64) * Δs) ^ 2 := by
      nlinarith
    have h_expand : ((65/64) * Δs) ^ 2 = (65/64)^2 * Δs ^ 2 := by ring
    rw [h_expand] at hΔp_sq
    have h_mid : (q / 2) * (h * Δs / (2 * C * ℓ)) = Δs ^ 2 / (16 * C * ℓ) := by
      rw [hq]
      have h1 : (Δs / (4 * h)) / 2 = Δs / (8 * h) := by
        field_simp [hh.ne']
        ring
      rw [h1]
      field_simp [hh.ne']
      ring
    have hq_div2_nonneg : 0 ≤ q / 2 := div_nonneg hq_nonneg (by norm_num)
    have hI_ge2 : I ≥ Δs ^ 2 / (16 * C * ℓ) := by
      calc
        I ≥ (q / 2) * V := hI_ge
        _ ≥ (q / 2) * (h * Δs / (2 * C * ℓ)) :=
          mul_le_mul_of_nonneg_left h_first hq_div2_nonneg
        _ = Δs ^ 2 / (16 * C * ℓ) := h_mid
    have hpos_16Cℓ : 0 < 16 * C * ℓ := by positivity
    have h_Δs_sq_bound : Δs ^ 2 ≤ 16 * C * ℓ * I := by
      have := (div_le_iff₀ hpos_16Cℓ).mp hI_ge2
      simpa [mul_comm, mul_left_comm, mul_assoc] using this
    have h_mid2 : (65/64)^2 * Δs ^ 2 ≤ (65/64)^2 * (16 * C * ℓ * I) :=
      mul_le_mul_of_nonneg_left h_Δs_sq_bound (by norm_num : (0 : ℝ) ≤ (65/64)^2)
    have h_KS_bound : (65/64)^2 * 16 * KS ≤ KD := by
      have h := AdversarialBco.Body2.KS_bounds
      rcases h with ⟨_, h_mul⟩
      exact h_mul
    have h_final : (65/64)^2 * (16 * C * ℓ * I) ≤ KD * (1 + T) ^ 2 * d ^ 2 * ℓ * I := by
      rw [hC]
      have h1 : ((65/64)^2 * 16 * KS) * ((1 + T) ^ 2 * d ^ 2) ≤ KD * ((1 + T) ^ 2 * d ^ 2) :=
        mul_le_mul_of_nonneg_right h_KS_bound (by positivity)
      have h2 : (((65/64)^2 * 16 * KS) * ((1 + T) ^ 2 * d ^ 2)) * (ℓ * I) ≤
          (KD * ((1 + T) ^ 2 * d ^ 2)) * (ℓ * I) :=
        mul_le_mul_of_nonneg_right h1 (mul_nonneg (by linarith) hI_nonneg)
      calc
        (65/64)^2 * (16 * (KS * (1 + T) ^ 2 * d ^ 2) * ℓ * I) =
            ((65/64)^2 * 16 * KS) * ((1 + T) ^ 2 * d ^ 2) * ℓ * I := by ring
        _ = (((65/64)^2 * 16 * KS) * ((1 + T) ^ 2 * d ^ 2)) * (ℓ * I) := by ring
        _ ≤ (KD * ((1 + T) ^ 2 * d ^ 2)) * (ℓ * I) := h2
        _ = KD * ((1 + T) ^ 2 * d ^ 2) * ℓ * I := by ring
        _ = KD * (1 + T) ^ 2 * d ^ 2 * ℓ * I := by ring
    linarith
  simpa [C, V, q, I, mul_assoc] using And.intro h_first h_second
end

section

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal

theorem AdversarialBco.Body2.exp_prod_le (a b c x : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hx : 0 ≤ x) : (1 + a * x) * (1 + b * x) * (1 + c * x) ≤ Real.exp ((a + b + c) * x) := by
  have hax : 0 ≤ a * x := mul_nonneg ha hx
  have hbx : 0 ≤ b * x := mul_nonneg hb hx
  have hcx : 0 ≤ c * x := mul_nonneg hc hx
  have h1 : 1 + a * x ≤ Real.exp (a * x) := by
    simpa [add_comm] using Real.add_one_le_exp (a * x)
  have h2 : 1 + b * x ≤ Real.exp (b * x) := by
    simpa [add_comm] using Real.add_one_le_exp (b * x)
  have h3 : 1 + c * x ≤ Real.exp (c * x) := by
    simpa [add_comm] using Real.add_one_le_exp (c * x)
  have hpos1 : 0 ≤ 1 + a * x := by linarith
  have hpos2 : 0 ≤ 1 + b * x := by linarith
  have hpos3 : 0 ≤ 1 + c * x := by linarith
  have hpos_exp1 : 0 ≤ Real.exp (a * x) := (Real.exp_pos _).le
  have hpos_exp2 : 0 ≤ Real.exp (b * x) := (Real.exp_pos _).le
  have hpos_exp3 : 0 ≤ Real.exp (c * x) := (Real.exp_pos _).le
  have h12 : (1 + a * x) * (1 + b * x) ≤ Real.exp (a * x) * Real.exp (b * x) :=
    mul_le_mul h1 h2 hpos2 hpos_exp1
  have hpos_exp12 : 0 ≤ Real.exp (a * x) * Real.exp (b * x) := mul_nonneg hpos_exp1 hpos_exp2
  have h123 : (1 + a * x) * (1 + b * x) * (1 + c * x) ≤ Real.exp (a * x) * Real.exp (b * x) * Real.exp (c * x) :=
    mul_le_mul h12 h3 hpos3 hpos_exp12
  calc
    (1 + a * x) * (1 + b * x) * (1 + c * x) ≤ Real.exp (a * x) * Real.exp (b * x) * Real.exp (c * x) := h123
    _ = Real.exp ((a * x) + (b * x)) * Real.exp (c * x) := by rw [← Real.exp_add]
    _ = Real.exp (((a * x) + (b * x)) + (c * x)) := by rw [← Real.exp_add]
    _ = Real.exp ((a + b + c) * x) := by rw [show ((a * x) + (b * x)) + (c * x) = (a + b + c) * x by ring]
end

section

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal

theorem AdversarialBco.Body2.final_arith (Δp KD T d ℓ L2n I W R2 q ι n CT lz : ℝ) (hKD0 : 0 ≤ KD) (hd : 1 ≤ d) (hℓ0 : 0 ≤ ℓ) (hℓ : ℓ ≤ L2n) (hq : 0 < q) (hι : 0 < ι) (hlz : 0 ≤ lz) (hKD : Δp ^ 2 ≤ KD * (1 + T) ^ 2 * d ^ 2 * ℓ * I) (hI : 2 * q * ι ≤ I) (hR2 : n ^ 2 * R2 ≤ q / 2 * (3 * ι / 4)) (hW : I / 2 - n ^ 2 * R2 ≤ W) (hT : (1 + T) ^ 2 ≤ CT * lz) (hC : 4 * KD * CT ≤ 1200000000) : Δp ^ 2 ≤ 1200000000 * d ^ 2 * lz * L2n * W := by
  have hIpos : 0 ≤ I := by
    have hpos : 0 < 2 * q * ι := by positivity
    linarith
  have h_nsqR2_le_3I_div_16 : n ^ 2 * R2 ≤ 3 * I / 16 := by
    have hqι_le_I_div_2 : q * ι ≤ I / 2 := by linarith
    have htmp : q / 2 * (3 * ι / 4) = 3 * (q * ι) / 8 := by ring
    have htmp2 : 3 * (q * ι) / 8 ≤ 3 * I / 16 := by nlinarith
    nlinarith
  have hWnonneg : 0 ≤ W := by
    have htmp : 0 ≤ I / 2 - n ^ 2 * R2 := by nlinarith
    linarith
  have h_5I_le_16W : 5 * I ≤ 16 * W := by nlinarith
  have hL2n_nonneg : 0 ≤ L2n := by linarith
  have h_sq_nonneg : 0 ≤ (1 + T) ^ 2 := pow_two_nonneg _
  have hCT_lz_nonneg : 0 ≤ CT * lz := by linarith
  have h_dsq_nonneg : 0 ≤ d ^ 2 := pow_two_nonneg _
  have h_prod_nonneg : 0 ≤ KD * CT * d ^ 2 * lz * L2n * W := by
    by_cases h_lz_zero : lz = 0
    · simp [h_lz_zero]
    · have h_lz_pos : 0 < lz := by
        by_contra! h_notpos
        have h_eq : lz = 0 := by linarith
        exact h_lz_zero h_eq
      have h_CT_nonneg : 0 ≤ CT :=
        le_of_mul_le_mul_left (by simpa [mul_comm] using hCT_lz_nonneg) h_lz_pos
      have h1 : 0 ≤ KD * CT := mul_nonneg hKD0 h_CT_nonneg
      have h2 : 0 ≤ (KD * CT) * d ^ 2 := mul_nonneg h1 h_dsq_nonneg
      have h3 : 0 ≤ ((KD * CT) * d ^ 2) * lz := mul_nonneg h2 hlz
      have h4 : 0 ≤ (((KD * CT) * d ^ 2) * lz) * L2n := mul_nonneg h3 hL2n_nonneg
      have h5 : 0 ≤ ((((KD * CT) * d ^ 2) * lz) * L2n) * W := mul_nonneg h4 hWnonneg
      exact h5
  have h_main : KD * (1 + T) ^ 2 * d ^ 2 * ℓ * I ≤ 1200000000 * d ^ 2 * lz * L2n * W := by
    calc
      KD * (1 + T) ^ 2 * d ^ 2 * ℓ * I ≤ KD * (CT * lz) * d ^ 2 * L2n * I := by
        have h_inner : (1 + T) ^ 2 * ℓ ≤ (CT * lz) * L2n := by
          calc
            (1 + T) ^ 2 * ℓ ≤ (CT * lz) * ℓ :=
              mul_le_mul_of_nonneg_right hT hℓ0
            _ ≤ (CT * lz) * L2n :=
              mul_le_mul_of_nonneg_left hℓ hCT_lz_nonneg
        have h_nonneg_factor : 0 ≤ KD * d ^ 2 * I := by
          apply mul_nonneg
          · apply mul_nonneg hKD0 h_dsq_nonneg
          · exact hIpos
        calc
          KD * (1 + T) ^ 2 * d ^ 2 * ℓ * I = (KD * d ^ 2 * I) * ((1 + T) ^ 2 * ℓ) := by ring
          _ ≤ (KD * d ^ 2 * I) * ((CT * lz) * L2n) :=
            mul_le_mul_of_nonneg_left h_inner h_nonneg_factor
          _ = KD * (CT * lz) * d ^ 2 * L2n * I := by ring
      _ ≤ KD * (CT * lz) * d ^ 2 * L2n * ((16/5 : ℝ) * W) := by
        have h_nonneg_factor : 0 ≤ KD * d ^ 2 * L2n := by
          apply mul_nonneg
          · apply mul_nonneg hKD0 h_dsq_nonneg
          · exact hL2n_nonneg
        have h_ineq : I ≤ (16/5 : ℝ) * W := by linarith
        calc
          KD * (CT * lz) * d ^ 2 * L2n * I = ((KD * d ^ 2 * L2n) * (CT * lz)) * I := by ring
          _ ≤ ((KD * d ^ 2 * L2n) * (CT * lz)) * ((16/5 : ℝ) * W) :=
            mul_le_mul_of_nonneg_left h_ineq (mul_nonneg h_nonneg_factor hCT_lz_nonneg)
          _ = KD * (CT * lz) * d ^ 2 * L2n * ((16/5 : ℝ) * W) := by ring
      _ = ((16/5 : ℝ) * KD * CT) * d ^ 2 * lz * L2n * W := by ring
      _ ≤ (4 * KD * CT) * d ^ 2 * lz * L2n * W := by
        nlinarith
      _ ≤ 1200000000 * d ^ 2 * lz * L2n * W := by
        have h_nonneg_prod' : 0 ≤ d ^ 2 * lz * L2n * W := by
          have h1 : 0 ≤ d ^ 2 := h_dsq_nonneg
          have h2 : 0 ≤ d ^ 2 * lz := mul_nonneg h1 hlz
          have h3 : 0 ≤ (d ^ 2 * lz) * L2n := mul_nonneg h2 hL2n_nonneg
          have h4 : 0 ≤ ((d ^ 2 * lz) * L2n) * W := mul_nonneg h3 hWnonneg
          exact h4
        nlinarith
  linarith
end

section

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal

theorem AdversarialBco.Body2.outside_arith (n m E2 X Γ t0 ι : ℝ) (hm0 : 0 ≤ m) (hm1 : m ≤ 1) (ht0 : 0 ≤ t0) (hι : 0 < ι) (hE2 : E2 ≤ 2 * (m + t0) * m + X) (hX : n ^ 2 * X ≤ ι / 4) (hΓm : Γ * m ≤ 1 / 8) (hΓ : n ^ 2 * (3 + 2 * t0) / (4 * ι) ≤ Γ) : n ^ 2 * (m ^ 2 + E2) ≤ 3 * ι / 4 := by
  have hpos : 0 < 4 * ι := by nlinarith
  have hn2_nonneg : 0 ≤ n ^ 2 := by nlinarith
  have h_step1 : n ^ 2 * (3 + 2 * t0) ≤ 4 * ι * Γ := by
    have := (div_le_iff₀ hpos).mp hΓ
    nlinarith
  have h_main : n ^ 2 * (m ^ 2 + E2) ≤ n ^ 2 * m * (3 + 2 * t0) + n ^ 2 * X := by
    calc
      n ^ 2 * (m ^ 2 + E2) ≤ n ^ 2 * (m ^ 2 + (2 * (m + t0) * m + X)) := by
        nlinarith
      _ = n ^ 2 * m ^ 2 + n ^ 2 * (2 * (m + t0) * m) + n ^ 2 * X := by ring
      _ = n ^ 2 * m * m + 2 * n ^ 2 * m * (m + t0) + n ^ 2 * X := by ring
      _ = n ^ 2 * m * (m + 2 * (m + t0)) + n ^ 2 * X := by ring
      _ = n ^ 2 * m * (3 * m + 2 * t0) + n ^ 2 * X := by ring
      _ ≤ n ^ 2 * m * (3 + 2 * t0) + n ^ 2 * X := by
        have h_ineq : 3 * m + 2 * t0 ≤ 3 + 2 * t0 := by nlinarith
        have h_nonneg_prod : 0 ≤ n ^ 2 * m := mul_nonneg hn2_nonneg hm0
        have h_mul := mul_le_mul_of_nonneg_left h_ineq h_nonneg_prod
        nlinarith
  have h_mid : n ^ 2 * m * (3 + 2 * t0) + n ^ 2 * X ≤ n ^ 2 * m * (3 + 2 * t0) + ι / 4 := by
    nlinarith
  have h_right : n ^ 2 * m * (3 + 2 * t0) + ι / 4 ≤ 3 * ι / 4 := by
    calc
      n ^ 2 * m * (3 + 2 * t0) + ι / 4 = m * (n ^ 2 * (3 + 2 * t0)) + ι / 4 := by ring
      _ ≤ m * (4 * ι * Γ) + ι / 4 := by nlinarith
      _ = 4 * ι * (Γ * m) + ι / 4 := by ring
      _ ≤ 4 * ι * (1 / 8) + ι / 4 := by nlinarith
      _ = ι / 2 + ι / 4 := by ring
      _ = 3 * ι / 4 := by ring
  nlinarith
end

section

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal

theorem AdversarialBco.Body2.iota_arith (Δ n d z T T' : ℝ) (hn : 2 ≤ n) (hd : 1 ≤ d) (hΔ1 : 1 / n < Δ) (hΔ2 : Δ ≤ 1) (hT : 0 ≤ T) (hTT : T ≤ T') (hz : n * d ≤ z) : 1 / (16 * 10 ^ 5 * (1 + T') ^ 2 * z ^ 2 * Real.log (2 * z)) ≤ Δ ^ 2 / (16 * 10 ^ 5 * (1 + T) ^ 2 * d ^ 2 * Real.log (2 / Δ)) := by
  have hnpos : 0 < n := by linarith
  have hdpos : 0 < d := by linarith
  have hΔpos : 0 < Δ := by
    have hpos : 0 < 1 / n := div_pos (by norm_num) hnpos
    linarith
  have hzpos : 0 < z := by
    have hpos : 0 < n * d := mul_pos hnpos hdpos
    linarith
  have hlogz_pos : 0 < Real.log (2 * z) := Real.log_pos (by nlinarith)
  have h_logΔ_arg : 1 < 2 / Δ := by
    have hΔlt2 : Δ < 2 := by linarith
    exact (one_lt_div hΔpos).mpr hΔlt2
  have hlogΔ_pos : 0 < Real.log (2 / Δ) := Real.log_pos h_logΔ_arg
  have hCpos : 0 < (16 : ℝ) * 10 ^ 5 := by norm_num
  have h_sq_pos : 0 < (1 + T') ^ 2 := pow_pos (by linarith : 0 < 1 + T') 2
  have h_sq_pos' : 0 < (1 + T) ^ 2 := pow_pos (by linarith : 0 < 1 + T) 2
  have h_denom1 : 0 < 16 * 10 ^ 5 * (1 + T') ^ 2 * z ^ 2 * Real.log (2 * z) := by
    refine mul_pos (mul_pos (mul_pos (by norm_num) h_sq_pos) (pow_pos hzpos 2)) hlogz_pos
  have h_denom2 : 0 < 16 * 10 ^ 5 * (1 + T) ^ 2 * d ^ 2 * Real.log (2 / Δ) := by
    refine mul_pos (mul_pos (mul_pos (by norm_num) h_sq_pos') (pow_pos hdpos 2)) hlogΔ_pos
  rw [div_le_div_iff₀ h_denom1 h_denom2]
  simp
  -- Goal: 16*10^5 * (1+T)^2 * d^2 * log(2/Δ) ≤ Δ^2 * (16*10^5 * (1+T')^2 * z^2 * log(2*z))
  -- Factor out C = 16*10^5 > 0
  have h_main : (1 + T) ^ 2 * d ^ 2 * Real.log (2 / Δ) ≤ Δ ^ 2 * ((1 + T') ^ 2 * z ^ 2 * Real.log (2 * z)) := by
    have hΔsq : 1 / n ^ 2 < Δ ^ 2 := by
      have h_one_div_n_nonneg : 0 ≤ 1 / n := by positivity
      have hsq : (1 / n) ^ 2 < Δ ^ 2 := pow_lt_pow_left₀ hΔ1 h_one_div_n_nonneg (by norm_num : 2 ≠ 0)
      calc
        1 / n ^ 2 = (1 / n) ^ 2 := by ring
        _ < Δ ^ 2 := hsq
    have hlog_le : Real.log (2 / Δ) ≤ Real.log (2 * z) := by
      have h_le : 2 / Δ ≤ 2 * z := by
        have h_one_div_n_pos : 0 < 1 / n := div_pos (by norm_num) hnpos
        have h : 1 / n ≤ Δ := by linarith
        have h_one_div : 1 / Δ ≤ 1 / (1 / n) :=
          ((one_div_le_one_div hΔpos h_one_div_n_pos).mpr h)
        calc
          2 / Δ = 2 * (1 / Δ) := by ring
          _ ≤ 2 * (1 / (1 / n)) := by nlinarith
          _ = 2 * n := by field_simp [hnpos.ne.symm]
          _ ≤ 2 * z := by nlinarith
      exact Real.log_le_log (by positivity) h_le
    have hT_sq_le : (1 + T) ^ 2 ≤ (1 + T') ^ 2 := by
      nlinarith
    have hd_sq_le : d ^ 2 ≤ z ^ 2 / n ^ 2 := by
      have hd_le : d ≤ z / n := by
        calc
          d = (n * d) / n := by field_simp [hnpos.ne.symm]
          _ ≤ z / n := div_le_div_of_nonneg_right hz (by positivity)
      have hd_nonneg : 0 ≤ d := by linarith
      have h_sq : d ^ 2 ≤ (z / n) ^ 2 := by
        nlinarith
      calc
        d ^ 2 ≤ (z / n) ^ 2 := h_sq
        _ = z ^ 2 / n ^ 2 := by ring
    have h_nonneg_logΔ : 0 ≤ Real.log (2 / Δ) := hlogΔ_pos.le
    have h_nonneg_logz : 0 ≤ Real.log (2 * z) := hlogz_pos.le
    have h_nonneg_T'sq : 0 ≤ (1 + T') ^ 2 := pow_two_nonneg _
    have h_nonneg_Tsq : 0 ≤ (1 + T) ^ 2 := pow_two_nonneg _
    have h_nonneg_dsq : 0 ≤ d ^ 2 := pow_two_nonneg _
    have h_nonneg_zsq_div_nsq : 0 ≤ z ^ 2 / n ^ 2 := div_nonneg (pow_two_nonneg _) (pow_two_nonneg _)
    have h_nonneg_prod : 0 ≤ (1 + T') ^ 2 * z ^ 2 * Real.log (2 * z) := by
      positivity
    have h_nonneg_T'sq_zsq_div_nsq : 0 ≤ (1 + T') ^ 2 * (z ^ 2 / n ^ 2) := mul_nonneg h_nonneg_T'sq h_nonneg_zsq_div_nsq
    have h_nonneg_Tsq_dsq : 0 ≤ (1 + T) ^ 2 * d ^ 2 := mul_nonneg h_nonneg_Tsq h_nonneg_dsq
    calc
      (1 + T) ^ 2 * d ^ 2 * Real.log (2 / Δ)
          ≤ (1 + T') ^ 2 * d ^ 2 * Real.log (2 / Δ) := by
        refine mul_le_mul_of_nonneg_right ?_ h_nonneg_logΔ
        refine mul_le_mul_of_nonneg_right hT_sq_le h_nonneg_dsq
      _ ≤ (1 + T') ^ 2 * (z ^ 2 / n ^ 2) * Real.log (2 / Δ) := by
        refine mul_le_mul_of_nonneg_right ?_ h_nonneg_logΔ
        refine mul_le_mul_of_nonneg_left hd_sq_le h_nonneg_T'sq
      _ ≤ (1 + T') ^ 2 * (z ^ 2 / n ^ 2) * Real.log (2 * z) := by
        refine mul_le_mul_of_nonneg_left hlog_le h_nonneg_T'sq_zsq_div_nsq
      _ = (1 / n ^ 2) * (1 + T') ^ 2 * z ^ 2 * Real.log (2 * z) := by ring
      _ = (1 / n ^ 2) * ((1 + T') ^ 2 * z ^ 2 * Real.log (2 * z)) := by ring
      _ ≤ Δ ^ 2 * ((1 + T') ^ 2 * z ^ 2 * Real.log (2 * z)) :=
        mul_le_mul_of_nonneg_right hΔsq.le h_nonneg_prod
  -- Now use h_main with the factor C = 16*10^5
  simpa [mul_comm, mul_left_comm, mul_assoc] using mul_le_mul_of_nonneg_left h_main hCpos.le
end

section

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal

theorem AdversarialBco.Body2.sh_arith (s m rb D z : ℝ) (hs : Real.sqrt (2 / Real.pi) * s ≤ m + D + rb) (hm : m ≤ 1 / 8) (hrb : rb ≤ m) (hD : 1 ≤ D) (hz : 2 * D ≤ z) : s ≤ Real.sqrt (Real.pi / 2) * (17 / 16) * z := by
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have hsqrt_pos : 0 < Real.sqrt (Real.pi / 2) :=
    Real.sqrt_pos.mpr (div_pos hpi_pos (by norm_num : (0 : ℝ) < 2))
  have hDpos : 0 < D := by linarith
  have hzpos : 0 < z := by linarith
  have h_key : Real.sqrt (Real.pi / 2) * Real.sqrt (2 / Real.pi) = 1 := by
    calc
      Real.sqrt (Real.pi / 2) * Real.sqrt (2 / Real.pi) =
          Real.sqrt ((Real.pi / 2) * (2 / Real.pi)) := by
        rw [← Real.sqrt_mul (by positivity : 0 ≤ Real.pi / 2)]
      _ = Real.sqrt 1 := by
        field_simp [hpi_pos.ne.symm]
      _ = 1 := Real.sqrt_one
  have hsum : m + D + rb ≤ D + 1/4 := by
    have : rb ≤ 1/8 := by linarith
    linarith
  have hineq : D + 1/4 ≤ (5/4 : ℝ) * D := by
    nlinarith
  have hDle : D ≤ z / 2 := by linarith
  have hcoeff : (5/8 : ℝ) ≤ (17/16 : ℝ) := by norm_num
  calc
    s = 1 * s := by ring
    _ = (Real.sqrt (Real.pi / 2) * Real.sqrt (2 / Real.pi)) * s := by rw [h_key]
    _ = Real.sqrt (Real.pi / 2) * (Real.sqrt (2 / Real.pi) * s) := by ring
    _ ≤ Real.sqrt (Real.pi / 2) * (m + D + rb) := by gcongr
    _ ≤ Real.sqrt (Real.pi / 2) * (D + 1/4) := by gcongr
    _ ≤ Real.sqrt (Real.pi / 2) * ((5/4 : ℝ) * D) := by gcongr
    _ = Real.sqrt (Real.pi / 2) * (5/4 : ℝ) * D := by ring
    _ ≤ Real.sqrt (Real.pi / 2) * (5/4 : ℝ) * (z / 2) := by gcongr
    _ = Real.sqrt (Real.pi / 2) * (5/8 : ℝ) * z := by ring
    _ ≤ Real.sqrt (Real.pi / 2) * (17/16 : ℝ) * z := by gcongr
end

section

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal

theorem AdversarialBco.Body2.proj_var (k : ℕ) (w : Fin k → ℝ) (hw : ∀ c, 0 ≤ w c) (hw1 : ∑ c, w c = 1) (a b : Fin k → ℝ) (t e : ℝ) (h : ∀ c, t ≤ a c - b c ∧ a c - b c ≤ t + e) : ∑ c, w c * (a c - ∑ c', w c' * a c') ^ 2 ≤ 2 * ∑ c, w c * ((∑ c', w c' * b c') - b c) ^ 2 + 2 * e ^ 2 := by
  -- define δ c = a c - b c - t ∈ [0, e]
  let δ : Fin k → ℝ := fun c => a c - b c - t
  have hδ_nonneg : ∀ c, 0 ≤ δ c := by
    intro c
    rcases h c with ⟨hlt, _⟩
    linarith
  have hδ_le_e : ∀ c, δ c ≤ e := by
    intro c
    rcases h c with ⟨_, hle⟩
    linarith
  -- define averages
  let a_avg : ℝ := ∑ c, w c * a c
  let b_avg : ℝ := ∑ c, w c * b c
  let d_avg : ℝ := ∑ c, w c * δ c
  -- a_avg = b_avg + t + d_avg
  have h_avg_eq : a_avg = b_avg + t + d_avg := by
    dsimp [a_avg, b_avg, d_avg, δ]
    calc
      ∑ c, w c * a c = ∑ c, w c * (b c + t + (a c - b c - t)) := by
        refine Finset.sum_congr rfl (fun c _ => ?_)
        ring
      _ = ∑ c, (w c * (b c + t) + w c * (a c - b c - t)) := by
        refine Finset.sum_congr rfl (fun c _ => ?_)
        ring
      _ = (∑ c, w c * (b c + t)) + (∑ c, w c * (a c - b c - t)) := by rw [Finset.sum_add_distrib]
      _ = (∑ c, (w c * b c + w c * t)) + (∑ c, w c * (a c - b c - t)) := by
        refine congrArg (· + _) (Finset.sum_congr rfl (fun c _ => ?_))
        ring
      _ = ((∑ c, w c * b c) + (∑ c, w c * t)) + (∑ c, w c * (a c - b c - t)) := by rw [Finset.sum_add_distrib]
      _ = ((∑ c, w c * b c) + t * (∑ c, w c)) + (∑ c, w c * (a c - b c - t)) := by
        simp [Finset.mul_sum, mul_comm]
      _ = (b_avg + t * (∑ c, w c)) + d_avg := by dsimp [b_avg, d_avg]
      _ = (b_avg + t * 1) + d_avg := by rw [hw1]
      _ = b_avg + t + d_avg := by ring
  -- a c - a_avg = (b c - b_avg) + (δ c - d_avg)
  have h_diff_eq : ∀ c, a c - a_avg = (b c - b_avg) + (δ c - d_avg) := by
    intro c
    calc
      a c - a_avg = a c - (b_avg + t + d_avg) := by rw [h_avg_eq]
      _ = (b c + t + δ c) - (b_avg + t + d_avg) := by dsimp [δ]; ring
      _ = (b c - b_avg) + (δ c - d_avg) := by ring
  -- bounds on d_avg
  have hd_avg_nonneg : 0 ≤ d_avg := by
    dsimp [d_avg]
    refine Finset.sum_nonneg (fun c _ => mul_nonneg (hw c) (hδ_nonneg c))
  have hd_avg_le_e : d_avg ≤ e := by
    dsimp [d_avg]
    calc
      ∑ c, w c * δ c ≤ ∑ c, w c * e :=
        Finset.sum_le_sum (fun c _ => mul_le_mul_of_nonneg_left (hδ_le_e c) (hw c))
      _ = e * (∑ c, w c) := by simp [Finset.mul_sum, mul_comm]
      _ = e * 1 := by rw [hw1]
      _ = e := by ring
  -- inequality (x + y)^2 ≤ 2*x^2 + 2*y^2
  have h_sq_add_le : ∀ x y : ℝ, (x + y)^2 ≤ 2*x^2 + 2*y^2 := by
    intro x y
    nlinarith [sq_nonneg (x - y)]
  -- bound (δ c - d_avg)^2 ≤ e^2
  have h_d_diff_sq_le : ∀ c, (δ c - d_avg)^2 ≤ e^2 := by
    intro c
    have h_low : -e ≤ δ c - d_avg := by
      have : 0 ≤ δ c := hδ_nonneg c
      have : d_avg ≤ e := hd_avg_le_e
      linarith
    have h_high : δ c - d_avg ≤ e := by
      have : δ c ≤ e := hδ_le_e c
      have : 0 ≤ d_avg := hd_avg_nonneg
      linarith
    nlinarith
  calc
    ∑ c, w c * (a c - a_avg)^2 = ∑ c, w c * ((b c - b_avg) + (δ c - d_avg))^2 := by
      refine Finset.sum_congr rfl (fun c _ => ?_)
      rw [h_diff_eq c]
    _ ≤ ∑ c, w c * (2*(b c - b_avg)^2 + 2*(δ c - d_avg)^2) := by
      refine Finset.sum_le_sum (fun c _ => ?_)
      exact mul_le_mul_of_nonneg_left (h_sq_add_le (b c - b_avg) (δ c - d_avg)) (hw c)
    _ = (∑ c, w c * (2*(b c - b_avg)^2)) + (∑ c, w c * (2*(δ c - d_avg)^2)) := by
      simp [Finset.sum_add_distrib, mul_add]
    _ = 2 * (∑ c, w c * (b c - b_avg)^2) + 2 * (∑ c, w c * (δ c - d_avg)^2) := by
      have h1 : ∑ c, w c * (2*(b c - b_avg)^2) = 2 * (∑ c, w c * (b c - b_avg)^2) := by
        calc
          ∑ c, w c * (2*(b c - b_avg)^2) = ∑ c, 2 * (w c * (b c - b_avg)^2) := by
            refine Finset.sum_congr rfl (fun c _ => ?_)
            ring
          _ = 2 * (∑ c, w c * (b c - b_avg)^2) := by rw [Finset.mul_sum]
      have h2 : ∑ c, w c * (2*(δ c - d_avg)^2) = 2 * (∑ c, w c * (δ c - d_avg)^2) := by
        calc
          ∑ c, w c * (2*(δ c - d_avg)^2) = ∑ c, 2 * (w c * (δ c - d_avg)^2) := by
            refine Finset.sum_congr rfl (fun c _ => ?_)
            ring
          _ = 2 * (∑ c, w c * (δ c - d_avg)^2) := by rw [Finset.mul_sum]
      rw [h1, h2]
    _ ≤ 2 * (∑ c, w c * (b c - b_avg)^2) + 2 * (∑ c, w c * e^2) := by
      have hsum : ∑ c, w c * (δ c - d_avg)^2 ≤ ∑ c, w c * e^2 :=
        Finset.sum_le_sum (fun c _ => mul_le_mul_of_nonneg_left (h_d_diff_sq_le c) (hw c))
      nlinarith
    _ = 2 * (∑ c, w c * (b c - b_avg)^2) + 2 * (e^2 * (∑ c, w c)) := by
      have htemp : ∑ c, w c * e^2 = e^2 * (∑ c, w c) := by
        rw [← Finset.sum_mul, mul_comm]
      rw [htemp]
    _ = 2 * (∑ c, w c * (b c - b_avg)^2) + 2 * (e^2 * 1) := by rw [hw1]
    _ = 2 * (∑ c, w c * (b c - b_avg)^2) + 2 * e^2 := by ring
    _ = 2 * ∑ c, w c * ((∑ c', w c' * b c') - b c)^2 + 2 * e^2 := by
      refine congrArg (fun x => 2 * x + 2 * e^2) (Finset.sum_congr rfl (fun c _ => ?_))
      dsimp [b_avg]
      ring
end

section

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal

theorem AdversarialBco.Body2.mass_arith (Fs Fb EF m h : ℝ) (hh : 0 < h) (hΔ : 0 < Fs - m) (hb : Fs ≤ Fb) (hp : (1 - (Fs - m) / (4 * h)) * Fs + (Fs - m) / (4 * h) / 2 * Fb + (Fs - m) / (4 * h) / 2 * EF - m ≤ 65 / 64 * (Fs - m)) : EF - Fs ≤ h / 8 := by
  set Δ := Fs - m with hΔdef
  have hΔpos : 0 < Δ := hΔ
  set q := Δ / (4 * h) with hqdef
  have hqpos : 0 < q := by
    rw [hqdef]
    exact div_pos hΔpos (by nlinarith)
  have hp_rewritten : Δ + (q / 2) * (Fb - Fs) + (q / 2) * (EF - Fs) ≤ 65 / 64 * Δ := by
    calc
      Δ + (q / 2) * (Fb - Fs) + (q / 2) * (EF - Fs) = (1 - q) * Fs + (q / 2) * Fb + (q / 2) * EF - m := by
        dsimp [Δ, q]
        ring
      _ ≤ 65 / 64 * (Fs - m) := hp
      _ = 65 / 64 * Δ := by rw [hΔdef]
  have hnonneg : 0 ≤ (q / 2) * (Fb - Fs) := by
    have hq2 : 0 ≤ q / 2 := by nlinarith
    have hFbFs : 0 ≤ Fb - Fs := by nlinarith
    nlinarith
  have hineq2 : (q / 2) * (EF - Fs) ≤ Δ / 64 := by
    nlinarith
  have hΔ_eq : Δ = 4 * h * q := by
    dsimp [q]
    field_simp [ne_of_gt hh]
  have hineq3 : (q / 2) * (EF - Fs) ≤ (h * q) / 16 := by
    calc
      (q / 2) * (EF - Fs) ≤ Δ / 64 := hineq2
      _ = (4 * h * q) / 64 := by rw [hΔ_eq]
      _ = (h * q) / 16 := by ring
  have hfinal : EF - Fs ≤ h / 8 := by
    have hqne0 : q ≠ 0 := by linarith
    have hqpos' : 0 ≤ 2 / q := by
      have : 0 < 2 / q := div_pos (by norm_num) hqpos
      exact this.le
    calc
      EF - Fs = (2 / q) * ((q / 2) * (EF - Fs)) := by
        field_simp [hqne0]
      _ ≤ (2 / q) * (h * q / 16) := by
        gcongr
      _ = h / 8 := by
        field_simp [hqne0]
        ring
  exact hfinal
end

section

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal

theorem AdversarialBco.Body2.log_gmax (n Δ gmax : ℝ) (hn : 2 ≤ n) (hΔ : 1 / n < Δ) (hΔg : Δ ≤ gmax) (hg : gmax ≤ 1) : 0 < Real.log (2 * gmax / Δ) ∧ Real.log (2 * gmax / Δ) ≤ Real.log (2 / Δ) ∧ Real.log (2 * gmax / Δ) ≤ Real.log (2 * n) := by
  have hnpos : 0 < n := by linarith
  have hΔpos : 0 < Δ := by
    have hpos : 0 < 1 / n := div_pos (by norm_num) hnpos
    linarith
  have hgpos : 0 < gmax := by linarith
  have h_div_pos : 0 < 2 * gmax / Δ := div_pos (by nlinarith) hΔpos
  have h_one_lt : 1 < 2 * gmax / Δ := by
    have hge : 1 ≤ gmax / Δ := (one_le_div hΔpos).mpr hΔg
    have h_eq : 2 * gmax / Δ = 2 * (gmax / Δ) := by ring
    rw [h_eq]
    have h2le : 2 ≤ 2 * (gmax / Δ) := by nlinarith
    linarith
  have h_le_div : 2 * gmax / Δ ≤ 2 / Δ := by
    have h : 2 * gmax ≤ 2 * 1 := by nlinarith
    have hdiv := div_le_div_of_nonneg_right h hΔpos.le
    simpa [mul_one] using hdiv
  have h_div_lt : 2 / Δ < 2 * n := by
    have htemp : 1 < n * Δ := by
      have h := (div_lt_iff₀ hnpos).mp hΔ
      simpa [mul_comm] using h
    have h_inv : 1 / Δ < n := (div_lt_iff₀ hΔpos).mpr htemp
    calc
      2 / Δ = 2 * (1 / Δ) := by ring
      _ < 2 * n := mul_lt_mul_of_pos_left h_inv (by norm_num : (0 : ℝ) < 2)
  have hlogpos : 0 < Real.log (2 * gmax / Δ) := Real.log_pos h_one_lt
  have hlogle1 : Real.log (2 * gmax / Δ) ≤ Real.log (2 / Δ) :=
    Real.log_le_log h_div_pos h_le_div
  have h_div2_pos : 0 < 2 / Δ := div_pos (by norm_num) hΔpos
  have hlogle2 : Real.log (2 * gmax / Δ) ≤ Real.log (2 * n) := by
    apply le_trans hlogle1
    apply Real.log_le_log h_div2_pos
    linarith
  exact And.intro hlogpos (And.intro hlogle1 hlogle2)
end

section

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal

theorem AdversarialBco.Body2.p3_iota (h Δ KS T d ℓ ℓ2 V : ℝ) (hΔ : 0 < Δ) (hΔh : Δ / 2 ≤ h) (hKS0 : 0 < KS) (hKS : KS ≤ 10 ^ 5) (hd : 1 ≤ d) (hT : 0 ≤ T) (hℓ : 0 < ℓ) (hℓ2 : ℓ ≤ ℓ2) (hP3 : h * Δ / (2 * KS * (1 + T) ^ 2 * d ^ 2 * ℓ) ≤ V) : 4 * (Δ ^ 2 / (16 * 10 ^ 5 * (1 + T) ^ 2 * d ^ 2 * ℓ2)) ≤ V := by
  have hΔ_bound : Δ ≤ 2 * h := by linarith
  have h_nonneg_Δ : 0 ≤ Δ := by linarith
  have h_nonneg_KS : 0 ≤ KS := by linarith
  have h_nonneg_ℓ : 0 ≤ ℓ := by linarith
  have h_nonneg_2h : 0 ≤ 2 * h := by linarith
  have h_nonneg_10pow5 : 0 ≤ (10 : ℝ) ^ 5 := by norm_num
  have h_nonneg_ℓ2 : 0 ≤ ℓ2 := by linarith
  have h_nonneg_prod : 0 ≤ (2 * h) * (10 : ℝ) ^ 5 := by nlinarith
  have h_main_ineq : Δ * KS * ℓ ≤ 2 * h * (10 : ℝ) ^ 5 * ℓ2 := by
    have h_first : Δ * KS ≤ (2 * h) * (10 : ℝ) ^ 5 := by
      exact mul_le_mul hΔ_bound hKS h_nonneg_KS h_nonneg_2h
    have h_second : (Δ * KS) * ℓ ≤ ((2 * h) * (10 : ℝ) ^ 5) * ℓ2 := by
      exact mul_le_mul h_first hℓ2 h_nonneg_ℓ h_nonneg_prod
    calc
      Δ * KS * ℓ = (Δ * KS) * ℓ := by ring
      _ ≤ ((2 * h) * (10 : ℝ) ^ 5) * ℓ2 := h_second
      _ = 2 * h * (10 : ℝ) ^ 5 * ℓ2 := by ring
  have hpos_denom1 : 0 < 16 * (10 : ℝ) ^ 5 * (1 + T) ^ 2 * d ^ 2 * ℓ2 := by
    have h1 : 0 < (10 : ℝ) ^ 5 := by norm_num
    have h2 : 0 < 1 + T := by linarith
    have h2sq : 0 < (1 + T) ^ 2 := by positivity
    have h3 : 0 < d := by linarith
    have h3sq : 0 < d ^ 2 := by positivity
    have h4 : 0 < ℓ2 := by linarith
    positivity
  have hpos_denom2 : 0 < 2 * KS * (1 + T) ^ 2 * d ^ 2 * ℓ := by
    have h2sq : 0 < (1 + T) ^ 2 := by
      have h2 : 0 < 1 + T := by linarith
      positivity
    have h3sq : 0 < d ^ 2 := by
      have h3 : 0 < d := by linarith
      positivity
    positivity
  have h_main : 4 * (Δ ^ 2 / (16 * 10 ^ 5 * (1 + T) ^ 2 * d ^ 2 * ℓ2)) ≤ h * Δ / (2 * KS * (1 + T) ^ 2 * d ^ 2 * ℓ) := by
    calc
      4 * (Δ ^ 2 / (16 * 10 ^ 5 * (1 + T) ^ 2 * d ^ 2 * ℓ2)) = (4 * Δ ^ 2) / (16 * (10 : ℝ) ^ 5 * (1 + T) ^ 2 * d ^ 2 * ℓ2) := by ring
      _ ≤ h * Δ / (2 * KS * (1 + T) ^ 2 * d ^ 2 * ℓ) := by
        rw [div_le_div_iff₀ hpos_denom1 hpos_denom2]
        have h_sq_nonneg : 0 ≤ (1 + T) ^ 2 * d ^ 2 := by positivity
        have hLHS : (4 * Δ ^ 2) * (2 * KS * (1 + T) ^ 2 * d ^ 2 * ℓ) = ((1 + T) ^ 2 * d ^ 2) * (8 * Δ ^ 2 * KS * ℓ) := by ring
        have hRHS : (h * Δ) * (16 * (10 : ℝ) ^ 5 * (1 + T) ^ 2 * d ^ 2 * ℓ2) = ((1 + T) ^ 2 * d ^ 2) * (16 * h * Δ * (10 : ℝ) ^ 5 * ℓ2) := by ring
        rw [hLHS, hRHS]
        refine mul_le_mul_of_nonneg_left ?_ h_sq_nonneg
        nlinarith
  linarith
end
