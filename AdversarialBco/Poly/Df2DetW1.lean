/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.Df2DetAcc

@[expose] public section

/-!
# DET, (W1) of Lemma D.14 at `τ`

For `x ∈ K_ε`, `eReg_τ(x) ≤ sReg_τ(x) + 1 + d L/(η λ)`. Each round: the play shift
(`E_{p'} e - s(μ) = (1 - λ)(E_p e - s(μ))`), prop:lower (X3) with a nonnegative right side, `s ≤ e` (X7); the trace
term by Lemma D.12 (`ld_core` with `H_u = η κ s''_u ≤ P̄_u`, from X6, `P_u ≤ 2 P̄_u` and row R6) and `Σ_u ≤ 2 P̄_u⁻¹`;
the terms `2 δ_e d/λ` sum to at most 1 (condition c2dl).
-/

open Matrix MeasureTheory ProbabilityTheory
open scoped Matrix

namespace AdversarialBco.Poly

open Layer2

namespace DetBase

variable {d : ℕ} {c : Df2Ctx d} {δ : ℝ} {π : Df2Path d} {m : ℕ}

theorem PBar_posDef (H : DetBase c δ π m) {u : ℕ} (hu : u ≤ c.tau π m) :
    ((1 / 2 : ℝ) • c.PBar π u).PosDef ∧ (c.PBar π u).PosDef := by
  have h1 := posDef_of_sub H.rows.pos_de (H.stInv_le_tau u hu).pbd
  refine ⟨h1, ?_⟩
  have := h1.smul (two_pos : (0 : ℝ) < 2)
  rwa [smul_smul, show (2 : ℝ) * (1 / 2) = 1 by norm_num, one_smul] at this

/-- `η κ s''_u ≤ P̄_u` for `u ≤ τ`. -/
theorem H_le_PBar (H : DetBase c δ π m) {u : ℕ} (hu : u ≤ c.tau π m) :
    (c.PBar π u - (c.p.eta * c.p.kap) • c.sHess π u).PosSemidef := by
  have hI := H.stInv_le_tau u hu
  have hsi := H.si_at hu
  have hpsd := H.sHess_psd hu
  have hPB := H.PBar_psd hu
  apply psd_of_sq (hPB.1.sub (herm_smul _ hpsd.1))
  intro v
  rw [sq_sub, sq_smul]
  have h1 : df2Sq (c.sHess π u) v ≤
      c.p.lam * (8 / c.p.eps) / (1 - c.p.lam) * Real.sqrt (2 * d * c.p.sig2) * df2Sq (c.st π u).P v := by
    have := le_of_abs_le (hsi.hess2 (WithLp.toLp 2 (c.st π u).mu) v)
    rwa [H.AAinv hu] at this
  have h2 := sq_le_of_psd hI.pbh v
  rw [sq_smul] at h2
  have hP0 := sq_nonneg_of_psd hI.pd.posSemidef v
  have hl := H.rows.lam_le
  have hl0 := H.rows.pos_lam
  have he := H.rows.pos_eps
  have hK : c.p.eta * c.p.kap * (c.p.lam * (8 / c.p.eps) / (1 - c.p.lam) * Real.sqrt (2 * d * c.p.sig2)) ≤
      1 / 2 := by
    have r6 := H.rows.r6
    rw [H.kap]
    have e : c.p.eta * (1 / 4) * (c.p.lam * (8 / c.p.eps) / (1 - c.p.lam) * Real.sqrt (2 * d * c.p.sig2)) =
        (8 * c.p.eta * c.p.lam * Real.sqrt (2 * d * c.p.sig2) / c.p.eps) / (4 * (1 - c.p.lam)) := by
      field_simp
    rw [e, div_le_iff₀ (by linarith)]
    nlinarith
  have hek := H.kap_pos
  have h3 : c.p.eta * c.p.kap * df2Sq (c.sHess π u) v ≤ df2Sq (c.PBar π u) v := by
    calc c.p.eta * c.p.kap * df2Sq (c.sHess π u) v
        ≤ c.p.eta * c.p.kap * (c.p.lam * (8 / c.p.eps) / (1 - c.p.lam) * Real.sqrt (2 * d * c.p.sig2) *
            df2Sq (c.st π u).P v) := mul_le_mul_of_nonneg_left h1 hek.le
      _ = c.p.eta * c.p.kap * (c.p.lam * (8 / c.p.eps) / (1 - c.p.lam) * Real.sqrt (2 * d * c.p.sig2)) *
            df2Sq (c.st π u).P v := by ring
      _ ≤ 1 / 2 * df2Sq (c.st π u).P v := mul_le_mul_of_nonneg_right hK hP0
      _ ≤ df2Sq (c.PBar π u) v := by linarith
  linarith

/-- `tr(s''_u Σ_u) ≤ 2 tr(s''_u P̄_u⁻¹)`. -/
theorem trace_S_le (H : DetBase c δ π m) {u : ℕ} (hu : u ≤ c.tau π m) :
    (c.sHess π u * ((c.st π u).A * (c.st π u).Aᵀ)).trace ≤ 2 * (c.sHess π u * (c.PBar π u)⁻¹).trace := by
  have hI := H.stInv_le_tau u hu
  obtain ⟨hh, hPpd⟩ := H.PBar_posDef hu
  have hS : (c.st π u).S = (c.st π u).P⁻¹ := (Matrix.inv_eq_left_inv hI.SP).symm
  have hinv := inv_antitone _ _ hh hI.pd hI.pbl
  have htr := trace_mul_nonneg _ _ (H.sHess_psd hu) hinv
  rw [Matrix.mul_sub, Matrix.trace_sub, sub_nonneg] at htr
  have hdet : IsUnit (c.PBar π u).det := isUnit_iff_ne_zero.2 hPpd.det_pos.ne'
  have e : ((1 / 2 : ℝ) • c.PBar π u)⁻¹ = (2 : ℝ) • (c.PBar π u)⁻¹ := by
    apply Matrix.inv_eq_left_inv
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.nonsing_inv_mul _ hdet]
    norm_num
  rw [e, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul] at htr
  rw [hI.AA, hS]
  exact htr

end DetBase

namespace DetHyp

variable {d : ℕ} {c : Df2Ctx d} {δ : ℝ} {π : Df2Path d} {m : ℕ}

/-- Lemma D.12 on the run. -/
theorem ld_sum (H : DetHyp c δ π m) :
    ∑ u ∈ Finset.range (c.tau π m + 1), ((c.PBar π u)⁻¹ * ((c.p.eta * c.p.kap) • c.sHess π u)).trace ≤
      2 * d * Real.log (1 / (2 * c.p.δe) * c.p.sig2) := by
  have hde := H.rows.pos_de
  have htop : ((1 / (2 * c.p.δe)) • (1 : Matrix (Fin d) (Fin d) ℝ) - c.PBar π (c.tau π m + 1)).PosSemidef := by
    have h := (H.c3_tau).2.2.2
    refine psd_of_eq (h.smul (by norm_num : (0 : ℝ) ≤ 1 / 2)) ?_
    rw [smul_sub, smul_smul, smul_smul]
    congr 1
    · congr 1; field_simp
    · norm_num
  exact ld_core (c.PBar π) (fun u => (c.p.eta * c.p.kap) • c.sHess π u) (c.tau π m) c.p.sig2 (1 / (2 * c.p.δe))
    H.rows.pos_sig2 (by positivity) (c.PBar_zero π) (fun u _ => c.PBar_succ π u)
    (fun u hu => (H.sHess_psd hu).smul H.kap_pos.le) (fun u hu => H.H_le_PBar hu) htop

/-- The trace term of (W1): `∑_{u ≤ τ} (2/λ) tr(s''_u Σ_u) ≤ d L/(λ η)`. -/
theorem trace_sum (H : DetHyp c δ π m) :
    ∑ u ∈ Finset.range (c.tau π m + 1), 2 / c.p.lam * (c.sHess π u * ((c.st π u).A * (c.st π u).Aᵀ)).trace ≤
      d * c.p.Le / (c.p.lam * c.p.eta) := by
  have hl := H.rows.pos_lam
  have hη := H.rows.pos_eta
  have hek := H.kap_pos
  have hld := H.ld_sum
  have e : ∀ u, ((c.PBar π u)⁻¹ * ((c.p.eta * c.p.kap) • c.sHess π u)).trace =
      c.p.eta * c.p.kap * (c.sHess π u * (c.PBar π u)⁻¹).trace := fun u => by
    rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Matrix.trace_mul_comm]
  simp only [e] at hld
  rw [← Finset.mul_sum] at hld
  have hσ1 : 2 * c.p.sig2 ≤ 1 := H.rows.r2
  have hσδ : 4 * c.p.δe ≤ c.p.sig2 := by
    have := H.rows.c4; rwa [div_le_iff₀ H.rows.pos_sig2, one_mul] at this
  obtain ⟨hlog, harith⟩ := w1_arith c.p.lam c.p.eta d c.p.δe c.p.sig2 c.p.Le hl hη (Nat.cast_nonneg d)
    H.rows.pos_de H.rows.de_lt H.rows.pos_sig2 hσ1 hσδ H.Le_eq
  have h1 : ∑ u ∈ Finset.range (c.tau π m + 1), (c.sHess π u * ((c.st π u).A * (c.st π u).Aᵀ)).trace ≤
      2 * ∑ u ∈ Finset.range (c.tau π m + 1), (c.sHess π u * (c.PBar π u)⁻¹).trace := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun u hu => H.trace_S_le (by have := Finset.mem_range.1 hu; omega)
  have h2 : 2 * ∑ u ∈ Finset.range (c.tau π m + 1), (c.sHess π u * (c.PBar π u)⁻¹).trace ≤
      2 / (c.p.eta * (1 / 4)) * (2 * d * Real.log (1 / (2 * c.p.δe) * c.p.sig2)) := by
    rw [← H.kap]
    rw [div_mul_eq_mul_div, le_div_iff₀ hek]
    nlinarith
  rw [← Finset.mul_sum]
  calc 2 / c.p.lam * ∑ u ∈ Finset.range (c.tau π m + 1), (c.sHess π u * ((c.st π u).A * (c.st π u).Aᵀ)).trace
      ≤ 2 / c.p.lam * (2 / (c.p.eta * (1 / 4)) * (2 * d * Real.log (1 / (2 * c.p.δe) * c.p.sig2))) :=
        mul_le_mul_of_nonneg_left (h1.trans h2) (by positivity)
    _ ≤ _ := harith

/-- One round of (W1): `ē_s - e_s(x) ≤ (2/λ) tr(s''_s Σ_s) + 2 δ_e d/λ + s_s(μ_s) - s_s(x)`. -/
theorem w1_round (H : DetHyp c δ π m) {s : ℕ} (hs : s ≤ c.tau π m) (x : Fin d → ℝ) :
    c.ebar π s - df2Ext c.p c.Kt (π.g s) (WithLp.toLp 2 x) ≤
      (2 / c.p.lam * (c.sHess π s * ((c.st π s).A * (c.st π s).Aᵀ)).trace + 2 * c.p.δe * d / c.p.lam) +
        (c.surr π s (WithLp.toLp 2 (c.st π s).mu) - c.surr π s (WithLp.toLp 2 x)) := by
  have hI := H.stInv_le_tau s hs
  have hsi := H.si_at hs
  have hl := H.rows.pos_lam
  have hl2 := H.rows.lam_le
  have hsh : c.ebar π s - c.surr π s (WithLp.toLp 2 (c.st π s).mu) =
      (1 - c.p.lam) * ((∫ z, df2Ext c.p c.Kt (π.g s)
        (WithLp.toLp 2 (c.st π s).mu + Matrix.toEuclideanCLM (𝕜 := ℝ) (c.st π s).A z) ∂(stdGaussian (E d))) -
        c.surr π s (WithLp.toLp 2 (c.st π s).mu)) :=
    H.shift d (df2Ext c.p c.Kt (π.g s)) (WithLp.toLp 2 (c.st π s).mu)
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (c.st π s).A) c.p.lam hl (by linarith)
  have hlo := hsi.lower
  have hle := hsi.le_ext (WithLp.toLp 2 x)
  have hR0 : 0 ≤ 2 / c.p.lam * (c.sHess π s * ((c.st π s).A * (c.st π s).Aᵀ)).trace + 2 * c.p.δe * d / c.p.lam := by
    have hS : ((c.st π s).A * (c.st π s).Aᵀ).PosSemidef := by
      rw [hI.AA, ← (Matrix.inv_eq_left_inv hI.SP)]
      exact hI.pd.inv.posSemidef
    have := trace_mul_nonneg _ _ (H.sHess_psd hs) hS
    have := H.rows.pos_de
    positivity
  have h1 := mul_le_mul_of_nonneg_left hlo (by linarith : (0 : ℝ) ≤ 1 - c.p.lam)
  have h2 : (1 - c.p.lam) * (2 / c.p.lam * (c.sHess π s * ((c.st π s).A * (c.st π s).Aᵀ)).trace +
      2 * c.p.δe * d / c.p.lam) ≤ 2 / c.p.lam * (c.sHess π s * ((c.st π s).A * (c.st π s).Aᵀ)).trace +
      2 * c.p.δe * d / c.p.lam := by nlinarith
  linarith

/-- (W1): `eReg_τ(x) ≤ sReg_τ(x) + 1 + d L/(η λ)` on `K_ε`. -/
theorem w1 (H : DetHyp c δ π m) (x : Fin d → ℝ) :
    c.eReg π (c.tau π m) x ≤ c.sReg π (c.tau π m + 1) x + (1 + d * c.p.Le / (c.p.lam * c.p.eta)) := by
  have hl := H.rows.pos_lam
  have hde := H.rows.pos_de
  unfold Df2Ctx.eReg Df2Ctx.sReg
  refine (Finset.sum_le_sum fun s hs => H.w1_round (by have := Finset.mem_range.1 hs; omega) x).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have h1 := H.trace_sum
  have h2 : ∑ _s ∈ Finset.range (c.tau π m + 1), 2 * c.p.δe * d / c.p.lam ≤ 1 := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hn := H.n_ge (le_refl (c.tau π m))
    have c2 := H.rows.c2dl
    have : ((c.tau π m + 1 : ℕ) : ℝ) * (2 * c.p.δe * d / c.p.lam) ≤ c.n * (2 * c.p.δe * d / c.p.lam) :=
      mul_le_mul_of_nonneg_right hn (by positivity)
    have e : (c.n : ℝ) * (2 * c.p.δe * d / c.p.lam) = 2 * c.p.δe * d * c.n / c.p.lam := by ring
    linarith
  linarith

end DetHyp

end AdversarialBco.Poly
