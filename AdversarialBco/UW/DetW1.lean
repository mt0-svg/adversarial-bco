/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.UW.DetAcc

@[expose] public section

/-!
# DET at T4U with sure ranges: Poly/Df2DetW1.lean on `DetHypW`
-/

open Matrix MeasureTheory ProbabilityTheory
open scoped Matrix

namespace AdversarialBco.UW

open AdversarialBco.Poly AdversarialBco.Poly.Layer2

namespace DetHypW

variable {d : ℕ} {c : Df2Ctx d} {π : Df2Path d} {m : ℕ} {ρ : RefW}

/-- Lemma LD on the run. -/
theorem ld_sum (H : DetHypW c π m ρ) :
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
theorem trace_sum (H : DetHypW c π m ρ) :
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
theorem w1_round (H : DetHypW c π m ρ) {s : ℕ} (hs : s ≤ c.tau π m) (x : Fin d → ℝ) :
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
theorem w1 (H : DetHypW c π m ρ) (x : Fin d → ℝ) :
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

end DetHypW

end AdversarialBco.UW
