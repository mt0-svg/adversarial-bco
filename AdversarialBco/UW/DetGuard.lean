/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.UW.DetOns

@[expose] public section

/-!
# DET at T4U with sure ranges: Poly/Df2DetGuard.lean on `DetHypW`
-/

open Matrix MeasureTheory ProbabilityTheory
open scoped Matrix

namespace AdversarialBco.UW

open AdversarialBco.Poly AdversarialBco.Poly.Layer2

namespace DetHypW

variable {d : ℕ} {c : Df2Ctx d} {π : Df2Path d} {m : ℕ} {ρ : RefW}

theorem P_le (H : DetHypW c π m ρ) {u : ℕ} (hu : u ≤ c.tau π m) :
    (c.p.δe⁻¹ • (1 : Matrix (Fin d) (Fin d) ℝ) - (c.st π u).P).PosSemidef :=
  psd_trans (H.stInv_le_tau u hu).pb2 (H.stInv_le_tau u hu).pbh

/-- `|u_s|² ≤ |ξ_s|²/δ_e`. -/
theorem u_sq (H : DetHypW c π m ρ) {u : ℕ} (hu : u ≤ c.tau π m) :
    c.u π u ⬝ᵥ c.u π u ≤ (π.xi u ⬝ᵥ π.xi u) / c.p.δe := by
  have hI := H.stInv_le_tau u hu
  exact u_norm _ _ _ (π.xi u) c.p.δe H.rows.pos_de hI.pd.posSemidef hI.AA hI.SP (H.P_le hu)

/-- `|Y_u| (|u_u|² + 1/δ_e) ≤ y0 (b0 + 2)/δ_e`: the clip, and the weight where `Y_u ≠ 0`. -/
theorem Y_u_sq (H : DetHypW c π m ρ) {u : ℕ} (hu : u ≤ c.tau π m) :
    |c.Y π u| * (c.u π u ⬝ᵥ c.u π u + c.p.δe⁻¹) ≤ ρ.y0 * (ρ.b0 + 2) / c.p.δe := by
  have hde := H.rows.pos_de
  have hb := H.b0_ge
  have hy := H.y0_nonneg
  by_cases hY0 : c.Y π u = 0
  · rw [hY0, abs_zero, zero_mul]; positivity
  · have hξ := H.Ywt u hu hY0
    have h1 : c.u π u ⬝ᵥ c.u π u + c.p.δe⁻¹ ≤ (ρ.b0 + 2) / c.p.δe := by
      have := (H.u_sq hu).trans (div_le_div_of_nonneg_right hξ hde.le)
      have e : (ρ.b0 + 2) / c.p.δe = (ρ.b0 + 1) / c.p.δe + c.p.δe⁻¹ := by ring
      rw [e]; linarith
    have h0 : 0 ≤ c.u π u ⬝ᵥ c.u π u + c.p.δe⁻¹ := by have := dot_self_nonneg (c.u π u); positivity
    calc |c.Y π u| * (c.u π u ⬝ᵥ c.u π u + c.p.δe⁻¹) ≤ ρ.y0 * ((ρ.b0 + 2) / c.p.δe) :=
          mul_le_mul (H.Ybd u hu) h1 h0 hy
      _ = _ := by ring

theorem moneW_nonneg (H : DetHypW c π m ρ) : 0 ≤ moneW c ρ := by
  have := H.rows.pos_lam; have := H.k0_pos; have := H.rows.pos_de; have := H.y0_nonneg; have := H.b0_ge
  unfold moneW; positivity

theorem shh_norm (H : DetHypW c π m ρ) {u : ℕ} (hu : u ≤ c.tau π m) (v : Fin d → ℝ) :
    oNorm (c.shh π u *ᵥ v) ≤ moneW c ρ * oNorm v := by
  have hI := H.stInv_le_tau u hu
  have h := rank_one_norm _ (c.u π u) v (c.p.lam * c.p.k0 * c.Y π u) c.p.δe⁻¹ hI.pd.posSemidef (H.P_le hu)
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (oNorm_nonneg' v))
  have hl := H.rows.pos_lam; have hk := H.k0_pos
  have hlk : 0 < c.p.lam * c.p.k0 := by positivity
  rw [abs_mul, abs_of_pos hlk]
  have := mul_le_mul_of_nonneg_left (H.Y_u_sq hu) hlk.le
  unfold moneW
  calc c.p.lam * c.p.k0 * |c.Y π u| * (c.u π u ⬝ᵥ c.u π u + c.p.δe⁻¹) =
      c.p.lam * c.p.k0 * (|c.Y π u| * (c.u π u ⬝ᵥ c.u π u + c.p.δe⁻¹)) := by ring
    _ ≤ c.p.lam * c.p.k0 * (ρ.y0 * (ρ.b0 + 2) / c.p.δe) := this
    _ = _ := by ring

theorem sqrt_k0 (H : DetHypW c π m ρ) : Real.sqrt c.p.k0 = (1 - c.p.lam)⁻¹ := by
  rw [H.k0, Real.sqrt_inv, Real.sqrt_sq]; have := H.rows.lam_le; linarith

/-- `|ĝ_u| ≤ y0 κ₀^{1/2} ((b0 + 1)/δ_e)^{1/2}`. -/
theorem ghat_norm (H : DetHypW c π m ρ) {u : ℕ} (hu : u ≤ c.tau π m) :
    oNorm (c.ghat π u) ≤ ρ.y0 * Real.sqrt c.p.k0 * Real.sqrt ((ρ.b0 + 1) / c.p.δe) := by
  have hl := H.rows.lam_le
  have h1l : 0 < 1 - c.p.lam := by linarith
  have e : oNorm (c.ghat π u) = |c.Y π u| * ((1 - c.p.lam)⁻¹ * oNorm (c.u π u)) := by
    unfold Df2Ctx.ghat
    rw [oNorm_smul', abs_div, abs_of_pos h1l, div_eq_mul_inv, mul_assoc]
  rw [e, H.sqrt_k0]
  by_cases hY0 : c.Y π u = 0
  · rw [hY0, abs_zero, zero_mul]; have := H.y0_nonneg; positivity
  · have hun : oNorm (c.u π u) ≤ Real.sqrt ((ρ.b0 + 1) / c.p.δe) :=
      Real.sqrt_le_sqrt ((H.u_sq hu).trans (div_le_div_of_nonneg_right (H.Ywt u hu hY0) H.rows.pos_de.le))
    have : (1 - c.p.lam)⁻¹ * oNorm (c.u π u) ≤ (1 - c.p.lam)⁻¹ * Real.sqrt ((ρ.b0 + 1) / c.p.δe) :=
      mul_le_mul_of_nonneg_left hun (by positivity)
    calc |c.Y π u| * ((1 - c.p.lam)⁻¹ * oNorm (c.u π u))
        ≤ ρ.y0 * ((1 - c.p.lam)⁻¹ * Real.sqrt ((ρ.b0 + 1) / c.p.δe)) :=
          mul_le_mul (H.Ybd u hu) this (mul_nonneg (inv_nonneg.2 h1l.le) (oNorm_nonneg' _)) H.y0_nonneg
      _ = _ := by ring

/-! ### The sums of round `s` -/

theorem Pn_sum (H : DetHypW c π m ρ) {s : ℕ} (hs : s ≤ c.tau π m) :
    c.Pn π s = (c.st π 0).P + ∑ u ∈ Finset.range (s + 1), (c.p.eta * c.p.kap) • c.shh π u := by
  rw [Df2Ctx.Pn_eq, (H.stInv_le_tau s hs).Pf, ← Finset.smul_sum, Finset.sum_range_succ, smul_add, add_assoc]

theorem bn_sum (H : DetHypW c π m ρ) {s : ℕ} (hs : s ≤ c.tau π m) :
    c.bn π s = ∑ u ∈ Finset.range (s + 1), ((c.p.eta * c.p.kap) • c.shh π u) *ᵥ (c.st π u).mu := by
  simp only [smul_mulVec]
  rw [Df2Ctx.bn_eq, (H.stInv_le_tau s hs).bf, ← Finset.smul_sum, Finset.sum_range_succ, smul_add]

theorem Gn_sum (H : DetHypW c π m ρ) {s : ℕ} (hs : s ≤ c.tau π m) :
    c.Gn π s = ∑ u ∈ Finset.range (s + 1), c.ghat π u := by
  unfold Df2Ctx.Gn; rw [(H.stInv_le_tau s hs).G, Finset.sum_range_succ]

theorem grad_arith' (H : DetHypW c π m ρ) :
    c.n * (c.p.eta * c.p.kap * moneW c ρ) ≤ 1 / (4 * c.p.δe ^ 2) ∧
      c.p.sig2⁻¹ + 2 * (c.n * (c.p.eta * c.p.kap * moneW c ρ)) ≤ 1 / c.p.δe ^ 2 := by
  refine ⟨H.gM, ?_⟩
  have h1 := H.gM; have h2 := H.gS
  have e : 1 / c.p.δe ^ 2 = 1 / (2 * c.p.δe ^ 2) + 2 * (1 / (4 * c.p.δe ^ 2)) := by ring
  rw [e]; linarith

/-- The sum `η κ ∑_{u ≤ s} ‖ŝ''_u‖` is at most `n η κ M₁`. -/
theorem sum_M (H : DetHypW c π m ρ) {s : ℕ} (hs : s ≤ c.tau π m) :
    ∑ _u ∈ Finset.range (s + 1), c.p.eta * c.p.kap * moneW c ρ ≤ c.n * (c.p.eta * c.p.kap * moneW c ρ) := by
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hM := H.moneW_nonneg
  exact mul_le_mul_of_nonneg_right (H.n_ge hs) (by have := H.kap_pos; positivity)

/-- Lemma IB2 (ii): the gradient of `Φ'` at a point of `B_R` is at most `R/δ_e²`. -/
theorem grad_le (H : DetHypW c π m ρ) {s : ℕ} (hs : s ≤ c.tau π m) {y : Fin d → ℝ} (hy : oNorm y ≤ c.p.R) :
    oNorm (c.Pn π s *ᵥ y - c.bn π s) ≤ c.p.R / c.p.δe ^ 2 := by
  have hek := H.kap_pos
  have hM := H.moneW_nonneg
  have hR : 0 ≤ c.p.R := by linarith [H.rows.one_le_R]
  rw [H.Pn_sum hs, H.bn_sum hs]
  have h := grad_bound (s + 1) (c.st π 0).P (fun u => (c.p.eta * c.p.kap) • c.shh π u) (fun u => (c.st π u).mu) y
    c.p.R c.p.sig2⁻¹ (fun _ => c.p.eta * c.p.kap * moneW c ρ) hy
    (fun u hu => H.norm_le_of_keps (H.stInv_le_tau u (by omega)).mu)
    (fun v => by
      show oNorm ((c.p.sig2⁻¹ • (1 : Matrix (Fin d) (Fin d) ℝ)) *ᵥ v) ≤ _
      rw [smul_mulVec, one_mulVec, oNorm_smul', abs_of_pos (inv_pos.2 H.rows.pos_sig2)])
    (fun u hu v => by
      rw [smul_mulVec, oNorm_smul', abs_of_pos hek]
      have := mul_le_mul_of_nonneg_left (H.shh_norm (show u ≤ c.tau π m by omega) v) hek.le
      linarith)
    (inv_pos.2 H.rows.pos_sig2).le (fun _ _ => by positivity)
  refine h.trans ?_
  have h2 := H.sum_M hs
  have h3 := (H.grad_arith').2
  calc c.p.sig2⁻¹ * c.p.R + 2 * c.p.R * ∑ _u ∈ Finset.range (s + 1), c.p.eta * c.p.kap * moneW c ρ
      ≤ c.p.R * (c.p.sig2⁻¹ + 2 * (c.n * (c.p.eta * c.p.kap * moneW c ρ))) := by nlinarith
    _ ≤ c.p.R * (1 / c.p.δe ^ 2) := mul_le_mul_of_nonneg_left h3 hR
    _ = _ := by ring

/-- `Σ'` is positive semidefinite and at most `I/δ_e`. -/
theorem Sn_props (H : DetHypW c π m ρ) {s : ℕ} (hs : s ≤ c.tau π m) :
    (c.Sn π s).PosSemidef ∧ (c.p.δe⁻¹ • (1 : Matrix (Fin d) (Fin d) ℝ) - c.Sn π s).PosSemidef ∧
      (c.Pn π s - c.p.δe • (1 : Matrix (Fin d) (Fin d) ℝ)).PosSemidef := by
  obtain ⟨h3a, h3b, -, -⟩ := H.c3_le_tau hs
  obtain ⟨hpd, hSP, -, -⟩ := H.r1_le_tau hs
  have hinv : (c.Pn π s)⁻¹ = c.Sn π s := Matrix.inv_eq_left_inv hSP
  have hlow := psd_trans h3b h3a
  refine ⟨hinv ▸ hpd.inv.posSemidef, ?_, hlow⟩
  have := inv_antitone _ _ (Matrix.PosDef.one.smul H.rows.pos_de) hpd hlow
  rwa [inv_smul_one H.rows.pos_de.ne', hinv] at this

/-- Lemma Z: `|z_s| ≤ R/δ_e³`, so the guard Z does not act at a round `s ≤ τ`. -/
theorem not_gdZ (H : DetHypW c π m ρ) {s : ℕ} (hs : s ≤ c.tau π m) : ¬ c.GdZ π s := by
  unfold Df2Ctx.GdZ
  rw [not_lt]
  have hde := H.rows.pos_de
  have hek := H.kap_pos
  have hη := H.rows.pos_eta
  have hR1 := H.rows.one_le_R
  obtain ⟨-, -, hlow⟩ := H.Sn_props hs
  have hSP := (H.r1_le_tau hs).2.1
  have hS := inv_norm_le _ _ c.p.δe hde hlow hSP (c.bn π s - (c.p.eta / 2) • c.Gn π s)
  -- the size of `b`
  have hb : oNorm (c.bn π s) ≤ c.p.R / (4 * c.p.δe ^ 2) := by
    rw [H.bn_sum hs]
    refine (oNorm_sum_le' _ _).trans ?_
    have hterm : ∀ u ∈ Finset.range (s + 1), oNorm (((c.p.eta * c.p.kap) • c.shh π u) *ᵥ (c.st π u).mu) ≤
        c.p.eta * c.p.kap * moneW c ρ * c.p.R := by
      intro u hu
      have hut : u ≤ c.tau π m := by have := Finset.mem_range.1 hu; omega
      rw [smul_mulVec, oNorm_smul', abs_of_pos hek]
      have h1 := (H.shh_norm hut _).trans (mul_le_mul_of_nonneg_left
        (H.norm_le_of_keps (H.stInv_le_tau u hut).mu) H.moneW_nonneg)
      have := mul_le_mul_of_nonneg_left h1 hek.le
      linarith
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have h1 := H.grad_arith'.1
    have h2 : ((s + 1 : ℕ) : ℝ) ≤ c.n := H.n_ge hs
    have hM := H.moneW_nonneg
    calc ((s + 1 : ℕ) : ℝ) * (c.p.eta * c.p.kap * moneW c ρ * c.p.R)
        ≤ c.n * (c.p.eta * c.p.kap * moneW c ρ) * c.p.R := by
          rw [← mul_assoc, ← mul_assoc]
          apply mul_le_mul_of_nonneg_right _ (by linarith)
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_right h2 (by positivity)
      _ ≤ 1 / (4 * c.p.δe ^ 2) * c.p.R := mul_le_mul_of_nonneg_right h1 (by linarith)
      _ = _ := by ring
  -- the size of `(η/2) Ĝ`
  have hG : c.p.eta / 2 * oNorm (c.Gn π s) ≤ 3 / 4 * c.p.R / c.p.δe ^ 2 := by
    rw [H.Gn_sum hs]
    have h1 : oNorm (∑ u ∈ Finset.range (s + 1), c.ghat π u) ≤
        c.n * (ρ.y0 * Real.sqrt c.p.k0 * Real.sqrt ((ρ.b0 + 1) / c.p.δe)) := by
      refine (oNorm_sum_le' _ _).trans ((Finset.sum_le_sum fun u hu => H.ghat_norm
        (by have := Finset.mem_range.1 hu; omega)).trans ?_)
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (H.n_ge hs) (by have := H.y0_nonneg; positivity)
    calc c.p.eta / 2 * oNorm (∑ u ∈ Finset.range (s + 1), c.ghat π u)
        ≤ c.p.eta / 2 * (c.n * (ρ.y0 * Real.sqrt c.p.k0 * Real.sqrt ((ρ.b0 + 1) / c.p.δe))) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ _ := H.gZ
  have hsum : oNorm (c.bn π s - (c.p.eta / 2) • c.Gn π s) ≤ c.p.R / c.p.δe ^ 2 := by
    refine (oNorm_sub_le' _ _).trans ?_
    rw [oNorm_smul', abs_of_pos (by positivity)]
    have : c.p.R / (4 * c.p.δe ^ 2) + 3 / 4 * c.p.R / c.p.δe ^ 2 = c.p.R / c.p.δe ^ 2 := by field_simp; ring
    linarith
  calc oNorm (c.zz π s) ≤ oNorm (c.bn π s - (c.p.eta / 2) • c.Gn π s) / c.p.δe := hS
    _ ≤ c.p.R / c.p.δe ^ 2 / c.p.δe := div_le_div_of_nonneg_right hsum hde.le
    _ = c.p.R / c.p.δe ^ 3 := by field_simp

/-- The guard W does not act at a round `s ≤ τ`: `|w_μ| ≤ R + η (16 d n L/δ_e)^{1/2}`. -/
theorem not_gdW (H : DetHypW c π m ρ) {s : ℕ} (hs : s ≤ c.tau π m) : ¬ c.GdW π s := by
  unfold Df2Ctx.GdW
  rw [not_lt, H.wmu_eq hs]
  have hde := H.rows.pos_de
  have hη := H.rows.pos_eta
  obtain ⟨hS, hSD, -⟩ := H.Sn_props hs
  have h1 := mulVec_sq_le _ _ hS hSD (c.ghat π s)
  rw [H.ghat_sq hs] at h1
  obtain ⟨-, hq⟩ := H.aq hs
  have hk := H.k0_pos
  have hb := H.b0_ge
  have hY2 : c.Y π s ^ 2 ≤ ρ.y0 ^ 2 := by
    have := H.Ybd s hs
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) this 2
  have hξ := H.Y_xi hs
  have h2 : c.p.k0 * c.Y π s ^ 2 * (π.xi s ⬝ᵥ π.xi s) / c.qq π s ≤ 4 * c.p.k0 * ρ.y0 ^ 2 * (ρ.b0 + 1) := by
    rw [div_le_iff₀ (by linarith)]
    have h4 : c.p.k0 * c.Y π s ^ 2 * (π.xi s ⬝ᵥ π.xi s) ≤ c.p.k0 * (ρ.y0 ^ 2 * (ρ.b0 + 1)) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (hξ.trans (mul_le_mul_of_nonneg_right hY2 (by linarith))) hk.le
    have : 0 ≤ c.p.k0 * ρ.y0 ^ 2 * (ρ.b0 + 1) := by positivity
    nlinarith
  have hsq : (c.Sn π s *ᵥ c.ghat π s) ⬝ᵥ (c.Sn π s *ᵥ c.ghat π s) ≤ 16 * d * c.n * c.p.Le / c.p.δe := by
    calc _ ≤ c.p.δe⁻¹ * (c.p.k0 * c.Y π s ^ 2 * (π.xi s ⬝ᵥ π.xi s) / c.qq π s) := h1
      _ ≤ c.p.δe⁻¹ * (4 * c.p.k0 * ρ.y0 ^ 2 * (ρ.b0 + 1)) := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ ≤ c.p.δe⁻¹ * (16 * d * c.n * c.p.Le) := mul_le_mul_of_nonneg_left H.gW (by positivity)
      _ = _ := by ring
  have hn : oNorm (c.Sn π s *ᵥ c.ghat π s) ≤ Real.sqrt (16 * d * c.n * c.p.Le / c.p.δe) := Real.sqrt_le_sqrt hsq
  refine (oNorm_sub_le' _ _).trans ?_
  rw [oNorm_smul', abs_of_pos hη]
  have := H.norm_le_of_keps (H.stInv_le_tau s hs).mu
  have := mul_le_mul_of_nonneg_left hn hη.le
  linarith

end DetHypW

end AdversarialBco.UW
