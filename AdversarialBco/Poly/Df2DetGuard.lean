/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.Df2DetOns

@[expose] public section

/-!
# DET, the sizes on the event G and the guards Z and W

For a round `s ≤ τ`, on G: `|u_s|² ≤ X/δ_e` with `X = (32/9) d log(1/δ_e)`, `‖ŝ''_s‖ ≤ M₁`,
`|ĝ_s| ≤ (L/(2ε)) κ₀^{1/2} (X/δ_e)^{1/2}`; the gradient of `Φ'` at a point of `B_R` is at most `R/δ_e²`
(Lemma D.17 (ii)); Lemma D.18 (`|z_s| ≤ R/δ_e³`, the guard Z does not act) and the bound of the
Newton point of line μ (the guard W does not act).
-/

open Matrix MeasureTheory
open scoped Matrix

namespace AdversarialBco.Poly

open Layer2

theorem oNorm_add_le' {d : ℕ} (u v : Fin d → ℝ) : oNorm (u + v) ≤ oNorm u + oNorm v :=
  (oNorm_tri u v 0 ∅ fun _ => 0).1

theorem oNorm_smul' {d : ℕ} (a : ℝ) (u : Fin d → ℝ) : oNorm (a • u) = |a| * oNorm u :=
  (oNorm_tri u u a ∅ fun _ => 0).2.1

theorem oNorm_sum_le' {d : ℕ} (F : Finset ℕ) (w : ℕ → Fin d → ℝ) :
    oNorm (∑ i ∈ F, w i) ≤ ∑ i ∈ F, oNorm (w i) :=
  (oNorm_tri (0 : Fin d → ℝ) 0 0 F w).2.2

theorem oNorm_sub_le' {d : ℕ} (u v : Fin d → ℝ) : oNorm (u - v) ≤ oNorm u + oNorm v := by
  have := oNorm_add_le' u ((-1 : ℝ) • v)
  rwa [oNorm_smul', abs_neg, abs_one, one_mul, neg_one_smul, ← sub_eq_add_neg] at this

theorem oNorm_nonneg' {d : ℕ} (v : Fin d → ℝ) : 0 ≤ oNorm v := Real.sqrt_nonneg _

namespace Df2Ctx

variable {d : ℕ} (c : Df2Ctx d)

/-- `X = (32/9) d log(1/δ_e)`, the level of `|ξ|²` on G. -/
noncomputable def Xg : ℝ := 32 / 9 * d * Real.log (1 / c.p.δe)

/-- `M₁ = λ κ₀ (L/(2ε)) (X + 1)/δ_e`, the bound of `‖ŝ''_u‖` on G. -/
noncomputable def Mone : ℝ := c.p.lam * c.p.k0 * (c.p.Le / (2 * c.p.eps)) * (c.Xg + 1) / c.p.δe

end Df2Ctx

namespace DetHyp

variable {d : ℕ} {c : Df2Ctx d} {δ : ℝ} {π : Df2Path d} {m : ℕ}

theorem Xg_nonneg (H : DetHyp c δ π m) : 0 ≤ c.Xg := by
  have := H.x_ge; unfold Df2Ctx.Xg; positivity

theorem P_le (H : DetHyp c δ π m) {u : ℕ} (hu : u ≤ c.tau π m) :
    (c.p.δe⁻¹ • (1 : Matrix (Fin d) (Fin d) ℝ) - (c.st π u).P).PosSemidef :=
  psd_trans (H.stInv_le_tau u hu).pb2 (H.stInv_le_tau u hu).pbh

theorem u_sq (H : DetHyp c δ π m) {u : ℕ} (hu : u ≤ c.tau π m) : c.u π u ⬝ᵥ c.u π u ≤ c.Xg / c.p.δe := by
  have hI := H.stInv_le_tau u hu
  exact (u_norm _ _ _ (π.xi u) c.p.δe H.rows.pos_de hI.pd.posSemidef hI.AA hI.SP (H.P_le hu)).trans
    (div_le_div_of_nonneg_right (H.xibd hu) H.rows.pos_de.le)

theorem shh_norm (H : DetHyp c δ π m) {u : ℕ} (hu : u ≤ c.tau π m) (v : Fin d → ℝ) :
    oNorm (c.shh π u *ᵥ v) ≤ c.Mone * oNorm v := by
  have hI := H.stInv_le_tau u hu
  have h := rank_one_norm _ (c.u π u) v (c.p.lam * c.p.k0 * c.Y π u) c.p.δe⁻¹ hI.pd.posSemidef (H.P_le hu)
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (oNorm_nonneg' v))
  have hl := H.rows.pos_lam; have hk := H.k0_pos; have hde := H.rows.pos_de; have hX := H.Xg_nonneg
  have hY := H.ybd hu
  have huu := H.u_sq hu
  have h0 : 0 ≤ c.u π u ⬝ᵥ c.u π u := dot_self_nonneg _
  rw [abs_mul, abs_of_pos (by positivity : 0 < c.p.lam * c.p.k0)]
  unfold Df2Ctx.Mone
  have e : c.p.lam * c.p.k0 * (c.p.Le / (2 * c.p.eps)) * (c.Xg + 1) / c.p.δe =
      c.p.lam * c.p.k0 * (c.p.Le / (2 * c.p.eps)) * (c.Xg / c.p.δe + c.p.δe⁻¹) := by field_simp
  rw [e]
  apply mul_le_mul (mul_le_mul_of_nonneg_left hY (by positivity)) (by linarith) (by positivity)
  have := H.rows.pos_eps; have := H.Le_pos; positivity

theorem sqrt_k0 (H : DetHyp c δ π m) : Real.sqrt c.p.k0 = (1 - c.p.lam)⁻¹ := by
  rw [H.k0, Real.sqrt_inv, Real.sqrt_sq]; have := H.rows.lam_le; linarith

theorem ghat_norm (H : DetHyp c δ π m) {u : ℕ} (hu : u ≤ c.tau π m) :
    oNorm (c.ghat π u) ≤ c.p.Le / (2 * c.p.eps) * Real.sqrt c.p.k0 * Real.sqrt (c.Xg / c.p.δe) := by
  have hl := H.rows.lam_le
  have h1l : 0 < 1 - c.p.lam := by linarith
  unfold Df2Ctx.ghat
  rw [oNorm_smul', abs_div, abs_of_pos h1l, H.sqrt_k0, div_eq_mul_inv, mul_assoc]
  have hY := H.ybd hu
  have hun : oNorm (c.u π u) ≤ Real.sqrt (c.Xg / c.p.δe) := Real.sqrt_le_sqrt (H.u_sq hu)
  have : (1 - c.p.lam)⁻¹ * oNorm (c.u π u) ≤ (1 - c.p.lam)⁻¹ * Real.sqrt (c.Xg / c.p.δe) :=
    mul_le_mul_of_nonneg_left hun (by positivity)
  calc |c.Y π u| * ((1 - c.p.lam)⁻¹ * oNorm (c.u π u))
      ≤ c.p.Le / (2 * c.p.eps) * ((1 - c.p.lam)⁻¹ * Real.sqrt (c.Xg / c.p.δe)) :=
        mul_le_mul hY this (mul_nonneg (inv_nonneg.2 h1l.le) (oNorm_nonneg' _))
          (by have := H.rows.pos_eps; have := H.Le_pos; positivity)
    _ = _ := by ring

/-! ### The sums of round `s` -/

theorem Pn_sum (H : DetHyp c δ π m) {s : ℕ} (hs : s ≤ c.tau π m) :
    c.Pn π s = (c.st π 0).P + ∑ u ∈ Finset.range (s + 1), (c.p.eta * c.p.kap) • c.shh π u := by
  rw [Df2Ctx.Pn_eq, (H.stInv_le_tau s hs).Pf, ← Finset.smul_sum, Finset.sum_range_succ, smul_add, add_assoc]

theorem bn_sum (H : DetHyp c δ π m) {s : ℕ} (hs : s ≤ c.tau π m) :
    c.bn π s = ∑ u ∈ Finset.range (s + 1), ((c.p.eta * c.p.kap) • c.shh π u) *ᵥ (c.st π u).mu := by
  simp only [smul_mulVec]
  rw [Df2Ctx.bn_eq, (H.stInv_le_tau s hs).bf, ← Finset.smul_sum, Finset.sum_range_succ, smul_add]

theorem Gn_sum (H : DetHyp c δ π m) {s : ℕ} (hs : s ≤ c.tau π m) :
    c.Gn π s = ∑ u ∈ Finset.range (s + 1), c.ghat π u := by
  unfold Df2Ctx.Gn; rw [(H.stInv_le_tau s hs).G, Finset.sum_range_succ]

theorem grad_arith' (H : DetHyp c δ π m) :
    c.n * (c.p.eta * c.p.kap * c.Mone) ≤ 1 / (4 * c.p.δe ^ 2) ∧
      c.p.sig2⁻¹ + 2 * (c.n * (c.p.eta * c.p.kap * c.Mone)) ≤ 1 / c.p.δe ^ 2 := by
  have hL : 504 ≤ c.p.Le := by rw [H.Le_eq]; linarith [H.x_ge]
  have hx : Real.log (1 / c.p.δe) = c.p.Le / 36 := by rw [H.Le_eq]; ring
  have := grad_arith c.p.eta c.p.kap c.p.lam c.p.k0 c.p.Le c.p.eps d (Real.log (1 / c.p.δe)) c.p.δe c.n c.p.sig2
    H.rows.pos_eta H.kap H.rows.pos_lam H.k0_pos H.rows.k0_le hL H.rows.pos_eps (by exact_mod_cast H.hd) hx
    H.rows.pos_de H.rows.de_lt (by exact_mod_cast H.hn) H.rows.pos_sig2 H.rows.r6a H.rows.c500 H.rows.c4
  unfold Df2Ctx.Mone Df2Ctx.Xg
  exact this

/-- The sum `η κ ∑_{u ≤ s} ‖ŝ''_u‖` is at most `n η κ M₁`. -/
theorem sum_M (H : DetHyp c δ π m) {s : ℕ} (hs : s ≤ c.tau π m) :
    ∑ _u ∈ Finset.range (s + 1), c.p.eta * c.p.kap * c.Mone ≤ c.n * (c.p.eta * c.p.kap * c.Mone) := by
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hM : 0 ≤ c.Mone := by
    have := H.rows.pos_lam; have := H.k0_pos; have := H.rows.pos_eps; have := H.Le_pos; have := H.Xg_nonneg
    have := H.rows.pos_de; unfold Df2Ctx.Mone; positivity
  exact mul_le_mul_of_nonneg_right (H.n_ge hs) (by have := H.kap_pos; positivity)

theorem Mone_nonneg (H : DetHyp c δ π m) : 0 ≤ c.Mone := by
  have := H.rows.pos_lam; have := H.k0_pos; have := H.rows.pos_eps; have := H.Le_pos; have := H.Xg_nonneg
  have := H.rows.pos_de; unfold Df2Ctx.Mone; positivity

/-- Lemma D.17 (ii): the gradient of `Φ'` at a point of `B_R` is at most `R/δ_e²`. -/
theorem grad_le (H : DetHyp c δ π m) {s : ℕ} (hs : s ≤ c.tau π m) {y : Fin d → ℝ} (hy : oNorm y ≤ c.p.R) :
    oNorm (c.Pn π s *ᵥ y - c.bn π s) ≤ c.p.R / c.p.δe ^ 2 := by
  have hek := H.kap_pos
  have hM := H.Mone_nonneg
  have hR : 0 ≤ c.p.R := by linarith [H.rows.one_le_R]
  rw [H.Pn_sum hs, H.bn_sum hs]
  have h := grad_bound (s + 1) (c.st π 0).P (fun u => (c.p.eta * c.p.kap) • c.shh π u) (fun u => (c.st π u).mu) y
    c.p.R c.p.sig2⁻¹ (fun _ => c.p.eta * c.p.kap * c.Mone) hy
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
  calc c.p.sig2⁻¹ * c.p.R + 2 * c.p.R * ∑ _u ∈ Finset.range (s + 1), c.p.eta * c.p.kap * c.Mone
      ≤ c.p.R * (c.p.sig2⁻¹ + 2 * (c.n * (c.p.eta * c.p.kap * c.Mone))) := by nlinarith
    _ ≤ c.p.R * (1 / c.p.δe ^ 2) := mul_le_mul_of_nonneg_left h3 hR
    _ = _ := by ring

/-- `Σ'` is positive semidefinite and at most `I/δ_e`. -/
theorem Sn_props (H : DetHyp c δ π m) {s : ℕ} (hs : s ≤ c.tau π m) :
    (c.Sn π s).PosSemidef ∧ (c.p.δe⁻¹ • (1 : Matrix (Fin d) (Fin d) ℝ) - c.Sn π s).PosSemidef ∧
      (c.Pn π s - c.p.δe • (1 : Matrix (Fin d) (Fin d) ℝ)).PosSemidef := by
  obtain ⟨h3a, h3b, -, -⟩ := H.c3_le_tau hs
  obtain ⟨hpd, hSP, -, -⟩ := H.r1_le_tau hs
  have hinv : (c.Pn π s)⁻¹ = c.Sn π s := Matrix.inv_eq_left_inv hSP
  have hlow := psd_trans h3b h3a
  refine ⟨hinv ▸ hpd.inv.posSemidef, ?_, hlow⟩
  have := inv_antitone _ _ (Matrix.PosDef.one.smul H.rows.pos_de) hpd hlow
  rwa [inv_smul_one H.rows.pos_de.ne', hinv] at this

/-- Lemma D.18: `|z_s| ≤ R/δ_e³`, so the guard Z does not act at a round `s ≤ τ`. -/
theorem not_gdZ (H : DetHyp c δ π m) {s : ℕ} (hs : s ≤ c.tau π m) : ¬ c.GdZ π s := by
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
        c.p.eta * c.p.kap * c.Mone * c.p.R := by
      intro u hu
      have hut : u ≤ c.tau π m := by have := Finset.mem_range.1 hu; omega
      rw [smul_mulVec, oNorm_smul', abs_of_pos hek]
      have h1 := (H.shh_norm hut _).trans (mul_le_mul_of_nonneg_left
        (H.norm_le_of_keps (H.stInv_le_tau u hut).mu) H.Mone_nonneg)
      have := mul_le_mul_of_nonneg_left h1 hek.le
      linarith
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have h1 := H.grad_arith'.1
    have h2 : ((s + 1 : ℕ) : ℝ) ≤ c.n := H.n_ge hs
    have hM := H.Mone_nonneg
    calc ((s + 1 : ℕ) : ℝ) * (c.p.eta * c.p.kap * c.Mone * c.p.R)
        ≤ c.n * (c.p.eta * c.p.kap * c.Mone) * c.p.R := by
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
        c.n * (c.p.Le / (2 * c.p.eps) * Real.sqrt c.p.k0 * Real.sqrt (c.Xg / c.p.δe)) := by
      refine (oNorm_sum_le' _ _).trans ((Finset.sum_le_sum fun u hu => H.ghat_norm
        (by have := Finset.mem_range.1 hu; omega)).trans ?_)
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (H.n_ge hs) (by have := H.rows.pos_eps; have := H.Le_pos; positivity)
    have hz := z_arith c.p.eta c.p.Le c.p.eps c.p.k0 c.Xg c.p.δe c.n d (Real.log (1 / c.p.δe)) c.p.R hη
      H.rows.eta_le hR1 H.rows.pos_eps H.rows.r14 (by exact_mod_cast H.hn) (by exact_mod_cast H.hd)
      (by linarith [H.x_ge]) H.k0_pos hde rfl H.Le_eq (by have := H.rows.cz; simp only [df2C0] at this; exact this)
    calc c.p.eta / 2 * oNorm (∑ u ∈ Finset.range (s + 1), c.ghat π u)
        ≤ c.p.eta / 2 * (c.n * (c.p.Le / (2 * c.p.eps) * Real.sqrt c.p.k0 * Real.sqrt (c.Xg / c.p.δe))) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ _ := hz
  have hsum : oNorm (c.bn π s - (c.p.eta / 2) • c.Gn π s) ≤ c.p.R / c.p.δe ^ 2 := by
    refine (oNorm_sub_le' _ _).trans ?_
    rw [oNorm_smul', abs_of_pos (by positivity)]
    have : c.p.R / (4 * c.p.δe ^ 2) + 3 / 4 * c.p.R / c.p.δe ^ 2 = c.p.R / c.p.δe ^ 2 := by field_simp; ring
    linarith
  calc oNorm (c.zz π s) ≤ oNorm (c.bn π s - (c.p.eta / 2) • c.Gn π s) / c.p.δe := hS
    _ ≤ c.p.R / c.p.δe ^ 2 / c.p.δe := div_le_div_of_nonneg_right hsum hde.le
    _ = c.p.R / c.p.δe ^ 3 := by field_simp

/-- The guard W does not act at a round `s ≤ τ`: `|w_μ| ≤ R + η (16 d n L/δ_e)^{1/2}`. -/
theorem not_gdW (H : DetHyp c δ π m) {s : ℕ} (hs : s ≤ c.tau π m) : ¬ c.GdW π s := by
  unfold Df2Ctx.GdW
  rw [not_lt, H.wmu_eq hs]
  have hde := H.rows.pos_de
  have hη := H.rows.pos_eta
  obtain ⟨hS, hSD, -⟩ := H.Sn_props hs
  have h1 := mulVec_sq_le _ _ hS hSD (c.ghat π s)
  rw [H.ghat_sq hs] at h1
  obtain ⟨-, hq⟩ := H.aq hs
  have hY2 : c.Y π s ^ 2 ≤ 22 * c.n :=
    le_trans (Finset.single_le_sum (f := fun u => c.Y π u ^ 2) (fun _ _ => sq_nonneg _)
      (Finset.mem_range.2 (Nat.lt_succ_of_le hs))) H.evY
  have hξ := H.xibd hs
  have hξ0 := dot_self_nonneg (π.xi s)
  have hk := H.k0_pos
  have h2 : c.p.k0 * c.Y π s ^ 2 * (π.xi s ⬝ᵥ π.xi s) / c.qq π s ≤ 4 * c.p.k0 * c.Y π s ^ 2 * c.Xg := by
    rw [div_le_iff₀ (by linarith)]
    have : c.p.k0 * c.Y π s ^ 2 * (π.xi s ⬝ᵥ π.xi s) ≤ c.p.k0 * c.Y π s ^ 2 * c.Xg :=
      mul_le_mul_of_nonneg_left hξ (by positivity)
    have : 0 ≤ c.p.k0 * c.Y π s ^ 2 * c.Xg := by have := H.Xg_nonneg; positivity
    nlinarith
  have hX : c.Xg = 32 / 9 * d * (c.p.Le / 36) := by
    unfold Df2Ctx.Xg; rw [H.Le_eq]; ring
  have h3 := t2_arith c.p.δe c.p.k0 (c.Y π s ^ 2) c.Xg d c.n c.p.Le hde hk H.rows.k0_le (sq_nonneg _) hY2 hX
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) H.Le_pos.le
  have hsq : (c.Sn π s *ᵥ c.ghat π s) ⬝ᵥ (c.Sn π s *ᵥ c.ghat π s) ≤ 16 * d * c.n * c.p.Le / c.p.δe := by
    calc _ ≤ c.p.δe⁻¹ * (c.p.k0 * c.Y π s ^ 2 * (π.xi s ⬝ᵥ π.xi s) / c.qq π s) := h1
      _ ≤ c.p.δe⁻¹ * (4 * c.p.k0 * c.Y π s ^ 2 * c.Xg) := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ ≤ _ := h3
  have hn : oNorm (c.Sn π s *ᵥ c.ghat π s) ≤ Real.sqrt (16 * d * c.n * c.p.Le / c.p.δe) := Real.sqrt_le_sqrt hsq
  refine (oNorm_sub_le' _ _).trans ?_
  rw [oNorm_smul', abs_of_pos hη]
  have := H.norm_le_of_keps (H.stInv_le_tau s hs).mu
  have := mul_le_mul_of_nonneg_left hn hη.le
  linarith

end DetHyp

end AdversarialBco.Poly
