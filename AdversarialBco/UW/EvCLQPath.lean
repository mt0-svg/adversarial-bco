/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.UW.SKpRound

@[expose] public section

/-!
# Event (c) of Theorem UW on a path

Theorem U's path lemmas of event (c) (Poly/Df2EvSILQ.lean) on any context with `DetBase`, with the sure ranges of
the weighted path in place of the bounds of event (a): on `pathW c b0 y0 π`, `|Y_s| ≤ y0` and `|ξ_s|² ≤ b0 + 1`
where `Y_s ≠ 0` (`Y_sure`).

* `lq_qE`: `|w - μ_s|²_{P_s} ≤ lvQ` for `w` within `δ_e⁴` of a point of `S_t`;
* `lq_varE`: the variance of (c) at `w` sums to at most `lvVc` up to `t ≤ τ`;
* `lq_rangeE`: `|Y_s φ_L(w)| ≤ y0 κ₀^{1/2} ((b0 + 1) lvQ)^{1/2}`, `sGrad_dotE`: `|⟨s'_s, v⟩| ≤ (8/ε) |v|`;
* `lq_disc_pathE`: the sums at `y` and at `w` differ by at most `n lvGc δ_e⁴`.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped Matrix

namespace AdversarialBco.UW

open AdversarialBco.Poly AdversarialBco.Poly.Layer2

variable {d : ℕ}

/-- On a round of the weighted epoch whose mode runs, `|Y_s| ≤ y0`, and `|ξ_s|² ≤ b0 + 1` where `Y_s ≠ 0`. -/
theorem Y_sure (c : Df2Ctx d) (b0 y0 : ℝ) (π : Df2Path d) (s : ℕ) (hy0 : 0 ≤ y0)
    (h : c.mode (pathW c b0 y0 π) s = .run (c.st (pathW c b0 y0 π) s)) :
    |c.Y (pathW c b0 y0 π) s| ≤ y0 ∧ (c.Y (pathW c b0 y0 π) s ≠ 0 → π.xi s ⬝ᵥ π.xi s ≤ b0 + 1) := by
  rw [mode_pathW] at h
  rw [Y_pathW c b0 y0 π s _ h]
  obtain ⟨h1, -, h3, -⟩ := obsW_sure hy0 b0 (π.xi s)
    (c.pip (pathW c b0 y0 π) s * (π.g s (WithLp.toLp 2 (c.play (pathW c b0 y0 π) s)) + π.e s) +
      2 * (c.pip (pathW c b0 y0 π) s - 1) / c.p.eps)
  refine ⟨h1, fun hne => ?_⟩
  by_contra hlt
  push Not at hlt
  exact hne (h3 hlt.le)

section path

variable {c : Df2Ctx d} {δ : ℝ} {π : Df2Path d} {m : ℕ}

theorem sqrt_k0E (H : DetBase c δ π m) : Real.sqrt c.p.k0 = (1 - c.p.lam)⁻¹ := by
  have hl1 := lam_ltE H
  rw [H.k0, Real.sqrt_inv, Real.sqrt_sq (by linarith)]

theorem k0_nonnegE (H : DetBase c δ π m) : 0 ≤ c.p.k0 := by
  rw [H.k0]; positivity

theorem lvQ_nonnegE (H : DetBase c δ π m) : 0 ≤ lvQ c.p := by
  have := H.rows.pos_de; have := H.rows.pos_lam; have := H.one_le_Le
  unfold lvQ; positivity

/-- `|w - μ_s|²_{P_s} ≤ lvQ` for `w` within `δ_e⁴` of `y ∈ S_t`. -/
theorem lq_qE (H : DetBase c δ π m) {t : ℕ} (ht : t ≤ c.tau π m) {y w : Fin d → ℝ} (hy : y ∈ c.SS π t)
    (hc : (w - y) ⬝ᵥ (w - y) ≤ c.p.δe ^ 8) {s : ℕ} (hs : s ≤ t) :
    df2Sq (c.st π s).P (w - (c.st π s).mu) ≤ lvQ c.p := by
  have hI := H.stInv_le_tau s (hs.trans ht)
  have hde : 0 < c.p.δe := H.rows.pos_de
  have hde1 : c.p.δe < 1 := H.rows.de_lt
  have hl : 0 < c.p.lam := H.rows.pos_lam
  have hL : 1 ≤ c.p.Le := H.one_le_Le
  set P := (c.st π s).P
  set mu := (c.st π s).mu
  have e1 : w - mu = (y - mu) + (w - y) := by abel
  have h1 := EvSI.psd_expand P hI.pd.posSemidef (y - mu) (w - y) _ hde
  have h2 : c.p.lam ^ 2 * df2Sq P (y - mu) ≤ 1 / (2 * c.p.Le) := hy s hs
  have h3 : df2Sq P (w - y) ≤ c.p.δe⁻¹ * ((w - y) ⬝ᵥ (w - y)) :=
    EvSI.quad_le_of_psd (EvSI.P_upper H hI) _
  have hpos : 0 < 2 * c.p.Le * c.p.lam ^ 2 := by positivity
  have h2' : df2Sq P (y - mu) ≤ 1 / (2 * c.p.Le * c.p.lam ^ 2) := by
    rw [le_div_iff₀ hpos]
    have : 1 / (2 * c.p.Le) * (2 * c.p.Le) = 1 := by field_simp
    nlinarith
  have h3' : df2Sq P (w - y) ≤ c.p.δe ^ 7 := by
    calc _ ≤ c.p.δe⁻¹ * c.p.δe ^ 8 := h3.trans (mul_le_mul_of_nonneg_left hc (by positivity))
      _ = c.p.δe ^ 7 := by field_simp
  rw [e1]
  unfold lvQ
  have h7 : (1 + c.p.δe⁻¹) * c.p.δe ^ 7 ≤ 2 * c.p.δe ^ 6 := by
    have : (1 + c.p.δe⁻¹) * c.p.δe ^ 7 = c.p.δe ^ 7 + c.p.δe ^ 6 := by field_simp
    rw [this]
    have : c.p.δe ^ 7 ≤ c.p.δe ^ 6 := pow_le_pow_of_le_one hde.le hde1.le (by norm_num)
    linarith
  calc _ ≤ (1 + c.p.δe) * df2Sq P (y - mu) + (1 + c.p.δe⁻¹) * df2Sq P (w - y) := h1
    _ ≤ (1 + c.p.δe) * (1 / (2 * c.p.Le * c.p.lam ^ 2)) + (1 + c.p.δe⁻¹) * c.p.δe ^ 7 := by gcongr
    _ ≤ _ := by
      have : (1 + c.p.δe) * (1 / (2 * c.p.Le * c.p.lam ^ 2)) = (1 + c.p.δe) / (2 * c.p.Le * c.p.lam ^ 2) := by ring
      linarith

/-- The second moments of the increments at `w` sum to at most `lvVc` up to `t ≤ τ`. -/
theorem lq_varE (H : DetBase c δ π m) {t : ℕ} (ht : t ≤ c.tau π m) {y w : Fin d → ℝ} (hy : y ∈ c.SS π t)
    (hc : (w - y) ⬝ᵥ (w - y) ≤ c.p.δe ^ 8) :
    ∑ s ∈ Finset.range (t + 1), ∫ z, yRE c.p c.Kt (π.g s) (c.st π s) z *
      (EvSI.lin (c.st π s) (w - (c.st π s).mu) z / (1 - c.p.lam)) ^ 2 ∂(EvSI.gam d) ≤ lvVc c.p d c.n := by
  have hx := H.x_ge
  set T := 8 * lvX c.p with hTdef
  have hT : 0 ≤ T := by rw [hTdef, lvX]; linarith
  have hk0 := k0_nonnegE H
  have hq := lvQ_nonnegE H
  set τ0 := Real.sqrt (Real.sqrt 105 * Real.exp (-T / 4)) with hτ0
  have hτ0n : 0 ≤ τ0 := Real.sqrt_nonneg _
  have hstep : ∀ s ∈ Finset.range (t + 1), ∫ z, yRE c.p c.Kt (π.g s) (c.st π s) z *
      (EvSI.lin (c.st π s) (w - (c.st π s).mu) z / (1 - c.p.lam)) ^ 2 ∂(EvSI.gam d) ≤
      c.p.k0 * (lvQ c.p * (T * ∫ z, yRE c.p c.Kt (π.g s) (c.st π s) z ∂(EvSI.gam d) +
        Real.sqrt (lvWb c.p d) * τ0)) := by
    intro s hs
    have hs' : s ≤ t := Nat.lt_succ_iff.1 (Finset.mem_range.1 hs)
    have hv := var_LE H (hs'.trans ht) (w - (c.st π s).mu) T hT
    have hqs := lq_qE H ht hy hc hs'
    have hY0 : 0 ≤ ∫ z, yRE c.p c.Kt (π.g s) (c.st π s) z ∂(EvSI.gam d) :=
      integral_nonneg fun z => yRE_nonneg c.p c.Kt (π.g s) _ z
    have hY2 := intY2_leE H (hs'.trans ht)
    have hsq : Real.sqrt (∫ z, yRE c.p c.Kt (π.g s) (c.st π s) z ^ 2 ∂(EvSI.gam d)) ≤ Real.sqrt (lvWb c.p d) :=
      Real.sqrt_le_sqrt hY2
    have hinner : 0 ≤ T * ∫ z, yRE c.p c.Kt (π.g s) (c.st π s) z ∂(EvSI.gam d) +
        Real.sqrt (∫ z, yRE c.p c.Kt (π.g s) (c.st π s) z ^ 2 ∂(EvSI.gam d)) * τ0 := by
      positivity
    refine hv.trans (mul_le_mul_of_nonneg_left ?_ hk0)
    refine mul_le_mul hqs ?_ hinner hq
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hsq hτ0n)
  refine (Finset.sum_le_sum hstep).trans ?_
  rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul]
  have hsum := sumY_leE H ht
  have htn : ((t + 1 : ℕ) : ℝ) ≤ c.n := by
    have h1 := H.le_tau_lt ht
    have h2 : m ≤ c.n := H.hmn
    exact_mod_cast (by omega : t + 1 ≤ c.n)
  have hW : 0 ≤ Real.sqrt (lvWb c.p d) * τ0 := by positivity
  unfold lvVc
  rw [← hTdef, ← hτ0]
  refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hq) hk0
  have h1 : T * ∑ s ∈ Finset.range (t + 1), ∫ z, yRE c.p c.Kt (π.g s) (c.st π s) z ∂(EvSI.gam d) ≤
      T * (9 * c.n) := mul_le_mul_of_nonneg_left hsum hT
  have h2 : ((t + 1 : ℕ) : ℝ) * (Real.sqrt (lvWb c.p d) * τ0) ≤ c.n * (Real.sqrt (lvWb c.p d) * τ0) :=
    mul_le_mul_of_nonneg_right htn hW
  push_cast at h2 ⊢
  linarith

/-- `|⟨s'_s(μ_s), v⟩| ≤ (8/ε) |v|` up to `τ`. -/
theorem sGrad_dotE (H : DetBase c δ π m) {s : ℕ} (hs : s ≤ c.tau π m) (v : Fin d → ℝ) :
    |c.sGrad π s ⬝ᵥ v| ≤ 8 / c.p.eps * Real.sqrt (v ⬝ᵥ v) := by
  have hI := H.stInv_le_tau s hs
  have hsi := H.si (H.le_tau_lt hs) (H.stOK_of_stInv hI)
  have he0 : 0 < c.p.eps := H.rows.pos_eps
  have hK : 0 ≤ 8 / c.p.eps := by positivity
  have hlip := EvSI.surr_lip (df2Ext c.p c.Kt (π.g s)) (8 / c.p.eps) hK hsi.ext_lip
    (WithLp.toLp 2 (c.st π s).mu) (Matrix.toEuclideanCLM (𝕜 := ℝ) (c.st π s).A) _ H.rows.pos_lam
  exact EvSI.gradM_dot_le _ _ hK hlip _ v

/-- The increment of (c) at `w` is at most `y0 κ₀^{1/2} ((b0 + 1) lvQ)^{1/2}` in absolute value, up to `τ`. -/
theorem lq_rangeE {b0 y0 : ℝ} (hy0 : 0 ≤ y0) (H : DetBase c δ (pathW c b0 y0 π) m) {s : ℕ}
    (hs : s ≤ c.tau (pathW c b0 y0 π) m) {w : Fin d → ℝ}
    (hq : df2Sq (c.st (pathW c b0 y0 π) s).P (w - (c.st (pathW c b0 y0 π) s).mu) ≤ lvQ c.p) :
    |c.Y (pathW c b0 y0 π) s * phiLE c.p w (c.st (pathW c b0 y0 π) s) (π.xi s)| ≤
      y0 * Real.sqrt c.p.k0 * Real.sqrt ((b0 + 1) * lvQ c.p) := by
  set πw := pathW c b0 y0 π with hπw
  have hI := H.stInv_le_tau s hs
  set st := c.st πw s with hstdef
  obtain ⟨hY, hYξ⟩ := Y_sure c b0 y0 π s hy0 hI.run
  set b := st.Aᵀ *ᵥ (st.P *ᵥ (w - st.mu)) with hb
  have hbb : b ⬝ᵥ b = df2Sq st.P (w - st.mu) := EvSI.dir_sq st hI.AA hI.SP _
  have hphi : phiLE c.p w st (π.xi s) = (π.xi s ⬝ᵥ b) * Real.sqrt c.p.k0 := by
    unfold phiLE; rw [EvSI.lin_eq_dot st (EvSI.P_symm hI), sqrt_k0E H, ← hb]; ring
  have hk := Real.sqrt_nonneg c.p.k0
  have hq0 := lvQ_nonnegE H
  by_cases hY0 : c.Y πw s = 0
  · rw [hY0, zero_mul, abs_zero]; positivity
  have hξ := hYξ hY0
  have h1 : |π.xi s ⬝ᵥ b| ≤ Real.sqrt (b0 + 1) * Real.sqrt (lvQ c.p) :=
    (EvSI.abs_dot_le _ _).trans (mul_le_mul (Real.sqrt_le_sqrt hξ) (Real.sqrt_le_sqrt (hbb ▸ hq))
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  have hb1 : 0 ≤ b0 + 1 := le_trans (EvSI.dot_self_nonneg' _) hξ
  rw [hphi, abs_mul, abs_mul, abs_of_nonneg hk, Real.sqrt_mul hb1]
  calc |c.Y πw s| * (|π.xi s ⬝ᵥ b| * Real.sqrt c.p.k0) ≤
        y0 * ((Real.sqrt (b0 + 1) * Real.sqrt (lvQ c.p)) * Real.sqrt c.p.k0) := by
        gcongr
    _ = _ := by ring

/-- The sums at `y` and at `w` differ by at most `n lvGc δ_e⁴` up to `τ`. -/
theorem lq_disc_pathE {b0 y0 : ℝ} (hy0 : 0 ≤ y0) (H : DetBase c δ (pathW c b0 y0 π) m) {t : ℕ}
    (ht : t ≤ c.tau (pathW c b0 y0 π) m) {y w : Fin d → ℝ} (hyc : Real.sqrt ((y - w) ⬝ᵥ (y - w)) ≤ c.p.δe ^ 4) :
    |∑ s ∈ Finset.range (t + 1), (c.ghat (pathW c b0 y0 π) s - c.sGrad (pathW c b0 y0 π) s) ⬝ᵥ
        (y - (c.st (pathW c b0 y0 π) s).mu) -
      ∑ s ∈ Finset.range (t + 1), (c.ghat (pathW c b0 y0 π) s - c.sGrad (pathW c b0 y0 π) s) ⬝ᵥ
        (w - (c.st (pathW c b0 y0 π) s).mu)| ≤ c.n * lvGc c.p b0 y0 * c.p.δe ^ 4 := by
  set πw := pathW c b0 y0 π with hπw
  have he0 : 0 < c.p.eps := H.rows.pos_eps
  have hde : 0 < c.p.δe := H.rows.pos_de
  have hk := Real.sqrt_nonneg c.p.k0
  have hG0 : 0 ≤ lvGc c.p b0 y0 := by
    unfold lvGc
    have : 0 ≤ y0 * Real.sqrt c.p.k0 * Real.sqrt ((b0 + 1) / c.p.δe) := by positivity
    have : 0 ≤ 8 / c.p.eps := by positivity
    linarith
  have hterm : ∀ s ≤ t, |(c.ghat πw s - c.sGrad πw s) ⬝ᵥ (y - w)| ≤ lvGc c.p b0 y0 * c.p.δe ^ 4 := by
    intro s hst
    have hs := hst.trans ht
    have hI := H.stInv_le_tau s hs
    set st := c.st πw s
    obtain ⟨hY, hYξ⟩ := Y_sure c b0 y0 π s hy0 hI.run
    have hgh : c.ghat πw s ⬝ᵥ (y - w) = c.Y πw s * Real.sqrt c.p.k0 * ((st.P *ᵥ (st.A *ᵥ π.xi s)) ⬝ᵥ (y - w)) := by
      unfold Df2Ctx.ghat Df2Ctx.u Df2Ctx.w
      rw [smul_dotProduct, smul_eq_mul, sqrt_k0E H]
      rfl
    have h1 : |c.Y πw s * Real.sqrt c.p.k0 * ((st.P *ᵥ (st.A *ᵥ π.xi s)) ⬝ᵥ (y - w))| ≤
        y0 * Real.sqrt c.p.k0 * (Real.sqrt ((b0 + 1) / c.p.δe) * c.p.δe ^ 4) := by
      by_cases hY0 : c.Y πw s = 0
      · rw [hY0, zero_mul, zero_mul, abs_zero]; positivity
      have hξ := hYξ hY0
      have hu : (st.P *ᵥ (st.A *ᵥ π.xi s)) ⬝ᵥ (st.P *ᵥ (st.A *ᵥ π.xi s)) ≤ (b0 + 1) / c.p.δe :=
        (u_norm st.P st.S st.A (π.xi s) _ hde hI.pd.posSemidef hI.AA hI.SP (EvSI.P_upper H hI)).trans
          (div_le_div_of_nonneg_right hξ hde.le)
      have h2 : |(st.P *ᵥ (st.A *ᵥ π.xi s)) ⬝ᵥ (y - w)| ≤ Real.sqrt ((b0 + 1) / c.p.δe) * c.p.δe ^ 4 :=
        (EvSI.abs_dot_le _ _).trans (mul_le_mul (Real.sqrt_le_sqrt hu) hyc (Real.sqrt_nonneg _)
          (Real.sqrt_nonneg _))
      rw [abs_mul, abs_mul, abs_of_nonneg hk]
      gcongr
    have h2 := sGrad_dotE H hs (y - w)
    rw [sub_dotProduct, hgh]
    unfold lvGc
    calc _ ≤ |c.Y πw s * Real.sqrt c.p.k0 * ((st.P *ᵥ (st.A *ᵥ π.xi s)) ⬝ᵥ (y - w))| +
          |c.sGrad πw s ⬝ᵥ (y - w)| := abs_sub _ _
      _ ≤ y0 * Real.sqrt c.p.k0 * (Real.sqrt ((b0 + 1) / c.p.δe) * c.p.δe ^ 4) + 8 / c.p.eps * c.p.δe ^ 4 := by
        gcongr
        exact h2.trans (mul_le_mul_of_nonneg_left hyc (by positivity))
      _ = _ := by ring
  rw [← Finset.sum_sub_distrib]
  have e1 : ∀ s ∈ Finset.range (t + 1),
      (c.ghat πw s - c.sGrad πw s) ⬝ᵥ (y - (c.st πw s).mu) - (c.ghat πw s - c.sGrad πw s) ⬝ᵥ (w - (c.st πw s).mu) =
      (c.ghat πw s - c.sGrad πw s) ⬝ᵥ (y - w) := by
    intro s _
    rw [← dotProduct_sub]; congr 1; abel
  rw [Finset.sum_congr rfl e1]
  have htn : ((t + 1 : ℕ) : ℝ) ≤ c.n := by
    have h1 := H.le_tau_lt ht
    have h2 : m ≤ c.n := H.hmn
    exact_mod_cast (by omega : t + 1 ≤ c.n)
  calc _ ≤ ∑ s ∈ Finset.range (t + 1), |(c.ghat πw s - c.sGrad πw s) ⬝ᵥ (y - w)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _s ∈ Finset.range (t + 1), lvGc c.p b0 y0 * c.p.δe ^ 4 :=
      Finset.sum_le_sum fun s hs => hterm s (Nat.lt_succ_iff.1 (Finset.mem_range.1 hs))
    _ = ((t + 1 : ℕ) : ℝ) * (lvGc c.p b0 y0 * c.p.δe ^ 4) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ c.n * (lvGc c.p b0 y0 * c.p.δe ^ 4) := mul_le_mul_of_nonneg_right htn (by positivity)
    _ = _ := by ring

end path

end AdversarialBco.UW
