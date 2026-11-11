/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.Df2DetState

@[expose] public section

/-!
# DET, the rounds up to the stopping time

On the event G, at every round `s ≤ τ`: the play is in `K~`,
`|Y_s| ≤ L/(2ε)`, `|ξ_s|² ≤ (32/9) d log(1/δ_e)`, `a_s ≥ 1/2` and `q_s ≥ 1/4`. The closure: condition 3 at
`τ`, from S-DF, the monotonicity of `P̄` and X8 (condition (d)). So conditions 2 and 3 hold at every round `s ≤ τ`, the
update `P'` is positive definite with inverse `Σ'` and factor `A'` there (Lemma D.2), and the first two guards do not
act.
-/

open Matrix MeasureTheory
open scoped Matrix

namespace AdversarialBco.Poly

open Layer2

theorem herm_smul {d : ℕ} (a : ℝ) {M : Matrix (Fin d) (Fin d) ℝ} (h : M.IsHermitian) : (a • M).IsHermitian :=
  h.smul rfl

namespace Df2Ctx

variable {d : ℕ} (c : Df2Ctx d) (π : Df2Path d)

/-- Condition 3 of the stopping time at round `s`. -/
def C3 (s : ℕ) : Prop :=
  ((1 / 2 : ℝ) • c.PBar π (s + 1) - c.p.δe • (1 : Matrix (Fin d) (Fin d) ℝ)).PosSemidef ∧
    (c.Pn π s - (1 / 2 : ℝ) • c.PBar π (s + 1)).PosSemidef ∧
    ((2 : ℝ) • c.PBar π (s + 1) - c.Pn π s).PosSemidef ∧
    (c.p.δe⁻¹ • (1 : Matrix (Fin d) (Fin d) ℝ) - (2 : ℝ) • c.PBar π (s + 1)).PosSemidef

theorem PBar_eq_sum (t : ℕ) :
    c.PBar π t = c.PBar π 0 + (c.p.eta * c.p.kap) • ∑ u ∈ Finset.range t, c.sHess π u := by
  induction t with
  | zero => simp
  | succ t ih => rw [PBar_succ, ih, Finset.sum_range_succ, smul_add, add_assoc]

theorem vecMulVec_psd (u : Fin d → ℝ) : (vecMulVec u u).PosSemidef := by
  simpa using Matrix.posSemidef_vecMulVec_self_star u

theorem Pn_herm (s : ℕ) (hP : (c.st π s).P.IsHermitian) : (c.Pn π s).IsHermitian :=
  (herm_smul _ hP).add (herm_smul _ (vecMulVec_psd (c.u π s)).isHermitian)

end Df2Ctx

/-! ## Arithmetic -/

theorem trace_le_of_psd {d : ℕ} {P : Matrix (Fin d) (Fin d) ℝ} {a : ℝ}
    (h : (a • (1 : Matrix (Fin d) (Fin d) ℝ) - P).PosSemidef) : P.trace ≤ d / a⁻¹ := by
  have := h.trace_nonneg
  rw [trace_sub, trace_smul, trace_one, Fintype.card_fin, smul_eq_mul] at this
  rw [div_inv_eq_mul]; linarith

/-- The arithmetic of the closure: `2 (1/σ² + η κ N β) ≤ 1/δ` with `β = λ (8/ε)/(1 - λ) (d/δ)^{1/2}`, `N ≤ n`, under
`4 δ/σ² ≤ 1` and `16 η λ n (d δ)^{1/2}/ε ≤ 1`. -/
theorem closure_arith (σ2 δ η κ l ε d n N : ℝ) (hσ : 0 < σ2) (hδ : 0 < δ) (hη : 0 ≤ η) (hl0 : 0 < l)
    (hl : l ≤ 1 / 2) (hε : 0 < ε) (hd : 0 ≤ d) (hκ : κ = 1 / 4) (hN : N ≤ n) (hN0 : 0 ≤ N)
    (c4 : 4 * δ / σ2 ≤ 1) (c16 : 16 * η * l * n * Real.sqrt (d * δ) / ε ≤ 1) :
    2 * (σ2⁻¹ + η * κ * N * (l * (8 / ε) / (1 - l) * Real.sqrt (d / δ))) ≤ δ⁻¹ := by
  set s := Real.sqrt (d / δ) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hsδ : s * δ = Real.sqrt (d * δ) := by
    have h := Real.sqrt_mul (div_nonneg hd hδ.le) (δ * δ)
    rw [Real.sqrt_mul_self hδ.le, show d / δ * (δ * δ) = d * δ by field_simp] at h
    rw [hs, ← h]
  have h1l : 0 < 1 - l := by linarith
  have hn0 : 0 ≤ n := hN0.trans hN
  have hinv : 1 / (1 - l) ≤ 2 := by rw [div_le_iff₀ h1l]; linarith
  have hσ' : σ2⁻¹ ≤ (4 * δ)⁻¹ := by
    rw [div_le_one hσ] at c4; exact inv_anti₀ (by positivity) c4
  have key : η * κ * N * (l * (8 / ε) / (1 - l) * s) ≤ 4 * η * l * n * s / ε := by
    rw [hκ]
    have e1 : η * (1 / 4) * N * (l * (8 / ε) / (1 - l) * s) = 2 * η * l * N * s / ε * (1 / (1 - l)) := by
      field_simp; ring
    rw [e1]
    have h2 : 2 * η * l * N * s / ε ≤ 2 * η * l * n * s / ε := by gcongr
    calc 2 * η * l * N * s / ε * (1 / (1 - l)) ≤ 2 * η * l * n * s / ε * 2 := by
          apply mul_le_mul h2 hinv (div_nonneg zero_le_one h1l.le) (by positivity)
      _ = 4 * η * l * n * s / ε := by ring
  have key2 : 4 * η * l * n * s / ε = (16 * η * l * n * Real.sqrt (d * δ) / ε) / (4 * δ) := by
    rw [← hsδ]; field_simp; ring
  have h3 : (16 * η * l * n * Real.sqrt (d * δ) / ε) / (4 * δ) ≤ 1 / (4 * δ) := by
    gcongr
  have h4 : (4 * δ)⁻¹ = δ⁻¹ / 4 := by rw [mul_inv]; ring
  rw [one_div] at h3
  linarith

namespace DetBase

variable {d : ℕ} {c : Df2Ctx d} {δ : ℝ} {π : Df2Path d} {m : ℕ}

theorem Le_eq (H : DetBase c δ π m) : c.p.Le = 36 * Real.log (1 / c.p.δe) := by rw [H.Le]; rfl

theorem x_ge (H : DetBase c δ π m) : 14 ≤ Real.log (1 / c.p.δe) := by
  have h := H.rows.cx
  have : 0 ≤ Real.log ((d : ℝ) * c.n) :=
    Real.log_nonneg (one_le_mul_of_one_le_of_one_le (by exact_mod_cast H.hd) (by exact_mod_cast H.hn))
  linarith

theorem one_le_Le (H : DetBase c δ π m) : 1 ≤ c.p.Le := by
  rw [H.Le_eq]; have := H.x_ge; linarith

theorem kap_pos (H : DetBase c δ π m) : 0 < c.p.eta * c.p.kap := mul_pos H.rows.pos_eta (by rw [H.kap]; norm_num)

theorem k0_pos (H : DetBase c δ π m) : 0 < c.p.k0 := by
  rw [H.k0]; have := H.rows.lam_le; apply inv_pos.2; nlinarith

theorem le_tau_lt (H : DetBase c δ π m) {s : ℕ} (hs : s ≤ c.tau π m) : s < m := lt_of_le_of_lt hs H.tau_lt

end DetBase

namespace DetHyp

variable {d : ℕ} {c : Df2Ctx d} {δ : ℝ} {π : Df2Path d} {m : ℕ}

/-- The play is in `K_ε` and in `K~`. -/
theorem play_keps (H : DetHyp c δ π m) (s : ℕ) :
    c.play π s ∈ c.Keps ∧ WithLp.toLp 2 (c.play π s) ∈ c.Kt := by
  obtain ⟨hconv, hcl, hball, -, -⟩ := H.body
  have hε0 := H.rows.pos_eps
  have hε1 : c.p.eps < 1 := by have := H.heps; linarith
  have h := play_mem c.Kt c.p.eps hconv hcl hball hε0 hε1 (WithLp.toLp 2 (c.X π s))
  have e1 : WithLp.toLp 2 (c.play π s) = (c.pip π s)⁻¹ • WithLp.toLp 2 (c.X π s) := WithLp.toLp_smul 2 _ _
  refine ⟨?_, ?_⟩
  · show WithLp.toLp 2 ((1 - c.p.eps)⁻¹ • c.play π s) ∈ c.Kt
    rw [WithLp.toLp_smul, e1]; exact h
  · have h0 : (0 : E d) ∈ c.Kt := hball (Metric.mem_closedBall_self zero_le_one)
    have := hconv.smul_mem_of_zero_mem h0 h (t := 1 - c.p.eps) ⟨by linarith, by linarith⟩
    rw [smul_smul, mul_inv_cancel₀ (by linarith : (1 - c.p.eps) ≠ 0), one_smul] at this
    rw [e1]; exact this

/-- On G: `|Y_s| ≤ L/(2ε)`. -/
theorem ybd (H : DetHyp c δ π m) {s : ℕ} (hs : s ≤ c.tau π m) : |c.Y π s| ≤ c.p.Le / (2 * c.p.eps) := by
  obtain ⟨he, hg, -⟩ := H.evG s hs
  have hgv := (H.adm s (H.le_tau_lt hs)).2 _ (H.play_keps s).2
  refine ybound (c.pip π s) (gauge c.Kt (WithLp.toLp 2 (c.X π s))) (π.g s (WithLp.toLp 2 (c.play π s))) (π.e s)
    c.p.Le (df2Lg c.p c.n) c.p.eps H.rows.pos_eps H.heps rfl (gauge_nonneg _) hg hgv.1 hgv.2 he ?_ ?_ H.one_le_Le
  · have := H.rows.clg; rw [H.Le_eq]; linarith
  · have := H.rows.r4; simp only [df2C0] at this; exact this

/-- On G: `|ξ_s|² ≤ (32/9) d log(1/δ_e)`. -/
theorem xibd (H : DetHyp c δ π m) {s : ℕ} (hs : s ≤ c.tau π m) :
    π.xi s ⬝ᵥ π.xi s ≤ 32 / 9 * d * Real.log (1 / c.p.δe) := by
  obtain ⟨-, -, hx⟩ := H.evG s hs
  have := H.rows.clg
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  calc _ ≤ 8 * d / 3 * df2Lg c.p c.n := hx
    _ ≤ 8 * d / 3 * (4 / 3 * Real.log (1 / c.p.δe)) := by gcongr
    _ = _ := by ring

theorem dot_self_nonneg (v : Fin d → ℝ) : 0 ≤ v ⬝ᵥ v := Finset.sum_nonneg fun _ _ => mul_self_nonneg _

/-- On G: `|c_s| ≤ κ₀/4`, `a_s ≥ 1/2`, `q_s ≥ 1/4` (rows R6a, R6b). -/
theorem aq (H : DetHyp c δ π m) {s : ℕ} (hs : s ≤ c.tau π m) : 1 / 2 ≤ c.aa π s ∧ 1 / 4 ≤ c.qq π s := by
  have hY := H.ybd hs
  have hξ := H.xibd hs
  have hξ0 := dot_self_nonneg (π.xi s)
  have hk0 := H.k0_pos
  have hk1 := H.rows.k0_le
  have hη := H.rows.pos_eta
  have hl := H.rows.pos_lam
  have hε := H.rows.pos_eps
  have hL := H.one_le_Le
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  set B := c.p.eta * c.p.kap * c.p.lam * c.p.k0 with hB
  have hB0 : 0 ≤ B := by rw [hB, H.kap]; positivity
  have hcc : c.cc π s = B * c.Y π s := rfl
  have h1 : |c.cc π s| ≤ B * (c.p.Le / (2 * c.p.eps)) := by
    rw [hcc, abs_mul, abs_of_nonneg hB0]; exact mul_le_mul_of_nonneg_left hY hB0
  have h2 : B * (c.p.Le / (2 * c.p.eps)) = c.p.k0 / 4 * (c.p.eta * c.p.lam * c.p.Le / (2 * c.p.eps)) := by
    rw [hB, H.kap]; ring
  have h3 : c.p.k0 / 4 * (c.p.eta * c.p.lam * c.p.Le / (2 * c.p.eps)) ≤ c.p.k0 / 4 * 1 :=
    mul_le_mul_of_nonneg_left H.rows.r6a (by positivity)
  have hx : Real.log (1 / c.p.δe) = c.p.Le / 36 := by rw [H.Le_eq]; ring
  have h4 : B * (c.p.Le / (2 * c.p.eps)) * (32 / 9 * d * Real.log (1 / c.p.δe)) =
      c.p.k0 * (2 / 36 * c.p.eta * c.p.lam * d * c.p.Le ^ 2 / c.p.eps) * (2 / 9) := by
    rw [hx, hB, H.kap]; field_simp; ring
  have hr6b : 2 / 36 * c.p.eta * c.p.lam * d * c.p.Le ^ 2 / c.p.eps ≤ 1 := by
    have := H.rows.r6b; simp only [df2C0] at this; exact this
  have h5 : c.p.k0 * (2 / 36 * c.p.eta * c.p.lam * d * c.p.Le ^ 2 / c.p.eps) * (2 / 9) ≤ c.p.k0 * 1 * (2 / 9) := by
    gcongr
  have h6 : |c.cc π s| * (π.xi s ⬝ᵥ π.xi s) ≤ B * (c.p.Le / (2 * c.p.eps)) * (32 / 9 * d * Real.log (1 / c.p.δe)) :=
    mul_le_mul h1 hξ hξ0 (by positivity)
  have h7 : -|c.cc π s| * (π.xi s ⬝ᵥ π.xi s) ≤ c.cc π s * (π.xi s ⬝ᵥ π.xi s) :=
    mul_le_mul_of_nonneg_right (neg_abs_le _) hξ0
  have h8 := le_abs_self (c.cc π s)
  have ha : c.aa π s = 1 - c.cc π s := rfl
  have hq : c.qq π s = c.aa π s + c.cc π s * (π.xi s ⬝ᵥ π.xi s) := rfl
  constructor
  · rw [ha]; linarith
  · rw [hq, ha]; linarith

end DetHyp

namespace DetBase

variable {d : ℕ} {c : Df2Ctx d} {δ : ℝ} {π : Df2Path d} {m : ℕ}

/-! ### The closure -/

theorem sHess_psd (H : DetBase c δ π m) {u : ℕ} (hu : u ≤ c.tau π m) : (c.sHess π u).PosSemidef := by
  have hsi := H.si (H.le_tau_lt hu) (H.stOK_of_stInv (H.stInv_le_tau u hu))
  exact hess_psd _ hsi.c2 hsi.convex _

/-- X8 at `μ_u`. -/
theorem sHess_le (H : DetBase c δ π m) {u : ℕ} (hu : u ≤ c.tau π m) (v : Fin d → ℝ) :
    df2Sq (c.sHess π u) v ≤
      c.p.lam * (8 / c.p.eps) / (1 - c.p.lam) * Real.sqrt (d / c.p.δe) * (v ⬝ᵥ v) := by
  have hsi := H.si (H.le_tau_lt hu) (H.stOK_of_stInv (H.stInv_le_tau u hu))
  exact le_of_abs_le (hsi.hess1 _ v)

theorem PBar_psd (H : DetBase c δ π m) {s : ℕ} (hs : s ≤ c.tau π m) : (c.PBar π s).PosSemidef := by
  have h := (H.stInv_le_tau s hs).pbd.add (psd_smul_one H.rows.pos_de.le)
  rw [sub_add_cancel] at h
  have := h.smul (by norm_num : (0 : ℝ) ≤ 2)
  rwa [smul_smul, show (2 : ℝ) * (1 / 2) = 1 by norm_num, one_smul] at this

end DetBase

namespace DetHyp

variable {d : ℕ} {c : Df2Ctx d} {δ : ℝ} {π : Df2Path d} {m : ℕ}

/-- The closure: condition 3 at `τ`. -/
theorem c3_tau (H : DetHyp c δ π m) : c.C3 π (c.tau π m) := by
  set τ := c.tau π m with hτ
  have hI := H.stInv_le_tau τ le_rfl
  have hH := H.sHess_psd (le_refl τ)
  have hek := H.kap_pos
  have hPBτ := H.PBar_psd (le_refl τ)
  have hPB1 : c.PBar π (τ + 1) = c.PBar π τ + (c.p.eta * c.p.kap) • c.sHess π τ := Df2Ctx.PBar_succ c π τ
  have hmono : (c.PBar π (τ + 1) - c.PBar π τ).PosSemidef := by
    rw [hPB1, add_sub_cancel_left]; exact hH.smul hek.le
  have hBn : 4 * c.p.kap * c.p.eta * df2Bn c.p d c.n ≤ 1 / 2 := by
    rw [H.kap]; have := H.rows.r12; unfold df2ThN at this; linarith
  have hsdf : ∀ v, |df2Sq (c.Pn π τ - c.PBar π (τ + 1)) v| ≤ 1 / 2 * df2Sq (c.PBar π τ) v := fun v =>
    (H.evSDF τ le_rfl v).trans (mul_le_mul_of_nonneg_right hBn (sq_nonneg_of_psd hPBτ v))
  have hle : ∀ v, df2Sq (c.PBar π τ) v ≤ df2Sq (c.PBar π (τ + 1)) v := sq_le_of_psd hmono
  have hτ0 : ∀ v, 0 ≤ df2Sq (c.PBar π τ) v := sq_nonneg_of_psd hPBτ
  have hPBh : (c.PBar π (τ + 1)).IsHermitian := by rw [hPB1]; exact hPBτ.isHermitian.add (hH.smul hek.le).isHermitian
  have hPnh := Df2Ctx.Pn_herm c π τ hI.pd.isHermitian
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact psd_of_eq (hI.pbd.add ((hH.smul hek.le).smul (by norm_num : (0 : ℝ) ≤ 1 / 2)))
      (by rw [hPB1]; module)
  · refine psd_of_sq (hPnh.sub (herm_smul _ hPBh)) fun v => ?_
    have := abs_le.1 (hsdf v)
    rw [sq_sub] at this ⊢
    rw [sq_smul]
    linarith [hle v, hτ0 v]
  · refine psd_of_sq ((herm_smul _ hPBh).sub hPnh) fun v => ?_
    have := abs_le.1 (hsdf v)
    rw [sq_sub] at this ⊢
    rw [sq_smul]
    linarith [hle v, hτ0 v]
  · refine psd_of_sq ((herm_smul _ Matrix.isHermitian_one).sub (herm_smul _ hPBh)) fun v => ?_
    have hv := dot_self_nonneg v
    have hsum : ∑ u ∈ Finset.range (τ + 1), df2Sq (c.sHess π u) v ≤
        (τ + 1 : ℕ) * (c.p.lam * (8 / c.p.eps) / (1 - c.p.lam) * Real.sqrt (d / c.p.δe) * (v ⬝ᵥ v)) := by
      have := Finset.sum_le_sum fun u (hu : u ∈ Finset.range (τ + 1)) =>
        H.sHess_le (Nat.lt_succ_iff.1 (Finset.mem_range.1 hu)) v
      simpa using this
    have harith := closure_arith c.p.sig2 c.p.δe c.p.eta c.p.kap c.p.lam c.p.eps d c.n (τ + 1 : ℕ)
      H.rows.pos_sig2 H.rows.pos_de H.rows.pos_eta.le H.rows.pos_lam H.rows.lam_le H.rows.pos_eps (Nat.cast_nonneg d)
      H.kap (by exact_mod_cast (H.le_tau_lt (le_refl τ)).trans_le H.hmn) (Nat.cast_nonneg _) H.rows.c4 H.rows.c16
    rw [sq_sub, sq_smul, sq_smul, sq_one, Df2Ctx.PBar_eq_sum, sq_add, sq_smul, sq_sum, Df2Ctx.PBar_zero, sq_smul,
      sq_one]
    have hβ0 : 0 ≤ c.p.lam * (8 / c.p.eps) / (1 - c.p.lam) * Real.sqrt (d / c.p.δe) := by
      have := H.rows.lam_le; have := H.rows.pos_lam; have := H.rows.pos_eps
      apply mul_nonneg (div_nonneg (by positivity) (by linarith)) (Real.sqrt_nonneg _)
    have := mul_le_mul_of_nonneg_left hsum hek.le
    nlinarith

/-! ### Conditions 2 and 3, and Lemma D.2, at every round up to `τ` -/

theorem c3_le_tau (H : DetHyp c δ π m) {s : ℕ} (hs : s ≤ c.tau π m) : c.C3 π s := by
  rcases lt_or_eq_of_le hs with h | h
  · exact (H.cond_lt_tau s h).2.2.1
  · rw [h]; exact H.c3_tau

/-- Lemma D.2 at a round `s ≤ τ`: `P'` positive definite, `Σ' P' = 1`, `A' A'ᵀ = Σ'`, `A'` invertible. -/
theorem r1_le_tau (H : DetHyp c δ π m) {s : ℕ} (hs : s ≤ c.tau π m) :
    (c.Pn π s).PosDef ∧ c.Sn π s * c.Pn π s = 1 ∧ c.An π s * (c.An π s)ᵀ = c.Sn π s ∧ (c.An π s).det ≠ 0 := by
  have hI := H.stInv_le_tau s hs
  obtain ⟨ha, hq⟩ := H.aq hs
  have hR1 : R1Hyp (c.st π s).P (c.st π s).S (c.st π s).A := ⟨hI.pd, hI.AA, hI.SP⟩
  have ha' : 0 < 1 - c.cc π s := by show 0 < c.aa π s; linarith
  have hq' : 0 < r1Q (c.cc π s) (π.xi s) := by show 0 < c.qq π s; linarith
  have hi := H.r1i d _ _ _ (π.xi s) (c.cc π s) hR1
  have hii := H.r1ii d _ _ _ (π.xi s) (c.cc π s) hR1 ha' hq'
  have hiii := H.r1iii d _ _ _ (π.xi s) (c.cc π s) hR1 ha' hq'
  exact ⟨hi.2.2.2.2.1 ha' hq', hii.1, hiii.2.1, hiii.2.2⟩

theorem not_gdA (H : DetHyp c δ π m) {s : ℕ} (hs : s ≤ c.tau π m) : ¬ c.GdA π s := by
  unfold Df2Ctx.GdA
  obtain ⟨ha, hq⟩ := H.aq hs
  rw [not_or, not_le, not_le]
  constructor <;> linarith

theorem not_gdT (H : DetHyp c δ π m) {s : ℕ} (hs : s ≤ c.tau π m) : ¬ c.GdT π s := by
  unfold Df2Ctx.GdT
  obtain ⟨h3a, h3b, h3c, h3d⟩ := H.c3_le_tau hs
  obtain ⟨hpd, hSP, -, -⟩ := H.r1_le_tau hs
  have hde := H.rows.pos_de
  rw [not_or, not_lt, not_lt]
  constructor
  · have := trace_le_of_psd (psd_trans h3d h3c)
    rwa [inv_inv] at this
  · have hlow := psd_trans h3b h3a
    have := inv_antitone _ _ (Matrix.PosDef.one.smul hde) hpd hlow
    rw [inv_smul_one hde.ne', Matrix.inv_eq_left_inv hSP] at this
    have := trace_le_of_psd this
    rwa [inv_inv] at this

end DetHyp

end AdversarialBco.Poly
