/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.Df2DetW
public import AdversarialBco.UW.Interfaces

@[expose] public section

/-!
# DET at T4U with sure ranges: the hypotheses and the rounds up to the stopping time

`DetHypW c π m ρ` is Theorem U's `DetHyp` (Poly/Df2DetMain.lean) for the weighted epoch: `DetBase` at the record `c.p`,
the rows of the deterministic layer at the levels with `u` (`r12w` to `r24bw` of `RowsW`, read at `c.p`), the closure
under the clip (`clo_a`, `clo_q`), four bounds of the guards, the sure ranges of the observation on the path
(`|Y_s| ≤ y0`, and `|ξ_s|² ≤ b0 + 1` where `Y_s ≠ 0`, Lemma WR), and the events (b) to (e) with sure ranges. Event
(a) is not a hypothesis: the closure is sure.

This file: on every round `s ≤ τ`, `a_s ≥ 1/2` and `q_s ≥ 1/4` from the closure; condition 3 at `τ` from S-DF at
the level `bnW` and row `r12w`; Lemma R1 and the first two guards, as in Poly/Df2DetRound.lean.
-/

open Matrix MeasureTheory
open scoped Matrix

namespace AdversarialBco.UW

open AdversarialBco.Poly AdversarialBco.Poly.Layer2

/-- `M₁` with sure ranges, `λ κ₀ y0 (b0 + 2)/δ_e`: the bound of `‖ŝ''_u‖`. -/
noncomputable def moneW {d : ℕ} (c : Df2Ctx d) (ρ : RefW) : ℝ := c.p.lam * c.p.k0 * ρ.y0 * (ρ.b0 + 2) / c.p.δe

/-- **The hypotheses of DET at T4U with sure ranges**, on the path `π` of the weighted epoch. -/
structure DetHypW {d : ℕ} (c : Df2Ctx d) (π : Df2Path d) (m : ℕ) (ρ : RefW) : Prop
    extends DetBase c (1 / 2) π m where
  u_ge : 1 ≤ ρ.u
  b0_ge : 1 ≤ ρ.b0
  y0_nonneg : 0 ≤ ρ.y0
  r12w : thnW c.p d c.n ρ.u ≤ 1
  r19ow : 2 * c.p.eta + d * c.p.Le / c.p.lam + df2Pri c.p + stabW c.p c.n ρ + c.p.eta * devKW c.p d c.n ρ.u + 1 ≤
    c.p.rho
  r20w : 2 * devPW c.p d c.n ρ.u ≤ c.p.gam * c.p.rho
  r21w : 16 * c.p.c1 * c.p.rho * c.p.Le * c.p.lam ^ 2 + 2 * thnW c.p d c.n ρ.u < 1
  r22w : 3 * c.p.eta + d * c.p.Le / c.p.lam + 10 * c.p.eta / (c.p.eps * c.p.lam) + 2 * df2Pri c.p +
    c.p.eta * devW c.p d c.n ρ.u ≤ (c.p.theta - c.p.alpha) * c.p.rho
  r24ow : 2 * c.p.eta + 8 * df2Pri c.p + 7 * stabW c.p c.n ρ + 7 * (c.p.eta * devKW c.p d c.n ρ.u) +
    7 * (c.p.eta * devW c.p d c.n ρ.u) + devPW c.p d c.n ρ.u + 7 * c.p.theta * c.p.rho + 7 ≤
      (c.p.c1 - c.p.gam) * c.p.rho
  r24bw : 3 + 2 * df2Pri c.p + stabW c.p c.n ρ + c.p.eta * devKW c.p d c.n ρ.u + c.p.eta * devW c.p d c.n ρ.u +
    devPW c.p d c.n ρ.u + c.p.theta * c.p.rho ≤ (c.p.c1 - c.p.gam) * c.p.rho
  clo_a : c.p.eta * c.p.kap * c.p.lam * c.p.k0 * ρ.y0 ≤ 1 / 2
  clo_q : c.p.eta * c.p.kap * c.p.lam * c.p.k0 * ρ.y0 * ρ.b0 ≤ 3 / 4
  /-- The guards Z and the gradient: `n η κ M₁ ≤ 1/(4 δ_e²)`. -/
  gM : c.n * (c.p.eta * c.p.kap * moneW c ρ) ≤ 1 / (4 * c.p.δe ^ 2)
  /-- The gradient: `1/σ² ≤ 1/(2 δ_e²)`. -/
  gS : c.p.sig2⁻¹ ≤ 1 / (2 * c.p.δe ^ 2)
  /-- The guard Z: `(η/2) n y0 κ₀^{1/2} ((b0 + 1)/δ_e)^{1/2} ≤ (3/4) R/δ_e²`. -/
  gZ : c.p.eta / 2 * (c.n * (ρ.y0 * Real.sqrt c.p.k0 * Real.sqrt ((ρ.b0 + 1) / c.p.δe))) ≤
    3 / 4 * c.p.R / c.p.δe ^ 2
  /-- The guard W: `4 κ₀ y0² (b0 + 1) ≤ 16 d n L`. -/
  gW : 4 * c.p.k0 * ρ.y0 ^ 2 * (ρ.b0 + 1) ≤ 16 * d * c.n * c.p.Le
  Ybd : ∀ s ≤ c.tau π m, |c.Y π s| ≤ ρ.y0
  Ywt : ∀ s ≤ c.tau π m, c.Y π s ≠ 0 → π.xi s ⬝ᵥ π.xi s ≤ ρ.b0 + 1
  evY : EvYW c π (sYW c.n ρ.y0 ρ.δc) m
  evLQ : EvLQW c π (b1W c.p d c.n ρ.u) m
  evSDF : EvSDFW c π (bnW c.p d c.n ρ.u) m
  evDQ : EvDQW c π (bnW c.p d c.n ρ.u) m

namespace DetHypW

variable {d : ℕ} {c : Df2Ctx d} {π : Df2Path d} {m : ℕ} {ρ : RefW}

theorem dot_self_nonneg (v : Fin d → ℝ) : 0 ≤ v ⬝ᵥ v := Finset.sum_nonneg fun _ _ => mul_self_nonneg _

/-- `Y_s² |ξ_s|² ≤ Y_s² (b0 + 1)` for `s ≤ τ` (the weight). -/
theorem Y_xi (H : DetHypW c π m ρ) {s : ℕ} (hs : s ≤ c.tau π m) :
    c.Y π s ^ 2 * (π.xi s ⬝ᵥ π.xi s) ≤ c.Y π s ^ 2 * (ρ.b0 + 1) := by
  by_cases hY : c.Y π s = 0
  · rw [hY]; norm_num
  · exact mul_le_mul_of_nonneg_left (H.Ywt s hs hY) (sq_nonneg _)

/-- The closure under the clip: `a_s ≥ 1/2`, `q_s ≥ 1/4` (`|c_s| ≤ η κ λ κ₀ y0`, `-1 ≤ |ξ_s|² - 1 ≤ b0` where
`c_s ≠ 0`). -/
theorem aq (H : DetHypW c π m ρ) {s : ℕ} (hs : s ≤ c.tau π m) : 1 / 2 ≤ c.aa π s ∧ 1 / 4 ≤ c.qq π s := by
  have hY := H.Ybd s hs
  have hξ0 := dot_self_nonneg (π.xi s)
  have hk0 := H.k0_pos
  have hη := H.rows.pos_eta
  have hl := H.rows.pos_lam
  have hb := H.b0_ge
  have hB0 : 0 ≤ c.p.eta * c.p.kap * c.p.lam * c.p.k0 := by rw [H.kap]; positivity
  have hcc : c.cc π s = c.p.eta * c.p.kap * c.p.lam * c.p.k0 * c.Y π s := rfl
  have h1 : |c.cc π s| ≤ c.p.eta * c.p.kap * c.p.lam * c.p.k0 * ρ.y0 := by
    rw [hcc, abs_mul, abs_of_nonneg hB0]; exact mul_le_mul_of_nonneg_left hY hB0
  have ha : c.aa π s = 1 - c.cc π s := rfl
  have hq : c.qq π s = c.aa π s + c.cc π s * (π.xi s ⬝ᵥ π.xi s) := rfl
  have hca := H.clo_a
  have hcq := H.clo_q
  have h8 := le_abs_self (c.cc π s)
  constructor
  · rw [ha]; linarith
  · rw [hq, ha]
    by_cases hY0 : c.Y π s = 0
    · have : c.cc π s = 0 := by rw [hcc, hY0, mul_zero]
      rw [this]; norm_num
    · have hξ := H.Ywt s hs hY0
      have key : -(|c.cc π s| * ρ.b0) ≤ c.cc π s * (π.xi s ⬝ᵥ π.xi s - 1) := by
        rcases le_total 0 (c.cc π s) with h | h
        · rw [abs_of_nonneg h]
          nlinarith [mul_nonneg h hξ0, mul_nonneg h (sub_nonneg.2 hb)]
        · rw [abs_of_nonpos h]
          nlinarith [mul_nonneg_of_nonpos_of_nonpos h (by linarith : π.xi s ⬝ᵥ π.xi s - 1 - ρ.b0 ≤ 0)]
      have h2 : |c.cc π s| * ρ.b0 ≤ c.p.eta * c.p.kap * c.p.lam * c.p.k0 * ρ.y0 * ρ.b0 :=
        mul_le_mul_of_nonneg_right h1 (by linarith)
      nlinarith

/-- The closure: condition 3 at `τ`, from S-DF at the level `bnW` and `r12w`. -/
theorem c3_tau (H : DetHypW c π m ρ) : c.C3 π (c.tau π m) := by
  set τ := c.tau π m with hτ
  have hI := H.stInv_le_tau τ le_rfl
  have hH := H.sHess_psd (le_refl τ)
  have hek := H.kap_pos
  have hPBτ := H.PBar_psd (le_refl τ)
  have hPB1 : c.PBar π (τ + 1) = c.PBar π τ + (c.p.eta * c.p.kap) • c.sHess π τ := Df2Ctx.PBar_succ c π τ
  have hmono : (c.PBar π (τ + 1) - c.PBar π τ).PosSemidef := by
    rw [hPB1, add_sub_cancel_left]; exact hH.smul hek.le
  have hBn : 4 * c.p.kap * c.p.eta * bnW c.p d c.n ρ.u ≤ 1 / 2 := by
    rw [H.kap]; have := H.r12w; unfold thnW at this; linarith
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

/-! ### Conditions 2 and 3, and Lemma R1, at every round up to `τ` -/

theorem c3_le_tau (H : DetHypW c π m ρ) {s : ℕ} (hs : s ≤ c.tau π m) : c.C3 π s := by
  rcases lt_or_eq_of_le hs with h | h
  · exact (H.cond_lt_tau s h).2.2.1
  · rw [h]; exact H.c3_tau

/-- Lemma R1 at a round `s ≤ τ`: `P'` positive definite, `Σ' P' = 1`, `A' A'ᵀ = Σ'`, `A'` invertible. -/
theorem r1_le_tau (H : DetHypW c π m ρ) {s : ℕ} (hs : s ≤ c.tau π m) :
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

theorem not_gdA (H : DetHypW c π m ρ) {s : ℕ} (hs : s ≤ c.tau π m) : ¬ c.GdA π s := by
  unfold Df2Ctx.GdA
  obtain ⟨ha, hq⟩ := H.aq hs
  rw [not_or, not_le, not_le]
  constructor <;> linarith

theorem not_gdT (H : DetHypW c π m ρ) {s : ℕ} (hs : s ≤ c.tau π m) : ¬ c.GdT π s := by
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

end DetHypW

end AdversarialBco.UW
