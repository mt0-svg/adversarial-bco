/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.BLRoundBasic

@[expose] public section

/-!
# Piece C: the facts of the setting

What `BudOK` and DET at the horizon `s + 1` with `τ(s + 1) = s` give at round `s` (E1):
the draws (`e_ξ ≤ 2^{-p}`, `e_ζ ≤ 2^{-p-1}`), `|ξ_s| ≤ Ξ`, `|A°_u| ≤ δe^{-1/2} ≤ Λ^{1/2}` for `u ≤ τ`, `λ'` against `λ`.
-/

namespace AdversarialBco.Bit.BLP.RC

open AdversarialBco.Poly
open AdversarialBco.Poly.Layer2 (inv_norm_le psd_trans)
open AdversarialBco.Poly.LeanAp (oNorm_eq oNorm_add_le oNorm_sub_le oNorm_smul abs_dot_le oNorm_sq oNorm_nonneg)
open Matrix

variable {d : ℕ}

/-! ## Numerical facts on the constants -/

namespace Bud

open AdversarialBco.Bit.BLP.Bud

theorem tp_pos (d n : ℕ) : 0 < tp d n := by unfold tp; positivity

theorem tp_le_one (d n : ℕ) : tp d n ≤ 1 := by
  unfold tp; rw [div_le_one (by positivity)]; exact one_le_pow₀ (by norm_num)

/-- The coin bound gives `2^{-B/2} ≤ 2^{-p-2}/(n (⌈d/2⌉ + 1))`; hence `e_ξ ≤ 2^{-p}` and `e_ζ ≤ 2^{-p-1}`. -/
theorem exi_le {d n : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n) (h : BudOK d n) : exi d n ≤ tp d n := by
  have hc := h.coins
  set z : ℝ := 1 / 2 ^ ((par d n).B / 2) with hz
  have hz0 : 0 < z := by rw [hz]; positivity
  set k : ℕ := (d + 1) / 2 + 1 with hk
  have hk2 : (d : ℝ) + 1 ≤ 2 * k := by
    have : d + 1 ≤ 2 * k := by omega
    exact_mod_cast this
  have hsd : Real.sqrt d ≤ k := by
    have hk0 : (0 : ℝ) ≤ k := by positivity
    rw [show (k : ℝ) = Real.sqrt ((k : ℝ) ^ 2) from (Real.sqrt_sq hk0).symm]
    apply Real.sqrt_le_sqrt
    have h2 : ((d : ℝ) + 1) ^ 2 ≤ (2 * (k : ℝ)) ^ 2 := pow_le_pow_left₀ (by positivity) hk2 2
    nlinarith [sq_nonneg ((d : ℝ) - 1)]
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hk0 : (0 : ℝ) ≤ k := by positivity
  have h1 : (k : ℝ) * z ≤ n * k * z := by
    have := mul_le_mul_of_nonneg_right hn1 (mul_nonneg hk0 hz0.le)
    linarith [show (n : ℝ) * k * z = n * (k * z) by ring]
  unfold exi dbits at *
  have e : (4 : ℝ) / 2 ^ ((par d n).B / 2) = 4 * z := by rw [hz]; ring
  rw [e]
  have : Real.sqrt d * (4 * z) ≤ 4 * (k * z) := by nlinarith [Real.sqrt_nonneg (d : ℝ)]
  nlinarith

theorem ezt_le {d n : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n) (h : BudOK d n) : ezt d n ≤ tp d n / 2 := by
  have hc := h.coins
  set z : ℝ := 1 / 2 ^ ((par d n).B / 2) with hz
  have hz0 : 0 < z := by rw [hz]; positivity
  have hk : (2 : ℝ) ≤ (((d + 1) / 2 + 1 : ℕ) : ℝ) := by
    have : 2 ≤ (d + 1) / 2 + 1 := by omega
    exact_mod_cast this
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  unfold ezt dbits at *
  have e : (2 : ℝ) / 2 ^ ((par d n).B / 2) = 2 * z := by rw [hz]; ring
  rw [e]
  have hnk : (2 : ℝ) ≤ n * (((d + 1) / 2 + 1 : ℕ) : ℝ) := by nlinarith
  have : (2 : ℝ) * z ≤ n * (((d + 1) / 2 + 1 : ℕ) : ℝ) * z := mul_le_mul_of_nonneg_right hnk hz0.le
  linarith

theorem ha_nonneg (d n : ℕ) : 0 ≤ ha d n := by
  unfold ha; have := tp_pos d n; positivity

theorem hb_nonneg {d n : ℕ} (h : BudOK d n) : 0 ≤ hb d n := by
  have := h.hTr_le 0 (Nat.zero_le n)
  unfold hTr at this; simp at this
  linarith [ha_nonneg d n]

end Bud

/-! ## The setting of round `s` -/

theorem tau_le {c : Df2Ctx d} {π : Df2Path d} {s : ℕ} (h : c.tau π (s + 1) = s) : s ≤ c.tau π (s + 1) := by
  rw [h]

/-- `|A°_u|² ≤ 1/δe` at a round `u ≤ τ`: `A Aᵀ = S`, `S P = 1` and `P ⪰ δe I`. -/
theorem opN_A_sq {c : Df2Ctx d} {δ : ℝ} {π : Df2Path d} {m : ℕ} (H : DetHyp c δ π m) {u : ℕ}
    (hu : u ≤ c.tau π m) : opN (c.st π u).A ≤ Real.sqrt (1 / c.p.δe) := by
  have hI := H.stInv_le_tau u hu
  have hde := H.rows.pos_de
  have hP : ((c.st π u).P - c.p.δe • (1 : Matrix (Fin d) (Fin d) ℝ)).PosSemidef := psd_trans hI.pbl hI.pbd
  rw [← opN_transpose]
  refine opN_le_of_mulVec _ _ (Real.sqrt_nonneg _) fun v => ?_
  have hS := inv_norm_le _ _ c.p.δe hde hP hI.SP v
  have e : (c.st π u).Aᵀ *ᵥ v ⬝ᵥ (c.st π u).Aᵀ *ᵥ v = v ⬝ᵥ ((c.st π u).S *ᵥ v) := by
    rw [← hI.AA, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec v, ← Matrix.mulVec_transpose]
  have h2 : oNorm ((c.st π u).Aᵀ *ᵥ v) ^ 2 ≤ (Real.sqrt (1 / c.p.δe) * oNorm v) ^ 2 := by
    rw [oNorm_sq, e, mul_pow, Real.sq_sqrt (by positivity)]
    calc v ⬝ᵥ ((c.st π u).S *ᵥ v) ≤ oNorm v * oNorm ((c.st π u).S *ᵥ v) := (le_abs_self _).trans (abs_dot_le _ _)
      _ ≤ oNorm v * (oNorm v / c.p.δe) := mul_le_mul_of_nonneg_left hS (oNorm_nonneg _)
      _ = 1 / c.p.δe * oNorm v ^ 2 := by ring
  exact (pow_le_pow_iff_left₀ (oNorm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (oNorm_nonneg _)) two_ne_zero).1 h2

/-- `1/δe ≤ Λ`. -/
theorem inv_de_le_Lam {d n : ℕ} (hd : 1 ≤ d) (h : Bud.BudOK d n) : 1 / (po d n).δe ≤ Bud.Lam d n := by
  have e := h.enc.de_eq
  unfold Bud.de at e
  rw [e, one_div_one_div]
  unfold Bud.Lam
  have hN : 0 ≤ Bud.Ne d n := by unfold Bud.Ne; positivity
  have : (1 : ℝ) ≤ d := by exact_mod_cast hd
  nlinarith

/-- `|ξ_s| ≤ Ξ` on G. -/
theorem xi_norm {c : Df2Ctx d} {δ : ℝ} {π : Df2Path d} {m n s : ℕ} (H : DetHyp c δ π m) (hs : s ≤ c.tau π m)
    (hp : c.p = po d n) (hcn : c.n = n) (h : Bud.BudOK d n) : oNorm (π.xi s) ≤ Bud.Xi d n := by
  obtain ⟨-, -, hx⟩ := H.evG s hs
  rw [hp, hcn] at hx
  have := h.Lg_le
  unfold oNorm Bud.Xi
  apply Real.sqrt_le_sqrt
  calc π.xi s ⬝ᵥ π.xi s ≤ 8 * d / 3 * df2Lg (po d n) n := hx
    _ ≤ 8 * d / 3 * Bud.Lgb d n := by gcongr

/-- E1: `|ξ' - ξ| ≤ e_ξ`. -/
theorem dxi_norm {n : ℕ} (ξ' : Fin d → ℚ) (ξ : Fin d → ℝ) (h : ∀ i, |(ξ' i : ℝ) - ξ i| ≤ eXi0 d n) :
    oNorm (cV ξ' - ξ) ≤ Bud.exi d n := by
  unfold Bud.exi
  exact oNorm_le_of_abs_le _ _ fun i => by simpa [cV, eXi0] using h i

/-- `λ'` within `2^{-p-4} λ` of `λ`. -/
theorem lam_err {d n : ℕ} (h : Bud.BudOK d n) (hl : 0 < (po d n).lam) :
    |((par d n).lam : ℝ) - (po d n).lam| ≤ Bud.tp d n / 16 * (po d n).lam := by
  have := h.enc.lam_rel
  unfold Bud.lam at this
  have e : ((par d n).lam : ℝ) - (po d n).lam = (po d n).lam * (((par d n).lam : ℝ) / (po d n).lam - 1) := by
    field_simp
  rw [e, abs_mul, abs_of_pos hl]
  nlinarith

end AdversarialBco.Bit.BLP.RC
