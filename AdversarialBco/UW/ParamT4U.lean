/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.UW.Interfaces
public import AdversarialBco.Bit.PieceA.Regime

@[expose] public section

/-!
# Theorem UW: the fields of T4U and the regime facts at the floor

The table `parW d n u` of UW/Defs.lean read off as explicit functions of `(d, n, u)`: its `L` is Piece A's
`Le d n = 36 ln N_0` (`N_0 = n0W d n = NeN d n`), its `ε` is Piece A's `eps d n` times `u^{1/2}`, and its `η` is
`ε/(14500 d L^6 u)`. In the regime (`1 ≤ u`, `ε(u) ≤ 1/4`) Piece A's regime facts hold at the floor: `N_0 > 2^700` and
`L ≥ 17467` (W-F1).
-/

namespace AdversarialBco.UW

open AdversarialBco.Poly
open AdversarialBco.Unified.BLO (NeO kDel parO)

theorem n0W_eq (d n : ℕ) : n0W d n = Bit.PieceA.NeN d n := rfl

/-- `L = 36 ln N_0`, Piece A's `Le` at `(d, n)`. -/
theorem parW_Le (d n : ℕ) (u : ℝ) : (parW d n u).Le = Bit.PieceA.Le d n := by
  show df2C0 * Real.log (1 / (1 / (n0W d n : ℝ))) = 36 * Real.log (Bit.PieceA.Ne d n)
  rw [one_div_one_div, df2C0]
  rfl

theorem parW_eps (d n : ℕ) (u : ℝ) : (parW d n u).eps = Bit.PieceA.eps d n * Real.sqrt u := by
  show 20 * df2oClam * (d * Real.sqrt d) * (parW d n u).Le ^ 5 * Real.sqrt u / Real.sqrt n = _
  rw [parW_Le, df2oClam, Bit.PieceA.eps]
  ring

theorem parW_eta (d n : ℕ) (u : ℝ) :
    (parW d n u).eta = Real.sqrt d / (Bit.PieceA.Le d n * Real.sqrt (n * u)) := by
  show Real.sqrt d / ((parW d n u).Le * Real.sqrt (n * u)) = _
  rw [parW_Le]

theorem parW_lam (d n : ℕ) (u : ℝ) : (parW d n u).lam = 1 / (725 * d * Bit.PieceA.Le d n ^ 2) := by
  show 1 / (df2oClam * d * (parW d n u).Le ^ 2) = _
  rw [parW_Le, df2oClam]

theorem parW_kap (d n : ℕ) (u : ℝ) : (parW d n u).kap = 1 / 4 := rfl

theorem parW_k0 (d n : ℕ) (u : ℝ) : (parW d n u).k0 = ((1 - (parW d n u).lam) ^ 2)⁻¹ := rfl

/-- In the regime the scale-free `ε` of Piece A is at most `ε(u) ≤ 1/4`. -/
theorem eps_le_of_regime {d n : ℕ} {u : ℝ} (hu : 1 ≤ u) (h : (parW d n u).eps ≤ 1 / 4) :
    Bit.PieceA.eps d n ≤ 1 / 4 := by
  rw [parW_eps] at h
  have hs : 1 ≤ Real.sqrt u := by rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hu
  rcases le_or_gt (Bit.PieceA.eps d n) 0 with h0 | h0
  · linarith
  · nlinarith

/-- (W-F1) at the floor: `N_0 > 2^700`. -/
theorem regW_N {d n : ℕ} {u : ℝ} (hd : 1 ≤ d) (hn : 1 ≤ n) (hu : 1 ≤ u) (h : (parW d n u).eps ≤ 1 / 4) :
    (2 : ℝ) ^ 700 < Bit.PieceA.Ne d n :=
  Bit.PieceA.regime_N hd hn ((eps_le_of_regime hu h).trans (by norm_num))

/-- (W-F1) at the floor: `L = 36 ln N_0 ≥ 17467`. -/
theorem regW_Le {d n : ℕ} {u : ℝ} (hd : 1 ≤ d) (hn : 1 ≤ n) (hu : 1 ≤ u) (h : (parW d n u).eps ≤ 1 / 4) :
    17467 ≤ Bit.PieceA.Le d n :=
  Bit.PieceA.regime_Le hd hn (regW_N hd hn hu h)

/-- `η = ε/(14500 d L^6 u)` at T4U. -/
theorem parW_eta_eps {d n : ℕ} {u : ℝ} (hd : 1 ≤ d) (hn : 1 ≤ n) (hu : 0 < u) (hL : 0 < Bit.PieceA.Le d n) :
    (parW d n u).eta = (parW d n u).eps / (14500 * d * Bit.PieceA.Le d n ^ 6 * u) := by
  rw [parW_eta, parW_eps, Bit.PieceA.eps]
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hsd := Real.sq_sqrt hd0.le
  have hsu := Real.sq_sqrt hu.le
  have hsd0 := Real.sqrt_pos.mpr hd0
  have hsn0 := Real.sqrt_pos.mpr hn0
  have hsu0 := Real.sqrt_pos.mpr hu
  rw [Real.sqrt_mul hn0.le]
  field_simp
  rw [show Real.sqrt u ^ 2 = u from hsu]

end AdversarialBco.UW
