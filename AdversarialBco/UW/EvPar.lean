/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.UW.ParamT4U

@[expose] public section

/-!
# The regime facts the events of Theorem UW read

On the regime `RegimeW d n ρ`, the table T4U `parW d n ρ.u` and the levels of event (a):

* `eps_pos`, `eps_lt_one`, `Le_ge`, `lam_pos`, `sig2_eq`, `sig2_pos`, `de_pos`, `eta_kap_nonneg`: the
  fields of T4U that the epoch's light invariant (`EvGY.LPar`) and the gauge tail read;
* `n0W_ge`, `n0W_le_inv`: `14 n ≤ N_0 ≤ 1/δc`;
* `lgW_le_leW`, `Le_le_leW`: the level `x = log(14 n/δc)` and the floor's `L = 36 log N_0` lie below
  `L_e = 36 log(1/δc)`; `two_exp_lgW`: `2 e^{-x} = δc/(7 n)`, the budget of one round of event (a).

The names live in `AdversarialBco.UW.EvP`.
-/

namespace AdversarialBco.UW.EvP

open AdversarialBco.Poly

variable {d n : ℕ} {ρ : RefW}

theorem eps_pos (hreg : RegimeW d n ρ) : 0 < (parW d n ρ.u).eps := by
  have hL := regW_Le hreg.hd hreg.hn hreg.hu hreg.heps
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hreg.hd
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hreg.hn
  have hu0 : (0 : ℝ) < ρ.u := lt_of_lt_of_le one_pos hreg.hu
  rw [parW_eps, Bit.PieceA.eps]
  have : 0 < Bit.PieceA.Le d n := by linarith
  positivity

theorem eps_lt_one (hreg : RegimeW d n ρ) : (parW d n ρ.u).eps < 1 := by
  have := hreg.heps; linarith

theorem Le_ge (hreg : RegimeW d n ρ) : 17467 ≤ (parW d n ρ.u).Le := by
  rw [parW_Le]; exact regW_Le hreg.hd hreg.hn hreg.hu hreg.heps

theorem lam_bounds (hreg : RegimeW d n ρ) : 0 < (parW d n ρ.u).lam ∧ (parW d n ρ.u).lam ≤ 1 := by
  rw [parW_lam]
  have hL := regW_Le hreg.hd hreg.hn hreg.hu hreg.heps
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hreg.hd
  have hL2 : 1 ≤ Bit.PieceA.Le d n ^ 2 := by nlinarith
  have hden : 1 ≤ 725 * (d : ℝ) * Bit.PieceA.Le d n ^ 2 := by nlinarith
  exact ⟨one_div_pos.2 (by linarith), (div_le_one (by linarith)).2 hden⟩

theorem y0_pos (hreg : RegimeW d n ρ) : 0 < ρ.y0 := by
  have h1 := hreg.y0_lo
  have he := eps_pos hreg
  have h2 : 0 < 18 / (parW d n ρ.u).eps := by positivity
  have h3 : 0 ≤ Real.sqrt (12 * lam0 d n) := Real.sqrt_nonneg _
  linarith

theorem lam_pos (hreg : RegimeW d n ρ) : 0 < (parW d n ρ.u).lam := (lam_bounds hreg).1

theorem sig2_eq (d n : ℕ) (u : ℝ) : (parW d n u).sig2 = 1 / (8 * (parW d n u).Le) := rfl

theorem sig2_pos (hreg : RegimeW d n ρ) : 0 < (parW d n ρ.u).sig2 := by
  rw [sig2_eq]
  have := Le_ge hreg
  exact one_div_pos.2 (by linarith)

/-- `14 n ≤ N_0`. -/
theorem n0W_ge (hd : 1 ≤ d) : 14 * n ≤ n0W d n := by
  rw [n0W_eq]
  unfold Bit.PieceA.NeN
  have hd3 : 1 ≤ d ^ 3 := Nat.one_le_pow _ _ hd
  have hn4 : n ≤ n ^ 4 := Nat.le_self_pow (by norm_num) n
  calc 14 * n = 14 * 1 * n := by ring
    _ ≤ 15 * 2 ^ 17 * d ^ 3 * n ^ 4 := Nat.mul_le_mul (Nat.mul_le_mul (by norm_num) hd3) hn4

theorem n0W_pos (hd : 1 ≤ d) (hn : 1 ≤ n) : (0 : ℝ) < n0W d n := by
  have := n0W_ge (n := n) hd
  exact Nat.cast_pos.2 (by omega)

theorem de_pos (hreg : RegimeW d n ρ) : 0 < (parW d n ρ.u).δe := by
  show 0 < 1 / (n0W d n : ℝ)
  exact one_div_pos.2 (n0W_pos hreg.hd hreg.hn)

theorem eta_kap_nonneg (hreg : RegimeW d n ρ) : 0 ≤ (parW d n ρ.u).eta * (parW d n ρ.u).kap := by
  rw [parW_kap, parW_eta]
  have hL := regW_Le hreg.hd hreg.hn hreg.hu hreg.heps
  have h0 : 0 ≤ Bit.PieceA.Le d n * Real.sqrt (n * ρ.u) := mul_nonneg (by linarith) (Real.sqrt_nonneg _)
  exact mul_nonneg (div_nonneg (Real.sqrt_nonneg _) h0) (by norm_num)

/-- `N_0 ≤ 1/δc`. -/
theorem n0W_le_inv (hreg : RegimeW d n ρ) : (n0W d n : ℝ) ≤ 1 / ρ.δc :=
  (le_one_div (n0W_pos hreg.hd hreg.hn) hreg.dc_pos).2 hreg.dc_le

/-- `14 n ≤ 1/δc`. -/
theorem fourteen_n_le (hreg : RegimeW d n ρ) : (14 * n : ℝ) ≤ 1 / ρ.δc :=
  calc (14 * n : ℝ) = ((14 * n : ℕ) : ℝ) := by push_cast; ring
    _ ≤ (n0W d n : ℝ) := by exact_mod_cast n0W_ge (n := n) hreg.hd
    _ ≤ 1 / ρ.δc := n0W_le_inv hreg

theorem log_fourteen_n_nonneg (hn : 1 ≤ n) : 0 ≤ Real.log (14 * n) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  exact Real.log_nonneg (by linarith)

theorem log_inv_dc_ge (hreg : RegimeW d n ρ) : Real.log (14 * n) ≤ Real.log (1 / ρ.δc) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hreg.hn
  exact Real.log_le_log (by linarith) (fourteen_n_le hreg)

theorem log_inv_dc_nonneg (hreg : RegimeW d n ρ) : 0 ≤ Real.log (1 / ρ.δc) :=
  (log_fourteen_n_nonneg hreg.hn).trans (log_inv_dc_ge hreg)

/-- `x = log(14 n) + log(1/δc)`. -/
theorem lgW_eq (hn : 1 ≤ n) {δc : ℝ} (hdc : 0 < δc) : lgW n δc = Real.log (14 * n) + Real.log (1 / δc) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  unfold lgW
  rw [← Real.log_mul (by linarith) (one_div_pos.2 hdc).ne', mul_one_div]

theorem lgW_nonneg (hreg : RegimeW d n ρ) : 0 ≤ lgW n ρ.δc := by
  rw [lgW_eq hreg.hn hreg.dc_pos]
  have := log_fourteen_n_nonneg hreg.hn
  have := log_inv_dc_nonneg hreg
  linarith

/-- The level of event (a) lies below `L_e`: `log(14 n/δc) ≤ 36 log(1/δc)`. -/
theorem lgW_le_leW (hreg : RegimeW d n ρ) : lgW n ρ.δc ≤ leW ρ.δc := by
  rw [lgW_eq hreg.hn hreg.dc_pos, leW, df2C0]
  have := log_inv_dc_ge hreg
  have := log_inv_dc_nonneg hreg
  linarith

/-- The floor's `L = 36 log N_0` lies below `L_e = 36 log(1/δc)`. -/
theorem Le_le_leW (hreg : RegimeW d n ρ) : (parW d n ρ.u).Le ≤ leW ρ.δc := by
  show df2C0 * Real.log (1 / (1 / (n0W d n : ℝ))) ≤ df2C0 * Real.log (1 / ρ.δc)
  rw [one_div_one_div]
  have := Real.log_le_log (n0W_pos hreg.hd hreg.hn) (n0W_le_inv hreg)
  rw [df2C0]
  linarith

/-- The budget of one round of event (a): `2 e^{-x} = δc/(7 n)`. -/
theorem two_exp_lgW (hn : 1 ≤ n) {δc : ℝ} (hdc : 0 < δc) : 2 * Real.exp (-lgW n δc) = δc / (7 * n) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hpos : 0 < 14 * (n : ℝ) / δc := by positivity
  rw [lgW, Real.exp_neg, Real.exp_log hpos]
  field_simp
  ring

end AdversarialBco.UW.EvP
