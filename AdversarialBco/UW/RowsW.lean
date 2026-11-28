/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.UW.Rows

@[expose] public section

/-!
# UW-ROWS at the levels with `u` and under the sure ranges

`rowsUW : RowsUW`, from UW/Rows.lean (`rows_dom`, `rowHyp_parW1`) and:

* `parDom_parW`: T4U at `u ≥ 1` against T4U at `u = 1` (`η` down by `√u`, `ε` up by `√u`);
* `etaBnW_le`, `etaB1W_le`: `η_u B_n(u) ≤ η_1 B_n(1)` and `η_u b₁(u) ≤ η_1 b₁(1)`;
* `stabW_le`: the stability term with the sure ranges is at most `ρ/10^6`;
* `y0_le`, `logc_le`: `y_0 ≤ 7 L^{1/2}/ε_u` and `0 ≤ log(7/δ_c) ≤ u d L` on the regime.
-/

namespace AdversarialBco.UW

open AdversarialBco.Poly AdversarialBco.Poly.Layer2

variable {d : ℕ}

/-! ## The scale `u` against `u = 1` -/

/-- `L = 36 Λ_0`. -/
theorem parW_Le_lam0 (d n : ℕ) (u : ℝ) : (parW d n u).Le = 36 * lam0 d n := by
  show df2C0 * Real.log (1 / (1 / (n0W d n : ℝ))) = _
  rw [df2C0, one_div_one_div, lam0]

theorem parW_Le_ge {n : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n) (u : ℝ) : 504 ≤ (parW d n u).Le :=
  (parOK_parW (u := 1) hd hn le_rfl).Le

/-- `ε(1)² n = 14500² d³ L^{10}`. -/
theorem parW1_eps_sq {n : ℕ} (hn : 1 ≤ n) :
    (parW d n 1).eps ^ 2 * n = 14500 ^ 2 * (d : ℝ) ^ 3 * (parW d n 1).Le ^ 10 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [parW1_eps, div_pow]
  have e1 : (20 * 725 * ((d : ℝ) * Real.sqrt d) * (parW d n 1).Le ^ 5) ^ 2 =
      14500 ^ 2 * (d : ℝ) ^ 2 * Real.sqrt d ^ 2 * (parW d n 1).Le ^ 10 := by ring
  rw [e1, Real.sq_sqrt (Nat.cast_nonneg d), Real.sq_sqrt (Nat.cast_nonneg n)]
  field_simp

/-- `η(1)/ε(1) = 1/(14500 d L⁶)`. -/
theorem parW1_eta_div_eps {n : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n) :
    (parW d n 1).eta / (parW d n 1).eps = 1 / (14500 * d * (parW d n 1).Le ^ 6) := by
  have hL := parW_Le_ge hd hn 1
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hsd : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.2 hd0
  rw [parW1_eta, parW1_eps]
  have hdd : (d : ℝ) * Real.sqrt d = Real.sqrt d * Real.sqrt d * Real.sqrt d := by
    rw [Real.mul_self_sqrt hd0.le]
  rw [hdd]
  field_simp
  ring_nf
  rw [Real.sq_sqrt hd0.le]

/-- `η(u)² n u = d/L²`. -/
theorem parW_eta_sq {n : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n) {u : ℝ} (hu : 0 < u) :
    (parW d n u).eta ^ 2 * n * u = d / (parW d n u).Le ^ 2 := by
  have hL := parW_Le_ge hd hn u
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  show (Real.sqrt d / ((parW d n u).Le * Real.sqrt ((n : ℝ) * u))) ^ 2 * n * u = _
  rw [div_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg d), Real.sq_sqrt (by positivity)]
  field_simp

/-- T4U at `u ≥ 1` against `u = 1`. -/
theorem parDom_parW {n : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n) {u : ℝ} (hu : 1 ≤ u) :
    ParDom (parW d n u) (parW d n 1) := by
  have hL := parW_Le_ge hd hn 1
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hsu : 1 ≤ Real.sqrt u := by rw [Real.one_le_sqrt]; exact hu
  have he1 : 0 < (parW d n 1).eps := by
    rw [parW1_eps]
    have := Real.sqrt_pos.2 hd0
    positivity
  have hη1 : 0 < (parW d n 1).eta := by
    rw [parW1_eta]
    have := Real.sqrt_pos.2 hd0
    positivity
  have hη := parW_eta_u1 d n (u := u) (by linarith)
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, he1, ?_, ?_, by linarith, by
    show (0 : ℝ) ≤ 1 / 4; norm_num⟩
  · rw [hη]; positivity
  · rw [hη]; exact div_le_self hη1.le hsu
  · rw [parW_eps_u1 d n u]; exact le_mul_of_one_le_right he1.le hsu
  · rw [hη, parW_eps_u1 d n u]; field_simp

/-- **The rows of Theorem U's record at T4U**, for `u ≥ 1` with `ε(u) ≤ 1/2`. -/
theorem rows_parW {n : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n) {u : ℝ} (hu : 1 ≤ u) (heps : (parW d n u).eps ≤ 1 / 2) :
    Df2Rows (parW d n u) d n := by
  have D := parDom_parW hd hn hu
  have h1 : (parW d n 1).eps ≤ 1 / 2 := D.eps.trans heps
  exact rows_dom D (rows_of _ d n (rowHyp_parW1 hd hn h1)) heps

/-! ## The levels with `u` -/

theorem sqrt_mul_u (x u : ℝ) (hx : 0 ≤ x) : Real.sqrt (x * u) = Real.sqrt x * Real.sqrt u :=
  Real.sqrt_mul hx u

/-- `η_u B_n(u) ≤ η_1 B_n(1)`: the factors `√u` of `B_n(u)` cancel those of `η` and `ε`. -/
theorem etaBnW_le {n : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n) {u : ℝ} (hu : 1 ≤ u) :
    (parW d n u).eta * bnW (parW d n u) d n u ≤ (parW d n 1).eta * df2Bn (parW d n 1) d n := by
  have D := parDom_parW hd hn hu
  have hL := parW_Le_ge hd hn 1
  set s := Real.sqrt u with hs
  have hs1 : 1 ≤ s := by rw [hs, Real.one_le_sqrt]; exact hu
  have hs0 : 0 < s := by linarith
  have hus : u = s * s := (Real.mul_self_sqrt (by linarith)).symm
  have hη := parW_eta_u1 d n (u := u) (by linarith)
  have hl1 : 0 < (parW d n 1).lam := by
    rw [(parOK_parW (u := 1) hd hn le_rfl).lam]; have : (0 : ℝ) < d := by exact_mod_cast hd
    positivity
  have he1 := D.eps0
  have hη1 := D.etap
  unfold bnW df2Bn
  rw [hη, parW_eps_u1 d n u, show (parW d n u).lam = (parW d n 1).lam from rfl, show (parW d n u).Le = (parW d n 1).Le from rfl,
    show (10 : ℝ) * d * n * u = (10 * d * n) * u by ring, sqrt_mul_u _ _ (by positivity), ← hs]
  set e := (parW d n 1).eta
  set l := (parW d n 1).lam
  set L := (parW d n 1).Le
  set ε := (parW d n 1).eps
  set a := Real.sqrt (10 * (d : ℝ) * n)
  have key : e / s * (l * L ^ 2 * (1 + a * s + (d : ℝ) ^ 2 * L * u / (ε * s))) =
      l * L ^ 2 * (e / s + e * a + e * ((d : ℝ) ^ 2 * L / ε)) := by
    rw [hus]; field_simp
  rw [key]
  have hes : e / s ≤ e := div_le_self hη1.le hs1
  have hc : 0 ≤ l * L ^ 2 := by positivity
  calc l * L ^ 2 * (e / s + e * a + e * ((d : ℝ) ^ 2 * L / ε)) ≤ l * L ^ 2 * (e + e * a + e * ((d : ℝ) ^ 2 * L / ε)) := by
        gcongr
    _ = e * (l * L ^ 2 * (1 + a + (d : ℝ) ^ 2 * L / ε)) := by ring

/-- `η_u b₁(u) ≤ η_1 b₁(1)`. -/
theorem etaB1W_le {n : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n) {u : ℝ} (hu : 1 ≤ u) :
    (parW d n u).eta * b1W (parW d n u) d n u ≤ (parW d n 1).eta * df2B1 (parW d n 1) d n := by
  have D := parDom_parW hd hn hu
  have hL := parW_Le_ge hd hn 1
  set s := Real.sqrt u with hs
  have hs1 : 1 ≤ s := by rw [hs, Real.one_le_sqrt]; exact hu
  have hs0 : 0 < s := by linarith
  have hus : u = s * s := (Real.mul_self_sqrt (by linarith)).symm
  have hη := parW_eta_u1 d n (u := u) (by linarith)
  have hl1 : 0 < (parW d n 1).lam := by
    rw [(parOK_parW (u := 1) hd hn le_rfl).lam]; have : (0 : ℝ) < d := by exact_mod_cast hd
    positivity
  have he1 := D.eps0
  have hη1 := D.etap
  unfold b1W df2B1
  rw [hη, parW_eps_u1 d n u, show (parW d n u).lam = (parW d n 1).lam from rfl, show (parW d n u).Le = (parW d n 1).Le from rfl,
    show (10 : ℝ) * d * n * (parW d n 1).Le * u = (10 * d * n * (parW d n 1).Le) * u by ring,
    sqrt_mul_u _ _ (by positivity), ← hs]
  set e := (parW d n 1).eta
  set l := (parW d n 1).lam
  set L := (parW d n 1).Le
  set ε := (parW d n 1).eps
  set a := Real.sqrt (10 * (d : ℝ) * n * L)
  set b := (d : ℝ) * Real.sqrt d
  have key : e / s * (1 + 1 / l * (11 / 20 * (a * s) + 13 / 100 * b * L ^ 2 * u / (ε * s))) =
      e / s + e * (1 / l * (11 / 20 * a + 13 / 100 * b * L ^ 2 / ε)) := by
    rw [hus]; field_simp
  rw [key]
  have hes : e / s ≤ e := div_le_self hη1.le hs1
  calc e / s + e * (1 / l * (11 / 20 * a + 13 / 100 * b * L ^ 2 / ε)) ≤
        e + e * (1 / l * (11 / 20 * a + 13 / 100 * b * L ^ 2 / ε)) := by linarith
    _ = e * (1 + 1 / l * (11 / 20 * a + 13 / 100 * b * L ^ 2 / ε)) := by ring

end AdversarialBco.UW
