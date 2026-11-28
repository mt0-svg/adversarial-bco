/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.UW.RowsW

@[expose] public section

/-!
# UW-ROWS: `rowsUW : RowsUW`

The rows of `RowsW` on the regime `RegimeW`: the record's rows (`rows_parW`), the rows at the levels with `u` from
Theorem U's rows and comparisons at `u = 1` (`etaBnW_le`, `etaB1W_le`), and the rows that read the sure ranges:
`stabW_le` (the stability term with `s_Y` and `b0`), `clo_a`, `clo_q` and event (b) under the clip, from
`y_0 ≤ 7 L^{1/2}/ε_u` (`y0_le`), `0 ≤ log(7/δ_c) ≤ u d L` (`logc_le`) and `ε_u² n = 14500² d³ L^{10} u`.
-/

namespace AdversarialBco.UW

open AdversarialBco.Poly AdversarialBco.Poly.Layer2

variable {d : ℕ}

/-! ## The sure ranges and the level on the regime -/

section Regime

variable {n : ℕ} {ρ : RefW}

theorem RegimeW.L_ge (R : RegimeW d n ρ) : 504 ≤ (parW d n ρ.u).Le := parW_Le_ge R.hd R.hn ρ.u

theorem RegimeW.u_pos (R : RegimeW d n ρ) : 0 < ρ.u := lt_of_lt_of_le one_pos R.hu

theorem RegimeW.eps_pos (R : RegimeW d n ρ) : 0 < (parW d n ρ.u).eps := (parDom_parW R.hd R.hn R.hu).eps0q

theorem RegimeW.lam0_nonneg (R : RegimeW d n ρ) : 0 ≤ lam0 d n := by
  have h := R.L_ge
  rw [parW_Le_lam0] at h
  linarith

/-- `y_0 ≤ 7 L^{1/2}/ε`. -/
theorem RegimeW.y0_le (R : RegimeW d n ρ) :
    ρ.y0 ≤ 7 * Real.sqrt (parW d n ρ.u).Le / (parW d n ρ.u).eps := by
  have hL := R.L_ge
  have he := R.eps_pos
  have he4 := R.heps
  have hsL : 22 ≤ Real.sqrt (parW d n ρ.u).Le := by
    rw [Real.le_sqrt (by norm_num) (by linarith)]; linarith
  have hy := R.y0_hi
  have h36 : 36 * lam0 d n = (parW d n ρ.u).Le := (parW_Le_lam0 d n ρ.u).symm
  rw [h36] at hy
  rw [le_div_iff₀ he]
  have h18 : 18 / (parW d n ρ.u).eps * (parW d n ρ.u).eps = 18 := div_mul_cancel₀ _ he.ne'
  calc ρ.y0 * (parW d n ρ.u).eps
      ≤ (11 + 18 / (parW d n ρ.u).eps + 10 * Real.sqrt (parW d n ρ.u).Le) * (parW d n ρ.u).eps :=
        mul_le_mul_of_nonneg_right hy he.le
    _ = 11 * (parW d n ρ.u).eps + 18 + 10 * Real.sqrt (parW d n ρ.u).Le * (parW d n ρ.u).eps := by
        rw [add_mul, add_mul, h18]
    _ ≤ 7 * Real.sqrt (parW d n ρ.u).Le := by nlinarith

theorem RegimeW.y0_pos (R : RegimeW d n ρ) : 0 < ρ.y0 := by
  have h := R.y0_lo
  have he := R.eps_pos
  have : 0 ≤ 18 / (parW d n ρ.u).eps + 10 * Real.sqrt (12 * lam0 d n) := by positivity
  linarith

theorem RegimeW.b0_le (R : RegimeW d n ρ) : ρ.b0 + 1 ≤ 3 * d * (parW d n ρ.u).Le := by
  have hL := R.L_ge
  have hb := R.b0_hi
  have h36 : 36 * lam0 d n = (parW d n ρ.u).Le := (parW_Le_lam0 d n ρ.u).symm
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast R.hd
  nlinarith

theorem RegimeW.b0_pos (R : RegimeW d n ρ) : 0 < ρ.b0 := by
  have h := R.b0_lo
  have := R.lam0_nonneg
  have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  linarith

/-- `0 ≤ log(7/δ_c) ≤ u d L`. -/
theorem RegimeW.logc (R : RegimeW d n ρ) :
    0 ≤ Real.log (7 / ρ.δc) ∧ Real.log (7 / ρ.δc) ≤ ρ.u * d * (parW d n ρ.u).Le := by
  have hL := R.L_ge
  have hl0 := R.lam0_nonneg
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast R.hd
  have hu := R.hu
  have hδ := R.dc_pos
  obtain ⟨hN, -, -, -⟩ := n0W_bounds R.hd R.hn (d := d)
  have hδ1 : ρ.δc ≤ 1 := by
    have h := R.dc_le
    have : 1 / (n0W d n : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    linarith
  have hsplit : Real.log (7 / ρ.δc) = Real.log 7 + Real.log (1 / ρ.δc) := by
    rw [← Real.log_mul (by norm_num) (by positivity)]; congr 1; field_simp
  have hl7 : Real.log 7 ≤ 6 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 7 by norm_num); linarith
  have hl7' : 0 ≤ Real.log 7 := Real.log_nonneg (by norm_num)
  have hlc : 0 ≤ Real.log (1 / ρ.δc) := Real.log_nonneg (by rw [le_div_iff₀ hδ]; linarith)
  refine ⟨by rw [hsplit]; linarith, ?_⟩
  rw [hsplit]
  have hlv := R.dc_lvl
  unfold lvl at hlv
  have h36 : (parW d n ρ.u).Le = 36 * lam0 d n := parW_Le_lam0 d n ρ.u
  rw [h36]
  -- `log 7 + Λ_0 + 7 d Λ_0 (u - 1) ≤ 6 u + 7 d Λ_0 u ≤ 36 u d Λ_0`
  have h1 : lam0 d n + 7 * d * lam0 d n * (ρ.u - 1) ≤ 7 * d * lam0 d n * ρ.u := by nlinarith
  have hL0 : 14 ≤ lam0 d n := by have := R.L_ge; rw [h36] at this; linarith
  have h2 : 6 ≤ ρ.u * d * lam0 d n := by
    have : 1 ≤ ρ.u * d := one_le_mul_of_one_le_of_one_le hu hd1
    nlinarith
  nlinarith


/-- `ε_u² n = 14500² d³ L^{10} u`. -/
theorem RegimeW.eps_sq (R : RegimeW d n ρ) :
    (parW d n ρ.u).eps ^ 2 * n = 14500 ^ 2 * (d : ℝ) ^ 3 * (parW d n ρ.u).Le ^ 10 * ρ.u := by
  have h1 := parW1_eps_sq (d := d) R.hn
  rw [parW_eps_u1, mul_pow, Real.sq_sqrt R.u_pos.le]
  have hL : (parW d n 1).Le = (parW d n ρ.u).Le := rfl
  rw [hL] at h1
  calc (parW d n 1).eps ^ 2 * ρ.u * n = (parW d n 1).eps ^ 2 * n * ρ.u := by ring
    _ = _ := by rw [h1]

/-- `η_u² y_0² log(7/δ_c) ≤ 1` and `y_0² log(7/δ_c) ≤ n`. -/
theorem RegimeW.y0_sq (R : RegimeW d n ρ) :
    (parW d n ρ.u).eta ^ 2 * (ρ.y0 ^ 2 * Real.log (7 / ρ.δc)) ≤ 1 ∧ ρ.y0 ^ 2 * Real.log (7 / ρ.δc) ≤ n := by
  have hL := R.L_ge
  have he := R.eps_pos
  have hu := R.hu
  have hu0 := R.u_pos
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast R.hd
  have hn0 : (0 : ℝ) < n := by exact_mod_cast R.hn
  obtain ⟨hlg0, hlg⟩ := R.logc
  have hy := R.y0_le
  have hy0 := R.y0_pos
  set L := (parW d n ρ.u).Le
  set ε := (parW d n ρ.u).eps
  set η := (parW d n ρ.u).eta
  set lg := Real.log (7 / ρ.δc)
  have hsL : Real.sqrt L ^ 2 = L := Real.sq_sqrt (by linarith)
  have hy2 : ρ.y0 ^ 2 ≤ 49 * L / ε ^ 2 := by
    calc ρ.y0 ^ 2 ≤ (7 * Real.sqrt L / ε) ^ 2 := pow_le_pow_left₀ hy0.le hy 2
      _ = 49 * L / ε ^ 2 := by rw [div_pow, mul_pow, hsL]; ring
  have hyl : ρ.y0 ^ 2 * lg ≤ 49 * L / ε ^ 2 * (ρ.u * d * L) :=
    mul_le_mul hy2 hlg hlg0 (by positivity)
  have hε2 := R.eps_sq
  have hη2 := parW_eta_sq R.hd R.hn hu0
  have hd3 : (d : ℝ) ≤ (d : ℝ) ^ 3 := le_self_pow₀ hd1 (by norm_num)
  have hL10 : L ^ 2 ≤ L ^ 10 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have hkey : 49 * (d : ℝ) * L ^ 2 * ρ.u ≤ 14500 ^ 2 * (d : ℝ) ^ 3 * L ^ 10 * ρ.u := by
    have h1 : 49 * (d : ℝ) * L ^ 2 ≤ 14500 ^ 2 * (d : ℝ) ^ 3 * L ^ 10 := by
      have hd0 : (0 : ℝ) ≤ d := by linarith
      have hL2 : 0 ≤ L ^ 2 := by positivity
      calc 49 * (d : ℝ) * L ^ 2 ≤ 14500 ^ 2 * (d : ℝ) * L ^ 2 := by gcongr; norm_num
        _ ≤ 14500 ^ 2 * (d : ℝ) ^ 3 * L ^ 10 := by gcongr
    exact mul_le_mul_of_nonneg_right h1 hu0.le
  have hb : 49 * L / ε ^ 2 * (ρ.u * d * L) ≤ n := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    calc 49 * L * (ρ.u * d * L) = 49 * (d : ℝ) * L ^ 2 * ρ.u := by ring
      _ ≤ 14500 ^ 2 * (d : ℝ) ^ 3 * L ^ 10 * ρ.u := hkey
      _ = n * ε ^ 2 := by rw [← hε2]; ring
  refine ⟨?_, hyl.trans hb⟩
  have hε2' : ε ^ 2 * n = 14500 ^ 2 * (d : ℝ) ^ 3 * L ^ 10 * ρ.u := hε2
  have hη2' : η ^ 2 * n * ρ.u = d / L ^ 2 := hη2
  have hd0 : (0 : ℝ) < d := by linarith
  have hL0 : 0 < L := by linarith
  have h1 : η ^ 2 * (ρ.y0 ^ 2 * lg) ≤ η ^ 2 * (49 * L / ε ^ 2 * (ρ.u * d * L)) :=
    mul_le_mul_of_nonneg_left hyl (sq_nonneg _)
  have e : η ^ 2 * (49 * L / ε ^ 2 * (ρ.u * d * L)) = 49 * (η ^ 2 * n * ρ.u) * L ^ 2 * d / (ε ^ 2 * n) := by
    field_simp <;> ring
  have e2 : 49 * ((d : ℝ) / L ^ 2) * L ^ 2 * d = 49 * (d : ℝ) ^ 2 := by
    field_simp <;> ring
  have hd23 : (d : ℝ) ^ 2 ≤ (d : ℝ) ^ 3 := pow_le_pow_right₀ hd1 (by norm_num)
  have hL1 : (1 : ℝ) ≤ L ^ 10 := one_le_pow₀ (by linarith)
  have h2 : 49 * (d : ℝ) ^ 2 ≤ 14500 ^ 2 * (d : ℝ) ^ 3 * L ^ 10 * ρ.u :=
    calc 49 * (d : ℝ) ^ 2 ≤ 14500 ^ 2 * (d : ℝ) ^ 3 * 1 * 1 := by nlinarith
      _ ≤ 14500 ^ 2 * (d : ℝ) ^ 3 * L ^ 10 * ρ.u := by gcongr
  refine h1.trans ?_
  rw [e, hη2', hε2', e2, div_le_one (by positivity)]
  exact h2

/-- **The stability term with the sure ranges** is at most `ρ/10^6`. -/
theorem RegimeW.stabW_le (R : RegimeW d n ρ) : stabW (parW d n ρ.u) n ρ ≤ (parW d n ρ.u).rho / 10 ^ 6 := by
  have hL := R.L_ge
  have hu := R.hu
  have hu0 := R.u_pos
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast R.hd
  have hn0 : (0 : ℝ) < n := by exact_mod_cast R.hn
  have hrows := rows_parW R.hd R.hn hu (R.heps.trans (by norm_num))
  have hk0 := hrows.k0_le
  have hk00 : 0 ≤ (parW d n ρ.u).k0 := by
    show (0 : ℝ) ≤ ((1 - _) ^ 2)⁻¹; positivity
  obtain ⟨hA2, -⟩ := R.y0_sq
  obtain ⟨hlg0, -⟩ := R.logc
  have hη2 := parW_eta_sq R.hd R.hn hu0
  have hb := R.b0_le
  have hb0 := R.b0_pos
  have hρ : (parW d n ρ.u).rho = 2 * 725 * (d : ℝ) ^ 2 * (parW d n ρ.u).Le ^ 3 := by
    show 2 * df2oClam * _ * _ = _; rw [df2oClam]; rfl
  set L := (parW d n ρ.u).Le
  set η := (parW d n ρ.u).eta
  set k0 := (parW d n ρ.u).k0
  set lg := Real.log (7 / ρ.δc)
  have hA1 : η ^ 2 * (21 * n) ≤ 21 * d / L ^ 2 := by
    have h : η ^ 2 * n ≤ d / L ^ 2 := by
      have h' : η ^ 2 * n * ρ.u = d / L ^ 2 := hη2
      have hη0 : 0 ≤ η ^ 2 * n := by positivity
      nlinarith
    calc η ^ 2 * (21 * n) = 21 * (η ^ 2 * n) := by ring
      _ ≤ 21 * (d / L ^ 2) := by gcongr
      _ = 21 * d / L ^ 2 := by ring
  have hA : η ^ 2 * sYW n ρ.y0 ρ.δc ≤ 2 * d := by
    unfold sYW
    have h21 : 21 * (d : ℝ) / L ^ 2 ≤ d := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    nlinarith
  have hA0 : 0 ≤ η ^ 2 * sYW n ρ.y0 ρ.δc := by unfold sYW; positivity
  have e : stabW (parW d n ρ.u) n ρ = 2 * k0 * (η ^ 2 * sYW n ρ.y0 ρ.δc) * (ρ.b0 + 1) := by
    unfold stabW; ring
  rw [e, hρ]
  calc 2 * k0 * (η ^ 2 * sYW n ρ.y0 ρ.δc) * (ρ.b0 + 1) ≤ 2 * (21 / 20) * (2 * d) * (3 * d * L) := by
        gcongr
    _ = 126 / 10 * (d : ℝ) ^ 2 * L := by ring
    _ ≤ 2 * 725 * (d : ℝ) ^ 2 * L ^ 3 / 10 ^ 6 := by
        rw [le_div_iff₀ (by norm_num)]
        have hd2 : (0 : ℝ) ≤ (d : ℝ) ^ 2 := by positivity
        have hL2 : (8690 : ℝ) ≤ L ^ 2 := by nlinarith
        have : 126 / 10 * L * 10 ^ 6 ≤ 2 * 725 * L ^ 3 := by nlinarith
        nlinarith

end Regime

/-! ## The rows -/

/-- **UW-ROWS**: every row of `RowsW` on the regime. -/
theorem rowsUW : RowsUW := by
  intro d n ρ R
  have hd := R.hd
  have hn := R.hn
  have hu := R.hu
  have heps2 : (parW d n ρ.u).eps ≤ 1 / 2 := R.heps.trans (by norm_num)
  have D := parDom_parW hd hn hu
  have RH := rowHyp_parW1 hd hn (D.eps.trans heps2)
  have H1 := rows_of _ d n RH
  have hL := R.L_ge
  have hl : 0 < (parW d n ρ.u).lam := (rows_parW hd hn hu heps2).pos_lam
  -- Theorem U's comparisons at `u = 1`, read at `u`.
  have h1 : 1 ≤ (parW d n ρ.u).rho / 10 ^ 8 := cmp_one (parW d n 1) d n RH
  have hpri : df2Pri (parW d n ρ.u) ≤ (parW d n ρ.u).rho / 300 := cmp_pri (parW d n 1) d n RH
  have hb1 : (parW d n 1).eta * df2B1 (parW d n 1) d n ≤ (parW d n ρ.u).rho / 1000 := cmp_b1 _ d n RH
  have hbn : (parW d n 1).eta * df2Bn (parW d n 1) d n / (8 * (parW d n ρ.u).Le * (parW d n ρ.u).lam ^ 2) ≤
      (parW d n ρ.u).rho / 1000 := cmp_bn _ d n RH
  have htr : (d : ℝ) * (parW d n ρ.u).Le / (parW d n ρ.u).lam = (parW d n ρ.u).rho / 2 := RH.trace_eq
  have hstab := R.stabW_le
  have hη1 : (parW d n 1).eta ≤ 1 := H1.eta_le
  have hη := D.eta
  have hηpos := D.eta0
  have hBn := etaBnW_le hd hn hu
  have hB1 := etaB1W_le hd hn hu
  have hθ : (parW d n ρ.u).theta = 1 := rfl
  have hα : (parW d n ρ.u).alpha = 1 / 4 := rfl
  have hc1 : (parW d n ρ.u).c1 = 8 := rfl
  have hγ : (parW d n ρ.u).gam = 1 / 100 := rfl
  have hκ : (parW d n ρ.u).kap = 1 / 4 := rfl
  have hLlam : 0 < 8 * (parW d n ρ.u).Le * (parW d n ρ.u).lam ^ 2 := by positivity
  -- `η B_n/(c L λ²)` at `u` against `u = 1`.
  have hBnL : (parW d n ρ.u).eta * bnW (parW d n ρ.u) d n ρ.u / (8 * (parW d n ρ.u).Le * (parW d n ρ.u).lam ^ 2) ≤
      (parW d n 1).eta * df2Bn (parW d n 1) d n / (8 * (parW d n ρ.u).Le * (parW d n ρ.u).lam ^ 2) :=
    div_le_div_of_nonneg_right hBn hLlam.le
  have hK : (parW d n ρ.u).eta * devKW (parW d n ρ.u) d n ρ.u = (parW d n ρ.u).eta * b1W (parW d n ρ.u) d n ρ.u +
      (parW d n ρ.u).eta * bnW (parW d n ρ.u) d n ρ.u / (8 * (parW d n ρ.u).Le * (parW d n ρ.u).lam ^ 2) := by
    unfold devKW; ring
  have hD : (parW d n ρ.u).eta * devW (parW d n ρ.u) d n ρ.u = (parW d n ρ.u).eta * b1W (parW d n ρ.u) d n ρ.u +
      2 * ((parW d n ρ.u).eta * bnW (parW d n ρ.u) d n ρ.u / (8 * (parW d n ρ.u).Le * (parW d n ρ.u).lam ^ 2)) := by
    unfold devW; field_simp <;> ring
  have hP : devPW (parW d n ρ.u) d n ρ.u =
      (parW d n ρ.u).eta * bnW (parW d n ρ.u) d n ρ.u / (8 * (parW d n ρ.u).Le * (parW d n ρ.u).lam ^ 2) := by
    unfold devPW; rw [hκ]; field_simp <;> ring
  set X := (parW d n 1).eta * df2Bn (parW d n 1) d n / (8 * (parW d n ρ.u).Le * (parW d n ρ.u).lam ^ 2)
  set Y := (parW d n ρ.u).eta * bnW (parW d n ρ.u) d n ρ.u / (8 * (parW d n ρ.u).Le * (parW d n ρ.u).lam ^ 2)
  have hthn : thnW (parW d n ρ.u) d n ρ.u ≤ df2ThN (parW d n 1) d n := by
    unfold thnW df2ThN; linarith
  have hP1 : df2DevP (parW d n 1) d n = X := RH.devP_eq
  have hne := D.ne hl
  have hY0 : 0 ≤ Y := by
    have : 0 ≤ bnW (parW d n ρ.u) d n ρ.u := by
      unfold bnW; have := R.eps_pos; have : 0 ≤ ρ.u := R.u_pos.le; positivity
    positivity
  have hρ0 : 0 < (parW d n ρ.u).rho := by linarith
  have hεpos := R.eps_pos
  -- the closure rows
  obtain ⟨hA2, hevb⟩ := R.y0_sq
  have hy := R.y0_le
  have hy0 := R.y0_pos
  have hηy : (parW d n ρ.u).eta * ρ.y0 ≤ 1 := by
    have hdiv : (parW d n ρ.u).eta / (parW d n ρ.u).eps ≤ 1 / (14500 * d * (parW d n ρ.u).Le ^ 6) := by
      have := D.eta_div
      rwa [parW1_eta_div_eps hd hn] at this
    have hsL : Real.sqrt (parW d n ρ.u).Le ≤ (parW d n ρ.u).Le ^ 6 := by
      calc Real.sqrt (parW d n ρ.u).Le ≤ (parW d n ρ.u).Le := by
            rw [Real.sqrt_le_left (by linarith)]; exact le_self_pow₀ (by linarith) (by norm_num)
        _ ≤ (parW d n ρ.u).Le ^ 6 := le_self_pow₀ (by linarith) (by norm_num)
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
    calc (parW d n ρ.u).eta * ρ.y0 ≤ (parW d n ρ.u).eta * (7 * Real.sqrt (parW d n ρ.u).Le / (parW d n ρ.u).eps) :=
          mul_le_mul_of_nonneg_left hy hηpos.le
      _ = 7 * Real.sqrt (parW d n ρ.u).Le * ((parW d n ρ.u).eta / (parW d n ρ.u).eps) := by ring
      _ ≤ 7 * Real.sqrt (parW d n ρ.u).Le * (1 / (14500 * d * (parW d n ρ.u).Le ^ 6)) :=
          mul_le_mul_of_nonneg_left hdiv (by positivity)
      _ ≤ 1 := by
          rw [mul_one_div, div_le_one (by positivity)]
          have hL6 : 0 ≤ (parW d n ρ.u).Le ^ 6 := by positivity
          have h6 := mul_le_mul_of_nonneg_right hd1 hL6
          linarith
  have hlam1 : (parW d n ρ.u).lam ≤ 1 / 2 := (rows_parW hd hn hu heps2).lam_le
  have hk0 : (parW d n ρ.u).k0 ≤ 21 / 20 := (rows_parW hd hn hu heps2).k0_le
  have hk00 : 0 ≤ (parW d n ρ.u).k0 := by show (0 : ℝ) ≤ ((1 - _) ^ 2)⁻¹; positivity
  have hlamb : (parW d n ρ.u).lam * ρ.b0 ≤ 1 := by
    have hb := R.b0_le
    have hlam : (parW d n ρ.u).lam = 1 / (725 * d * (parW d n ρ.u).Le ^ 2) := RH.lam
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
    rw [hlam, one_div_mul_eq_div, div_le_one (by positivity)]
    have hLL : (parW d n ρ.u).Le ≤ (parW d n ρ.u).Le ^ 2 := le_self_pow₀ (by linarith) (by norm_num)
    have h2 := mul_le_mul_of_nonneg_left hLL (by linarith : (0 : ℝ) ≤ d)
    have h3 : 0 ≤ (d : ℝ) * (parW d n ρ.u).Le ^ 2 := by positivity
    linarith
  refine
    { base := rows_parW hd hn hu heps2
      r12w := hthn.trans H1.r12
      r19ow := ?_
      r20w := ?_
      r21w := ?_
      r22w := ?_
      r24ow := ?_
      r24bw := ?_
      clo_a := ?_
      clo_q := ?_
      evb := hevb }
  · rw [hK, htr]; linarith
  · have h20 : 2 * df2DevP (parW d n 1) d n ≤ (parW d n ρ.u).gam * (parW d n ρ.u).rho := H1.r20
    rw [hP]; rw [hP1] at h20; linarith
  · have h21 : 16 * (parW d n ρ.u).c1 * (parW d n ρ.u).rho * (parW d n ρ.u).Le * (parW d n ρ.u).lam ^ 2 +
        2 * df2ThN (parW d n 1) d n < 1 := H1.r21
    linarith
  · have h22 : 3 * (parW d n 1).eta + d * (parW d n ρ.u).Le / (parW d n ρ.u).lam +
        10 * (parW d n 1).eta / ((parW d n 1).eps * (parW d n 1).lam) + 2 * df2Pri (parW d n ρ.u) +
        (parW d n 1).eta * df2Dev (parW d n 1) d n ≤ ((parW d n ρ.u).theta - (parW d n ρ.u).alpha) * (parW d n ρ.u).rho :=
      H1.r22
    have hdev1 : (parW d n 1).eta * df2Dev (parW d n 1) d n = (parW d n 1).eta * df2B1 (parW d n 1) d n + 2 * X :=
      RH.dev_eq
    rw [hD]; rw [hdev1] at h22; linarith
  · rw [hK, hD, hP, hθ, hc1, hγ]; linarith
  · rw [hK, hD, hP, hθ, hc1, hγ]; linarith
  · have e : (parW d n ρ.u).eta * (parW d n ρ.u).kap * (parW d n ρ.u).lam * (parW d n ρ.u).k0 * ρ.y0 =
        (parW d n ρ.u).kap * (parW d n ρ.u).lam * (parW d n ρ.u).k0 * ((parW d n ρ.u).eta * ρ.y0) := by ring
    rw [e, hκ]
    have hc : 1 / 4 * (parW d n ρ.u).lam * (parW d n ρ.u).k0 ≤ 1 / 2 := by
      have := mul_le_mul hlam1 hk0 hk00 (by norm_num)
      linarith
    have hc0 : 0 ≤ 1 / 4 * (parW d n ρ.u).lam * (parW d n ρ.u).k0 := by positivity
    have := mul_le_mul_of_nonneg_left hηy hc0
    linarith
  · have e : (parW d n ρ.u).eta * (parW d n ρ.u).kap * (parW d n ρ.u).lam * (parW d n ρ.u).k0 * ρ.y0 * ρ.b0 =
        (parW d n ρ.u).kap * (parW d n ρ.u).k0 * ((parW d n ρ.u).eta * ρ.y0) * ((parW d n ρ.u).lam * ρ.b0) := by ring
    rw [e, hκ]
    have hηy0 : 0 ≤ (parW d n ρ.u).eta * ρ.y0 := by positivity
    have hlamb0 : 0 ≤ (parW d n ρ.u).lam * ρ.b0 := by have := R.b0_pos; positivity
    have h2 : (parW d n ρ.u).eta * ρ.y0 * ((parW d n ρ.u).lam * ρ.b0) ≤ 1 := mul_le_one₀ hηy hlamb0 hlamb
    have h3 : 1 / 4 * (parW d n ρ.u).k0 ≤ 21 / 80 := by linarith
    have := mul_le_mul h3 h2 (mul_nonneg hηy0 hlamb0) (by norm_num)
    linarith

end AdversarialBco.UW
