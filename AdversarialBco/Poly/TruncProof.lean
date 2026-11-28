/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import Mathlib

@[expose] public section

/-!
# The truncation and compensator core of Lemmas S# and QM: a leaf

`quad_disc_of_rat`: if `0 ≤ a - 2 q b + q² c` for every rational `q` and `0 ≤ c`, then `b² ≤ a c`.
-/

open MeasureTheory ProbabilityTheory

universe u

/-! ## Leaves -/

theorem AdversarialBco.Poly.quad_disc_of_rat (a b c : ℝ) (hc : 0 ≤ c)
    (h : ∀ q : ℚ, 0 ≤ a - 2 * (q : ℝ) * b + (q : ℝ) ^ 2 * c) : b ^ 2 ≤ a * c := by
  by_contra! hlt
  -- hlt : a * c < b ^ 2
  rcases lt_or_eq_of_le hc with (hcpos | hcz)
  · -- case c > 0
    have hcpos' : 0 < c := hcpos
    set e := b ^ 2 - a * c with he
    have hepos : 0 < e := by
      dsimp [e]
      linarith
    have h_identity (t : ℝ) : a - 2 * t * b + t ^ 2 * c = c * (t - b / c) ^ 2 - e / c := by
      field_simp [hcpos'.ne']
      ring
    set s := Real.sqrt e / (2 * c) with hs
    have hsqrt_pos : 0 < Real.sqrt e := Real.sqrt_pos.mpr hepos
    have hden_pos : 0 < 2 * c := by nlinarith
    have hs_pos : 0 < s := div_pos hsqrt_pos hden_pos
    have hsq_sqrt : (Real.sqrt e) ^ 2 = e := Real.sq_sqrt hepos.le
    have hcsq_lt_e : c ^ 2 * s ^ 2 < e := by
      dsimp [s]
      have hcalc : c ^ 2 * ((Real.sqrt e) / (2 * c)) ^ 2 = e / 4 := by
        calc
          c ^ 2 * ((Real.sqrt e) / (2 * c)) ^ 2 = c ^ 2 * ((Real.sqrt e) ^ 2 / ((2 * c) ^ 2)) := by ring
          _ = c ^ 2 * (e / (4 * c ^ 2)) := by rw [hsq_sqrt]; ring
          _ = e / 4 := by field_simp [hcpos'.ne']
      rw [hcalc]
      nlinarith
    have h_lt : b / c - s < b / c + s := by
      nlinarith
    rcases exists_rat_btwn h_lt with ⟨q, hq1, hq2⟩
    -- hq1 : b / c - s < (q : ℝ), hq2 : (q : ℝ) < b / c + s
    have h_abs_lt : |(q : ℝ) - b / c| < s := by
      rw [abs_sub_lt_iff]
      constructor <;> linarith
    have h_abs_lt' := abs_lt.mp h_abs_lt
    -- h_abs_lt' : -s < (q : ℝ) - b / c ∧ (q : ℝ) - b / c < s
    have h_sq_lt : ((q : ℝ) - b / c) ^ 2 < s ^ 2 :=
      sq_lt_sq' h_abs_lt'.1 h_abs_lt'.2
    have hq_val := h q
    rw [h_identity (q : ℝ)] at hq_val
    -- hq_val : 0 ≤ c * ((q : ℝ) - b / c) ^ 2 - e / c
    have h_cs_bound : c * ((q : ℝ) - b / c) ^ 2 < e / c := by
      have h1 : c * ((q : ℝ) - b / c) ^ 2 < c * s ^ 2 := by
        nlinarith
      have h2 : c * s ^ 2 = e / (4 * c) := by
        dsimp [s]
        field_simp [hcpos'.ne']
        nlinarith
      have h3 : e / (4 * c) < e / c :=
        div_lt_div_of_pos_left hepos hcpos' (by nlinarith)
      nlinarith
    nlinarith
  · -- case c = 0
    have hcz' : c = 0 := hcz.symm
    rw [hcz'] at hlt h
    simp at hlt h
    -- hlt : 0 < b ^ 2
    -- h : ∀ q : ℚ, 0 ≤ a - 2 * (q : ℝ) * b
    have hb_ne_zero : b ≠ 0 := by
      intro hbz
      rw [hbz] at hlt
      simp at hlt
    by_cases hb_pos : 0 < b
    · -- b > 0: pick q > a / (2 * b)
      rcases exists_rat_gt (a / (2 * b)) with ⟨q, hq⟩
      have hq_val := h q
      -- hq_val : 2 * (q : ℝ) * b ≤ a
      -- hq : a / (2 * b) < (q : ℝ)
      have ha_lt : a < 2 * (q : ℝ) * b := by
        have hpos : 0 < 2 * b := by nlinarith
        calc
          a = (a / (2 * b)) * (2 * b) := by field_simp [hb_pos.ne']
          _ < (q : ℝ) * (2 * b) := by nlinarith
          _ = 2 * (q : ℝ) * b := by ring
      linarith
    · -- b ≤ 0, and since b ≠ 0, b < 0
      have hb_neg : b < 0 := by
        by_contra! hb_nonneg
        have hbz' : b = 0 := by linarith
        exact hb_ne_zero hbz'
      rcases exists_rat_lt (a / (2 * b)) with ⟨q, hq⟩
      have hq_val := h q
      -- hq_val : 2 * (q : ℝ) * b ≤ a
      -- hq : (q : ℝ) < a / (2 * b)
      have ha_lt : a < 2 * (q : ℝ) * b := by
        have hneg : 2 * b < 0 := by nlinarith
        calc
          a = (a / (2 * b)) * (2 * b) := by field_simp [hb_neg.ne']
          _ < (q : ℝ) * (2 * b) := by nlinarith
          _ = 2 * (q : ℝ) * b := by ring
      linarith


