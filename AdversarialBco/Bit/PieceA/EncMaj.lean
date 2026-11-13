/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.PieceA.EncR

@[expose] public section

/-!
# Piece A: the enclosure lemma over `EncR`

Each field of `Bud.EncOK` that is an inequality, over the abstract record `EncR` of Bit/PieceA/EncR.lean: the
relative errors of PARAM's fields against their reference values, in the stated directions (the enclosure lemma). The
bounds of `λ'`, `η'`, `sig2'` and `R'` are sharper than `2^{-p-4}`: `κ_c'`, `A_0`, `B_0`, `s'_b` and
`W'` use them. This file depends on Mathlib only.
-/

namespace AdversarialBco.Bit.PieceA.EncR.OK

open AdversarialBco.Bit.PieceA AdversarialBco.Bit.PieceA.EncR

variable {r : EncR}

theorem base (h : r.OK) : 0 < r.d ∧ 0 < r.n ∧ 0 < r.Ne ∧ 0 < r.Le ∧ 0 < r.Lp ∧ r.Lp ≤ r.Lh ∧ r.n ≤ r.Ne ∧
    r.d ≤ r.Ne ∧ 1 ≤ Real.sqrt r.d ∧ 1 ≤ Real.sqrt r.n ∧ r.eq ≤ r.tp / 2 ^ 18 ∧ r.eF * r.Ne ^ 2 ≤ r.tp / 2 ^ 40 := by
  have hpos_d : 0 < r.d :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) h.hd
  have hpos_n : 0 < r.n :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) h.hn
  have hpos_Ne : 0 < r.Ne := by
    rw [h.hNe]
    positivity
  have hpos_Le : 0 < r.Le :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 17467) h.hLe
  have hpos_Lp : 0 < r.Lp := by
    have htp_div_pos : 0 ≤ r.tp / 2 ^ 9 := div_nonneg (le_of_lt h.htp0) (by positivity)
    have hLe_sub_pos : 0 < r.Le - r.tp / 2 ^ 9 := by
      have : r.tp / 2 ^ 9 < r.Le := by
        have htp_le : r.tp ≤ (1 : ℝ) / 2 ^ 160 := h.htp1
        have htp_div_le : r.tp / 2 ^ 9 ≤ ((1 : ℝ) / 2 ^ 160) / 2 ^ 9 :=
          div_le_div_of_nonneg_right htp_le (by positivity)
        have h_small : ((1 : ℝ) / 2 ^ 160) / 2 ^ 9 < 17467 := by
          have h_eq : ((1 : ℝ) / 2 ^ 160) / 2 ^ 9 = (1 : ℝ) / ((2 : ℝ) ^ 169) := by
            calc
              ((1 : ℝ) / 2 ^ 160) / 2 ^ 9 = (1 : ℝ) / ((2 ^ 160 : ℝ) * (2 ^ 9 : ℝ)) := by ring
              _ = (1 : ℝ) / ((2 : ℝ) ^ 169) := by norm_num
          rw [h_eq]
          have hpos : 0 < (2 : ℝ) ^ 169 := by positivity
          have h_lt_one : (1 : ℝ) / ((2 : ℝ) ^ 169) < 1 :=
            (div_lt_one hpos).mpr (by
              have h_one_lt : (1 : ℝ) < (2 : ℝ) ^ 169 := by
                have : (2 : ℝ) ^ 0 < (2 : ℝ) ^ 169 :=
                  pow_lt_pow_right₀ (by norm_num : 1 < (2 : ℝ)) (by norm_num : 0 < 169)
                simpa using this
              exact h_one_lt)
          have h_one_lt_17467 : (1 : ℝ) < 17467 := by norm_num
          linarith
        calc
          r.tp / 2 ^ 9 ≤ ((1 : ℝ) / 2 ^ 160) / 2 ^ 9 := htp_div_le
          _ < 17467 := h_small
          _ ≤ r.Le := h.hLe
      linarith
    linarith [h.hLp1, hLe_sub_pos]
  have hLp_le_Lh : r.Lp ≤ r.Lh := le_trans h.hLp2 h.hLh1
  have hn_le_Ne : r.n ≤ r.Ne := by
    rw [h.hNe]
    have h_d_ge_1 : 1 ≤ r.d := h.hd
    have h_n_ge_1 : 1 ≤ r.n := h.hn
    have h_d3_ge_d : r.d ≤ r.d ^ 3 := by
      have h_sq_ge_one : 1 ≤ r.d ^ 2 := by
        have : (1 : ℝ) ^ 2 ≤ r.d ^ 2 := pow_le_pow_left₀ (by norm_num) h_d_ge_1 2
        simpa using this
      calc
        r.d = r.d * 1 := by ring
        _ ≤ r.d * (r.d ^ 2) := by gcongr
        _ = r.d ^ 3 := by ring
    have h_n4_ge_n : r.n ≤ r.n ^ 4 := by
      have h_cube_ge_one : 1 ≤ r.n ^ 3 := by
        have : (1 : ℝ) ^ 3 ≤ r.n ^ 3 := pow_le_pow_left₀ (by norm_num) h_n_ge_1 3
        simpa using this
      calc
        r.n = r.n * 1 := by ring
        _ ≤ r.n * (r.n ^ 3) := by gcongr
        _ = r.n ^ 4 := by ring
    have h_factor : (1 : ℝ) ≤ 15 * 2 ^ 17 := by norm_num
    nlinarith
  have hd_le_Ne : r.d ≤ r.Ne := by
    rw [h.hNe]
    have h_d_ge_1 : 1 ≤ r.d := h.hd
    have h_n_ge_1 : 1 ≤ r.n := h.hn
    have h_d3_ge_d : r.d ≤ r.d ^ 3 := by
      have h_sq_ge_one : 1 ≤ r.d ^ 2 := by
        have : (1 : ℝ) ^ 2 ≤ r.d ^ 2 := pow_le_pow_left₀ (by norm_num) h_d_ge_1 2
        simpa using this
      calc
        r.d = r.d * 1 := by ring
        _ ≤ r.d * (r.d ^ 2) := by gcongr
        _ = r.d ^ 3 := by ring
    have h_n4_ge_1 : 1 ≤ r.n ^ 4 := by
      have : (1 : ℝ) ^ 4 ≤ r.n ^ 4 := pow_le_pow_left₀ (by norm_num) h_n_ge_1 4
      simpa using this
    have h_factor : (1 : ℝ) ≤ 15 * 2 ^ 17 := by norm_num
    nlinarith
  have h_sqrt_d : 1 ≤ Real.sqrt r.d :=
    Real.one_le_sqrt.mpr h.hd
  have h_sqrt_n : 1 ≤ Real.sqrt r.n :=
    Real.one_le_sqrt.mpr h.hn
  have heq_le : r.eq ≤ r.tp / 2 ^ 18 := by
    have hpos_eq : 0 ≤ r.eq := le_of_lt h.heq0
    calc
      r.eq = r.eq * 1 := by ring
      _ ≤ r.eq * (1 + r.Le) := by
        gcongr
        linarith
      _ ≤ r.tp / 2 ^ 18 := h.heq1
  have heF_le : r.eF * r.Ne ^ 2 ≤ r.tp / 2 ^ 40 := by
    have h_d4_ge_1 : 1 ≤ r.d ^ 4 := by
      have h_d_ge_1 : 1 ≤ r.d := h.hd
      have : (1 : ℝ) ^ 4 ≤ r.d ^ 4 := pow_le_pow_left₀ (by norm_num) h_d_ge_1 4
      simpa using this
    have hpos_2pow40 : 0 < (2 : ℝ) ^ 40 := by positivity
    have hpos_eF : 0 ≤ r.eF := le_of_lt h.heF0
    have h_mul_ineq : r.eF * r.Ne ^ 2 * (2 : ℝ) ^ 40 ≤ r.tp := by
      calc
        r.eF * r.Ne ^ 2 * (2 : ℝ) ^ 40 = r.eF * ((2 : ℝ) ^ 40 * r.Ne ^ 2) := by ring
        _ ≤ r.eF * ((2 : ℝ) ^ 40 * r.Ne ^ 2 * r.d ^ 4) := by
          refine mul_le_mul_of_nonneg_left ?_ hpos_eF
          have hpos_2pow40' : 0 ≤ (2 : ℝ) ^ 40 := by positivity
          have hpos_Ne2 : 0 ≤ r.Ne ^ 2 := pow_two_nonneg _
          nlinarith
        _ ≤ r.tp := h.heF1
    calc
      r.eF * r.Ne ^ 2 = (r.eF * r.Ne ^ 2 * (2 : ℝ) ^ 40) / (2 : ℝ) ^ 40 := by
        field_simp [hpos_2pow40.ne.symm]
      _ ≤ r.tp / (2 : ℝ) ^ 40 := div_le_div_of_nonneg_right h_mul_ineq (by positivity)
  exact ⟨hpos_d, hpos_n, hpos_Ne, hpos_Le, hpos_Lp, hLp_le_Lh, hn_le_Ne, hd_le_Ne, h_sqrt_d, h_sqrt_n, heq_le, heF_le⟩

theorem Lp_rat (h : r.OK) : 1 ≤ r.Le / r.Lp ∧ r.Le / r.Lp ≤ 1 + r.tp / 2 ^ 22 ∧ 1 - r.tp / 2 ^ 22 ≤ r.Lp / r.Le ∧
    r.Lp / r.Le ≤ 1 ∧ 1 ≤ r.Lh / r.Le ∧ r.Lh / r.Le ≤ 1 + r.tp / 2 ^ 22 := by
  have hLp1 := h.hLp1
  have hLp2 := h.hLp2
  have hLh1 := h.hLh1
  have hLh2 := h.hLh2
  have hLe := h.hLe
  have htp0 := h.htp0
  have htp1 := h.htp1
  have hLe_pos : 0 < r.Le := by linarith
  have htp_pos : 0 < r.tp := htp0
  have hLe_ge_2pow13 : (2 : ℝ) ^ 13 ≤ r.Le := by
    have h8192 : (2 : ℝ) ^ 13 = 8192 := by norm_num
    have h8192_le_17467 : (8192 : ℝ) ≤ 17467 := by norm_num
    linarith
  have hLp_pos : 0 < r.Lp := by
    have hpos : 0 < r.Le - r.tp / 2 ^ 9 := by
      have hbound : r.tp / 2 ^ 9 ≤ 1 / 2 ^ 169 := by
        calc
          r.tp / 2 ^ 9 ≤ (1 / 2 ^ 160) / 2 ^ 9 := by gcongr
          _ = 1 / (2 ^ 160 * 2 ^ 9) := by ring
          _ = 1 / 2 ^ 169 := by norm_num
      have h17467 : (1 : ℝ) / 2 ^ 169 < 17467 := by norm_num
      linarith
    linarith
  have hLp_ge_2pow13 : (2 : ℝ) ^ 13 ≤ r.Lp := by
    have hbound : r.tp / 2 ^ 9 ≤ 1 / 2 ^ 169 := by
      calc
        r.tp / 2 ^ 9 ≤ (1 / 2 ^ 160) / 2 ^ 9 := by gcongr
        _ = 1 / (2 ^ 160 * 2 ^ 9) := by ring
        _ = 1 / 2 ^ 169 := by norm_num
    have h17467 : (1 : ℝ) / 2 ^ 169 < 17467 := by norm_num
    linarith
  have h_div_ineq_Le : (r.tp / 2 ^ 9) / r.Le ≤ r.tp / 2 ^ 22 := by
    have hkey : (r.tp / 2 ^ 9) * (2 ^ 22) ≤ r.tp * r.Le := by
      calc
        (r.tp / 2 ^ 9) * (2 ^ 22) = r.tp * ((2 ^ 22) / (2 ^ 9)) := by ring
        _ = r.tp * (2 ^ 13) := by norm_num
        _ ≤ r.tp * r.Le := by gcongr
    exact ((div_le_div_iff₀ hLe_pos (by norm_num : 0 < (2 : ℝ) ^ 22)).mpr hkey)
  have h_div_ineq_Lp : (r.tp / 2 ^ 9) / r.Lp ≤ r.tp / 2 ^ 22 := by
    have hkey : (r.tp / 2 ^ 9) * (2 ^ 22) ≤ r.tp * r.Lp := by
      calc
        (r.tp / 2 ^ 9) * (2 ^ 22) = r.tp * ((2 ^ 22) / (2 ^ 9)) := by ring
        _ = r.tp * (2 ^ 13) := by norm_num
        _ ≤ r.tp * r.Lp := by gcongr
    exact ((div_le_div_iff₀ hLp_pos (by norm_num : 0 < (2 : ℝ) ^ 22)).mpr hkey)
  have h1 : 1 ≤ r.Le / r.Lp := (one_le_div hLp_pos).mpr hLp2
  have h2 : r.Lp / r.Le ≤ 1 := (div_le_one hLe_pos).mpr hLp2
  have h3 : 1 ≤ r.Lh / r.Le := (one_le_div hLe_pos).mpr hLh1
  have h4 : r.Lh / r.Le ≤ 1 + r.tp / 2 ^ 22 := by
    calc
      r.Lh / r.Le ≤ (r.Le + r.tp / 2 ^ 9) / r.Le :=
        div_le_div_of_nonneg_right hLh2 hLe_pos.le
      _ = r.Le / r.Le + (r.tp / 2 ^ 9) / r.Le := by ring
      _ = 1 + (r.tp / 2 ^ 9) / r.Le := by field_simp [hLe_pos.ne.symm]
      _ ≤ 1 + r.tp / 2 ^ 22 := by gcongr
  have h5 : r.Le / r.Lp ≤ 1 + r.tp / 2 ^ 22 := by
    have hLe_le : r.Le ≤ r.Lp + r.tp / 2 ^ 9 := by linarith
    calc
      r.Le / r.Lp ≤ (r.Lp + r.tp / 2 ^ 9) / r.Lp :=
        div_le_div_of_nonneg_right hLe_le hLp_pos.le
      _ = r.Lp / r.Lp + (r.tp / 2 ^ 9) / r.Lp := by ring
      _ = 1 + (r.tp / 2 ^ 9) / r.Lp := by field_simp [hLp_pos.ne.symm]
      _ ≤ 1 + r.tp / 2 ^ 22 := by gcongr
  have h6 : 1 - r.tp / 2 ^ 22 ≤ r.Lp / r.Le := by
    have hsub : r.Le - r.Lp ≤ r.tp / 2 ^ 9 := by linarith
    have hkey : r.tp / 2 ^ 9 ≤ r.tp * r.Le / 2 ^ 22 := by
      have hkey' : (r.tp / 2 ^ 9) * (2 ^ 22) ≤ r.tp * r.Le := by
        calc
          (r.tp / 2 ^ 9) * (2 ^ 22) = r.tp * ((2 ^ 22) / (2 ^ 9)) := by ring
          _ = r.tp * (2 ^ 13) := by norm_num
          _ ≤ r.tp * r.Le := by gcongr
      have htemp := (div_le_div_iff₀ (by norm_num : 0 < (1 : ℝ))
        (by norm_num : 0 < (2 : ℝ) ^ 22)).mpr (by
          simpa [mul_one] using hkey')
      simpa [div_one] using htemp
    have h_combined : r.Le - r.Lp ≤ r.tp * r.Le / 2 ^ 22 := le_trans hsub hkey
    have hgoal : (1 - r.tp / 2 ^ 22) * r.Le ≤ r.Lp := by
      linarith
    exact (le_div_iff₀ hLe_pos).mpr hgoal
  exact ⟨h1, h5, h6, h2, h3, h4⟩

theorem root_rat (h : r.OK) : 1 - r.eq ≤ r.rd / Real.sqrt r.d ∧ r.rd / Real.sqrt r.d ≤ 1 ∧
    (r.rd + r.eq) / Real.sqrt r.d ≤ 1 + r.eq ∧ 1 ≤ Real.sqrt r.n / r.rn ∧ Real.sqrt r.n / r.rn ≤ 1 + r.eq := by
  have hdpos : 0 < r.d := by linarith [h.hd]
  have hnpos : 0 < r.n := by linarith [h.hn]
  have hsqrdpos : 0 < Real.sqrt r.d := Real.sqrt_pos.mpr hdpos
  have hsqrnpos : 0 < Real.sqrt r.n := Real.sqrt_pos.mpr hnpos
  have hsqrd_ge_one : 1 ≤ Real.sqrt r.d := (h.base).2.2.2.2.2.2.2.2.1
  have hsqrn_ge_one : 1 ≤ Real.sqrt r.n := (h.base).2.2.2.2.2.2.2.2.2.1
  have heqpos : 0 ≤ r.eq := by linarith [h.heq0]
  have hrnpos : 0 < r.rn := by linarith [h.hrn0]
  have h1 : 1 - r.eq ≤ r.rd / Real.sqrt r.d := by
    have htmp : Real.sqrt r.d - r.eq ≤ r.rd := by
      simpa [add_sub_cancel_right] using sub_le_sub_right h.hrd2 r.eq
    have hdiv : (Real.sqrt r.d - r.eq) / Real.sqrt r.d ≤ r.rd / Real.sqrt r.d :=
      ((div_le_div_iff_of_pos_right hsqrdpos).mpr htmp)
    have hsubdiv : (Real.sqrt r.d - r.eq) / Real.sqrt r.d = 1 - r.eq / Real.sqrt r.d := by
      field_simp [hsqrdpos.ne']
    have heqdiv : r.eq / Real.sqrt r.d ≤ r.eq := by
      have h : r.eq / Real.sqrt r.d ≤ r.eq / 1 :=
        div_le_div_of_nonneg_left heqpos (by norm_num) hsqrd_ge_one
      simpa using h
    have hsub : 1 - r.eq ≤ 1 - r.eq / Real.sqrt r.d := by linarith
    calc
      1 - r.eq ≤ 1 - r.eq / Real.sqrt r.d := hsub
      _ = (Real.sqrt r.d - r.eq) / Real.sqrt r.d := by rw [hsubdiv]
      _ ≤ r.rd / Real.sqrt r.d := hdiv
  have h2 : r.rd / Real.sqrt r.d ≤ 1 :=
    (div_le_one hsqrdpos).mpr h.hrd1
  have h3 : (r.rd + r.eq) / Real.sqrt r.d ≤ 1 + r.eq := by
    have hsum : r.rd + r.eq ≤ Real.sqrt r.d + r.eq := by
      simpa [add_comm, add_left_comm, add_assoc] using add_le_add_right h.hrd1 r.eq
    have hdiv : (r.rd + r.eq) / Real.sqrt r.d ≤ (Real.sqrt r.d + r.eq) / Real.sqrt r.d :=
      ((div_le_div_iff_of_pos_right hsqrdpos).mpr hsum)
    have hright : (Real.sqrt r.d + r.eq) / Real.sqrt r.d = 1 + r.eq / Real.sqrt r.d := by
      field_simp [hsqrdpos.ne']
    have heqdiv : r.eq / Real.sqrt r.d ≤ r.eq := by
      have h : r.eq / Real.sqrt r.d ≤ r.eq / 1 :=
        div_le_div_of_nonneg_left heqpos (by norm_num) hsqrd_ge_one
      simpa using h
    have hright' : 1 + r.eq / Real.sqrt r.d ≤ 1 + r.eq := by linarith
    calc
      (r.rd + r.eq) / Real.sqrt r.d ≤ (Real.sqrt r.d + r.eq) / Real.sqrt r.d := hdiv
      _ = 1 + r.eq / Real.sqrt r.d := by rw [hright]
      _ ≤ 1 + r.eq := hright'
  have h4 : 1 ≤ Real.sqrt r.n / r.rn :=
    (one_le_div hrnpos).mpr h.hrn1
  have h5 : Real.sqrt r.n / r.rn ≤ 1 + r.eq := by
    have htmp : Real.sqrt r.n ≤ r.rn + r.eq := h.hrn2
    have hdiv : Real.sqrt r.n / r.rn ≤ (r.rn + r.eq) / r.rn :=
      ((div_le_div_iff_of_pos_right hrnpos).mpr htmp)
    have hright : (r.rn + r.eq) / r.rn = 1 + r.eq / r.rn := by
      field_simp [hrnpos.ne']
    have heqdiv : r.eq / r.rn ≤ r.eq := by
      have h : r.eq / r.rn ≤ r.eq / 1 :=
        div_le_div_of_nonneg_left heqpos (by norm_num) (by linarith [h.hrn0])
      simpa using h
    have hright' : 1 + r.eq / r.rn ≤ 1 + r.eq := by linarith
    calc
      Real.sqrt r.n / r.rn ≤ (r.rn + r.eq) / r.rn := hdiv
      _ = 1 + r.eq / r.rn := by rw [hright]
      _ ≤ 1 + r.eq := hright'
  exact And.intro h1 (And.intro h2 (And.intro h3 (And.intro h4 h5)))

theorem Le_rel (h : r.OK) : |r.Lp / r.Le - 1| ≤ r.tp / 16 := by
  rcases h.Lp_rat with ⟨_, _, hlow, hhigh, _, _⟩
  have hdiv : r.Lp / r.Le - 1 ≤ 0 := by linarith
  have habs : |r.Lp / r.Le - 1| = 1 - r.Lp / r.Le := by
    rw [abs_of_nonpos hdiv]
    ring
  rw [habs]
  have hineq : 1 - r.Lp / r.Le ≤ r.tp / (2 : ℝ) ^ 22 := by linarith
  have htp_pos : 0 < r.tp := h.htp0
  have hpow : (16 : ℝ) ≤ (2 : ℝ) ^ 22 := by norm_num
  have hpos_pow : 0 < (2 : ℝ) ^ 22 := by norm_num
  have hpos_16 : 0 < (16 : ℝ) := by norm_num
  have h_one_div : 1 / (2 : ℝ) ^ 22 ≤ 1 / (16 : ℝ) :=
    (one_div_le_one_div hpos_pow hpos_16).mpr hpow
  have hfinal : r.tp / (2 : ℝ) ^ 22 ≤ r.tp / 16 := by
    calc
      r.tp / (2 : ℝ) ^ 22 = r.tp * (1 / (2 : ℝ) ^ 22) := by ring
      _ ≤ r.tp * (1 / (16 : ℝ)) := mul_le_mul_of_nonneg_left h_one_div htp_pos.le
      _ = r.tp / 16 := by ring
  linarith

theorem eps_le (h : r.OK) : r.eps ≤ r.ep := by
  unfold eps
  -- Goal: 14500 * r.d * Real.sqrt r.d * r.Le ^ 5 / Real.sqrt r.n ≤ r.ep
  -- h.hep1: 14500 * r.d * (r.rd + r.eq) * r.Lh ^ 5 / r.rn ≤ r.ep
  -- So it suffices to show LHS ≤ the expression in h.hep1
  apply le_trans ?_ h.hep1
  -- Goal: 14500 * r.d * Real.sqrt r.d * r.Le ^ 5 / Real.sqrt r.n ≤
  --       14500 * r.d * (r.rd + r.eq) * r.Lh ^ 5 / r.rn
  have hdpos : 0 < r.d := by
    have hd1 : 1 ≤ r.d := h.hd
    linarith
  have hnpos : 0 < r.n := by
    have hn1 : 1 ≤ r.n := h.hn
    linarith
  have hLe_nonneg : 0 ≤ r.Le := by
    have hLe1 : 17467 ≤ r.Le := h.hLe
    linarith
  have hLh_nonneg : 0 ≤ r.Lh := by
    linarith [h.hLe, h.hLh1]
  have hsqrtn_pos : 0 < Real.sqrt r.n := Real.sqrt_pos.mpr hnpos
  have hrn_pos : 0 < r.rn := by
    have hrn0 : 1 ≤ r.rn := h.hrn0
    linarith
  -- Numerator inequality: A ≤ B where
  -- A = 14500 * r.d * Real.sqrt r.d * r.Le ^ 5
  -- B = 14500 * r.d * (r.rd + r.eq) * r.Lh ^ 5
  have hrd_pos : 0 < r.rd := by
    have hrd1 : 1 ≤ r.rd := h.hrd0
    linarith
  have heq_nonneg : 0 ≤ r.eq := by linarith [h.heq0]
  have hLh_nonneg' : 0 ≤ r.Lh := by linarith [h.hLe, h.hLh1]
  have h_num : 14500 * r.d * Real.sqrt r.d * r.Le ^ 5 ≤ 14500 * r.d * (r.rd + r.eq) * r.Lh ^ 5 := by
    -- Goal: (((14500*d) * sqrt_d) * Le^5) ≤ (((14500*d) * (rd+eq)) * Lh^5)
    -- Apply mul_le_mul with:
    --   a = ((14500*d) * sqrt_d), c = ((14500*d) * (rd+eq))
    --   b = Le^5, d = Lh^5
    refine mul_le_mul ?_ (pow_le_pow_left₀ hLe_nonneg h.hLh1 5) ?_ ?_
    · -- (14500*d) * sqrt_d ≤ (14500*d) * (rd+eq)
      refine mul_le_mul (le_refl _) h.hrd2 ?_ ?_
      · exact Real.sqrt_nonneg _
      · -- 0 ≤ 14500 * r.d
        have h14500 : 0 ≤ (14500 : ℝ) := by norm_num
        have hd_nonneg : 0 ≤ r.d := by linarith
        nlinarith
    · -- 0 ≤ Le^5
      have hLe5_nonneg : 0 ≤ r.Le ^ 5 := pow_nonneg hLe_nonneg 5
      exact hLe5_nonneg
    · -- 0 ≤ (14500*d) * (rd+eq)
      have h14500d_nonneg : 0 ≤ 14500 * r.d := by
        have h14500 : 0 ≤ (14500 : ℝ) := by norm_num
        have hd_nonneg : 0 ≤ r.d := by linarith
        nlinarith
      have hsum_nonneg : 0 ≤ r.rd + r.eq := by linarith [hrd_pos, heq_nonneg]
      nlinarith
  -- Split into two steps: A / sqrt_n ≤ B / sqrt_n ≤ B / rn
  have h1 : 14500 * r.d * Real.sqrt r.d * r.Le ^ 5 / Real.sqrt r.n ≤
           14500 * r.d * (r.rd + r.eq) * r.Lh ^ 5 / Real.sqrt r.n :=
    div_le_div_of_nonneg_right h_num hsqrtn_pos.le
  have h_num_nonneg : 0 ≤ 14500 * r.d * (r.rd + r.eq) * r.Lh ^ 5 := by positivity
  have h_denom : r.rn ≤ Real.sqrt r.n := h.hrn1
  have h2 : 14500 * r.d * (r.rd + r.eq) * r.Lh ^ 5 / Real.sqrt r.n ≤
           14500 * r.d * (r.rd + r.eq) * r.Lh ^ 5 / r.rn :=
    div_le_div_of_nonneg_left h_num_nonneg hrn_pos h_denom
  exact le_trans h1 h2

theorem eps_rel (h : r.OK) : r.ep ≤ r.eps * (1 + r.tp / 16) := by
  have hbase := base h
  have hLp_rat := Lp_rat h
  have hroot_rat := root_rat h
  rcases hbase with ⟨hd_pos, hn_pos, hNe_pos, hLe_pos, hLp_pos, hLp_le_Lh, hn_le_Ne, hd_le_Ne, hsqrt_d, hsqrt_n, heq_le, heF_Ne⟩
  rcases hLp_rat with ⟨hLe_div_Lp, hLp_div_Le_le, hLp_div_Le_ge, hLp_div_Le_le_one, hLe_div_Lh, hLh_div_Le_le⟩
  rcases hroot_rat with ⟨h_rd_sqrt_d_le, h_rd_sqrt_d_le_one, h_rd_eq_le, h_sqrt_n_rn_le_one, h_sqrt_n_rn_le⟩
  have htp_pos : 0 < r.tp := h.htp0
  have heq_pos : 0 < r.eq := h.heq0
  have heF_pos : 0 < r.eF := h.heF0
  have hsqrt_d_pos : 0 < Real.sqrt r.d := Real.sqrt_pos.mpr (by linarith)
  have hsqrt_n_pos : 0 < Real.sqrt r.n := Real.sqrt_pos.mpr (by linarith)
  have hLe_pos' : 0 < r.Le := by linarith
  have hrn_pos : 0 < r.rn := by
    have : 1 ≤ r.rn := h.hrn0
    linarith
  have heps_nonneg : 0 ≤ r.eps := by
    dsimp [EncR.eps]
    positivity
  set X := 14500 * r.d * (r.rd + r.eq) * r.Lh ^ 5 / r.rn with hX_def
  have h_ep_le_X_plus_eF : r.ep ≤ X + r.eF := h.hep2
  -- key algebraic identity: X = eps * ((r.rd + r.eq) / sqrt d) * (Lh/Le)^5 * (sqrt n / rn)
  have hX_eq : X = r.eps * ((r.rd + r.eq) / Real.sqrt r.d) * ((r.Lh / r.Le) ^ 5) * (Real.sqrt r.n / r.rn) := by
    dsimp [X, EncR.eps]
    field_simp [hsqrt_d_pos.ne.symm, hsqrt_n_pos.ne.symm, hLe_pos'.ne.symm, hrn_pos.ne.symm]
  have h_factor1 : (r.rd + r.eq) / Real.sqrt r.d ≤ 1 + r.eq := h_rd_eq_le
  have h_factor2 : Real.sqrt r.n / r.rn ≤ 1 + r.eq := h_sqrt_n_rn_le
  have hLh_div_Le_nonneg : 0 ≤ r.Lh / r.Le := by positivity
  have h_one_plus_tp22_nonneg' : 0 ≤ 1 + r.tp / 2 ^ 22 := by positivity
  have h_factor3 : (r.Lh / r.Le) ^ 5 ≤ (1 + r.tp / 2 ^ 22) ^ 5 := by
    induction' 5 with k ih
    · norm_num
    · rw [pow_succ, pow_succ]
      have hb : 0 ≤ 1 + r.tp / 2 ^ 22 := h_one_plus_tp22_nonneg'
      have hbk : 0 ≤ (1 + r.tp / 2 ^ 22) ^ k := pow_nonneg hb k
      exact mul_le_mul ih hLh_div_Le_le hLh_div_Le_nonneg hbk
  -- X ≤ eps * (1 + eq)^2 * (1 + tp/2^22)^5
  have hX_le_eps_mul : X ≤ r.eps * ((1 + r.eq) ^ 2) * ((1 + r.tp / 2 ^ 22) ^ 5) := by
    calc
      X = r.eps * ((r.rd + r.eq) / Real.sqrt r.d) * ((r.Lh / r.Le) ^ 5) * (Real.sqrt r.n / r.rn) := hX_eq
      _ ≤ r.eps * (1 + r.eq) * ((r.Lh / r.Le) ^ 5) * (Real.sqrt r.n / r.rn) := by gcongr
      _ ≤ r.eps * (1 + r.eq) * ((1 + r.tp / 2 ^ 22) ^ 5) * (Real.sqrt r.n / r.rn) := by gcongr
      _ ≤ r.eps * (1 + r.eq) * ((1 + r.tp / 2 ^ 22) ^ 5) * (1 + r.eq) := by gcongr
      _ = r.eps * ((1 + r.eq) ^ 2) * ((1 + r.tp / 2 ^ 22) ^ 5) := by ring
  -- (1+eq) ≤ (1+tp/2^18) and (1+tp/2^22) ≤ (1+tp/2^18)
  have h_one_plus_eq_le : 1 + r.eq ≤ 1 + r.tp / 2 ^ 18 := by linarith
  have h_one_plus_tp22_le : 1 + r.tp / 2 ^ 22 ≤ 1 + r.tp / 2 ^ 18 := by
    have h : r.tp / 2 ^ 22 ≤ r.tp / 2 ^ 18 :=
      div_le_div_of_nonneg_left htp_pos.le (by norm_num) (by norm_num)
    linarith
  have h_sq_bound : (1 + r.eq) ^ 2 ≤ (1 + r.tp / 2 ^ 18) ^ 2 := by
    nlinarith
  have h_one_plus_tp22_nonneg'' : 0 ≤ 1 + r.tp / 2 ^ 22 := by positivity
  have h_pow5_bound : (1 + r.tp / 2 ^ 22) ^ 5 ≤ (1 + r.tp / 2 ^ 18) ^ 5 := by
    induction' 5 with k ih
    · norm_num
    · rw [pow_succ, pow_succ]
      have hb : 0 ≤ 1 + r.tp / 2 ^ 18 := by positivity
      have hbk : 0 ≤ (1 + r.tp / 2 ^ 18) ^ k := pow_nonneg hb k
      exact mul_le_mul ih h_one_plus_tp22_le h_one_plus_tp22_nonneg'' hbk
  -- X ≤ eps * (1 + tp/2^18)^7
  have hX_le_eps_pow7 : X ≤ r.eps * ((1 + r.tp / 2 ^ 18) ^ 7) := by
    calc
      X ≤ r.eps * ((1 + r.eq) ^ 2) * ((1 + r.tp / 2 ^ 22) ^ 5) := hX_le_eps_mul
      _ ≤ r.eps * ((1 + r.tp / 2 ^ 18) ^ 2) * ((1 + r.tp / 2 ^ 18) ^ 5) := by gcongr
      _ = r.eps * ((1 + r.tp / 2 ^ 18) ^ 7) := by ring
  -- (1 + tp/2^18)^7 ≤ 1 + tp/32
  have htp_le_one : r.tp ≤ 1 := by
    have h : r.tp ≤ 1 / 2 ^ 160 := h.htp1
    calc
      r.tp ≤ 1 / 2 ^ 160 := h
      _ ≤ 1 := by norm_num
  set a := r.tp / 2 ^ 18 with ha_def
  have ha_nonneg : 0 ≤ a := by
    dsimp [a]; positivity
  have ha_le_one : a ≤ 1 := by
    dsimp [a]
    refine (div_le_one ?_).mpr ?_
    · positivity
    · linarith
  have ha_le_120th : a ≤ 1/120 := by
    dsimp [a]
    calc
      r.tp / 2 ^ 18 ≤ 1 / 2 ^ 18 := div_le_div_of_nonneg_right htp_le_one (by positivity)
      _ ≤ 1/120 := by norm_num
  have h_pow7_bound : (1 + a) ^ 7 ≤ 1 + 8 * a := by
    -- (1+a)^7 = 1 + 7a + 21a^2 + 35a^3 + 35a^4 + 21a^5 + 7a^6 + a^7
    -- ≤ 1 + 7a + 120*a^2  (since a^k ≤ a^2 for k ≥ 2)
    -- ≤ 1 + 7a + a = 1 + 8a  (since a ≤ 1/120)
    have h_expand : (1 + a) ^ 7 = 1 + 7 * a + 21 * a ^ 2 + 35 * a ^ 3 + 35 * a ^ 4
        + 21 * a ^ 5 + 7 * a ^ 6 + a ^ 7 := by
      ring
    rw [h_expand]
    have h_pow_le_sq {k : ℕ} (hk : 2 ≤ k) : a ^ k ≤ a ^ 2 := by
      refine pow_le_pow_of_le_one ha_nonneg ha_le_one hk
    have h_tail_le : 21 * a ^ 2 + 35 * a ^ 3 + 35 * a ^ 4 + 21 * a ^ 5 + 7 * a ^ 6 + a ^ 7 ≤ 120 * a ^ 2 := by
      have h3 : a ^ 3 ≤ a ^ 2 := h_pow_le_sq (by omega)
      have h4 : a ^ 4 ≤ a ^ 2 := h_pow_le_sq (by omega)
      have h5 : a ^ 5 ≤ a ^ 2 := h_pow_le_sq (by omega)
      have h6 : a ^ 6 ≤ a ^ 2 := h_pow_le_sq (by omega)
      have h7 : a ^ 7 ≤ a ^ 2 := h_pow_le_sq (by omega)
      linarith
    have h_120a2_le_a : 120 * a ^ 2 ≤ a := by
      calc
        120 * a ^ 2 = a * (120 * a) := by ring
        _ ≤ a * 1 := by
          gcongr
          linarith
        _ = a := by ring
    linarith
  have h_pow7_le_one_plus_tp32 : (1 + a) ^ 7 ≤ 1 + r.tp / 32 := by
    calc
      (1 + a) ^ 7 ≤ 1 + 8 * a := h_pow7_bound
      _ = 1 + 8 * (r.tp / 2 ^ 18) := rfl
      _ = 1 + r.tp / 2 ^ 15 := by ring
      _ ≤ 1 + r.tp / 32 := by
        have hdiv : r.tp / 2 ^ 15 ≤ r.tp / 32 :=
          div_le_div_of_nonneg_left htp_pos.le (by norm_num) (by norm_num)
        linarith
  -- X ≤ eps * (1 + tp/32)
  have hX_le_eps_tp32 : X ≤ r.eps * (1 + r.tp / 32) := by
    calc
      X ≤ r.eps * ((1 + r.tp / 2 ^ 18) ^ 7) := hX_le_eps_pow7
      _ = r.eps * (1 + a) ^ 7 := by simp [a]
      _ ≤ r.eps * (1 + r.tp / 32) := by gcongr
  -- Now eF ≤ eps * (tp/32)
  -- From heF_Ne: r.eF * r.Ne^2 ≤ r.tp / 2^40
  have heF_bound : r.eF ≤ r.tp / (2 ^ 40 * r.Ne ^ 2) := by
    calc
      r.eF = (r.eF * r.Ne ^ 2) / r.Ne ^ 2 := by
        field_simp [show r.Ne ^ 2 ≠ 0 from by positivity]
      _ ≤ (r.tp / 2 ^ 40) / r.Ne ^ 2 := by gcongr
      _ = r.tp / (2 ^ 40 * r.Ne ^ 2) := by ring
  -- Need: r.tp / (2^40 * Ne^2) ≤ eps * (tp/32)
  have hNe_ge_one : 1 ≤ r.Ne := by
    have hNe_eq : r.Ne = 15 * 2 ^ 17 * r.d ^ 3 * r.n ^ 4 := h.hNe
    rw [hNe_eq]
    have hd1 : 1 ≤ r.d := h.hd
    have hn1 : 1 ≤ r.n := h.hn
    have h_pow_le {x : ℝ} (hx : 1 ≤ x) (k : ℕ) : 1 ≤ x ^ k := by
      induction' k with m ih
      · norm_num
      · rw [pow_succ]
        have hxpos : 0 ≤ x := by linarith
        have hpow_nonneg : 0 ≤ x ^ m := pow_nonneg hxpos m
        calc
          1 = 1 * 1 := by norm_num
          _ ≤ x ^ m * x := mul_le_mul ih hx (by norm_num) hpow_nonneg
    have hd3 : 1 ≤ r.d ^ 3 := h_pow_le hd1 3
    have hn4 : 1 ≤ r.n ^ 4 := h_pow_le hn1 4
    calc
      1 ≤ 15 * 2 ^ 17 * 1 * 1 := by norm_num
      _ ≤ 15 * 2 ^ 17 * r.d ^ 3 * r.n ^ 4 := by gcongr
  have h_sqrt_n_le_n : Real.sqrt r.n ≤ r.n := by
    have hn_ge_one : 1 ≤ r.n := h.hn
    calc
      Real.sqrt r.n ≤ Real.sqrt (r.n ^ 2) := Real.sqrt_le_sqrt (by
        calc
          r.n = r.n * 1 := by ring
          _ ≤ r.n * r.n := by gcongr
          _ = r.n ^ 2 := by ring)
      _ = r.n := Real.sqrt_sq (by linarith)
  have heps_ge_one_div_Ne : 1 / r.Ne ≤ r.eps := by
    dsimp [EncR.eps]
    have hnum_ge_one : 1 ≤ 14500 * r.d * Real.sqrt r.d * r.Le ^ 5 := by
      have h1 : (1 : ℝ) ≤ 14500 := by norm_num
      have h2 : 1 ≤ r.d := h.hd
      have h3 : 1 ≤ Real.sqrt r.d := hsqrt_d
      have h4 : 1 ≤ r.Le ^ 5 := by
        have hLe_ge_one : 1 ≤ r.Le := by linarith [h.hLe]
        have h_pow_le {x : ℝ} (hx : 1 ≤ x) (k : ℕ) : 1 ≤ x ^ k := by
          induction' k with m ih
          · norm_num
          · rw [pow_succ]
            have hxpos : 0 ≤ x := by linarith
            have hpow_nonneg : 0 ≤ x ^ m := pow_nonneg hxpos m
            calc
              1 = 1 * 1 := by norm_num
              _ ≤ x ^ m * x := mul_le_mul ih hx (by norm_num) hpow_nonneg
        exact h_pow_le hLe_ge_one 5
      calc
        1 = 1 * 1 * 1 * 1 := by norm_num
        _ ≤ 14500 * r.d * Real.sqrt r.d * r.Le ^ 5 := by
          have h := mul_le_mul (mul_le_mul (mul_le_mul h1 h2 (by norm_num) (by linarith))
            h3 (by positivity) (by linarith)) h4 (by positivity) (by positivity)
          simpa [mul_assoc] using h
    calc
      1 / r.Ne ≤ 1 / r.n := by
        refine (one_div_le_one_div hNe_pos hn_pos).mpr hn_le_Ne
      _ ≤ 1 / Real.sqrt r.n := by
        refine (one_div_le_one_div (by linarith) hsqrt_n_pos).mpr h_sqrt_n_le_n
      _ ≤ 14500 * r.d * Real.sqrt r.d * r.Le ^ 5 / Real.sqrt r.n :=
        div_le_div_of_nonneg_right hnum_ge_one (by positivity)
  have h_eps_mul_tp32 : r.eF ≤ r.eps * (r.tp / 32) := by
    calc
      r.eF ≤ r.tp / (2 ^ 40 * r.Ne ^ 2) := heF_bound
      _ = r.tp * (1 / (2 ^ 40 * r.Ne ^ 2)) := by ring
      _ ≤ r.tp * (r.eps / 32) := by
        have h_ineq : 1 / (2 ^ 40 * r.Ne ^ 2) ≤ r.eps / 32 := by
          calc
            1 / (2 ^ 40 * r.Ne ^ 2) = (1 / r.Ne) * (1 / (2 ^ 40 * r.Ne)) := by ring
            _ ≤ r.eps * (1 / (2 ^ 40 * r.Ne)) := by gcongr
            _ ≤ r.eps * (1 / 32) := by
              have hdiv : 1 / (2 ^ 40 * r.Ne) ≤ 1 / 32 := by
                refine (one_div_le_one_div ?_ ?_).mpr ?_
                · positivity
                · norm_num
                · have : (32 : ℝ) ≤ 2 ^ 40 * r.Ne := by
                    have h32le2pow40 : (32 : ℝ) ≤ (2 : ℝ) ^ 40 := by norm_num
                    calc
                      (32 : ℝ) ≤ (2 : ℝ) ^ 40 := h32le2pow40
                      _ = (2 : ℝ) ^ 40 * 1 := by ring
                      _ ≤ (2 : ℝ) ^ 40 * r.Ne := by gcongr
                  exact this
              gcongr
            _ = r.eps / 32 := by
              field_simp
        gcongr
      _ = r.eps * (r.tp / 32) := by ring
  -- Final combination
  calc
    r.ep ≤ X + r.eF := h_ep_le_X_plus_eF
    _ ≤ r.eps * (1 + r.tp / 32) + r.eF := by gcongr
    _ ≤ r.eps * (1 + r.tp / 32) + r.eps * (r.tp / 32) := by gcongr
    _ = r.eps * (1 + r.tp / 16) := by ring

theorem lam_rel (h : r.OK) : |r.lm / r.lam - 1| ≤ r.tp / 2 ^ 16 := by
  have hd_pos : 0 < r.d := by exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) h.hd
  have hn_pos : 0 < r.n := by exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) h.hn
  have hLe_pos : 0 < r.Le := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 17467) h.hLe
  have htp_pos : 0 < r.tp := h.htp0
  have heF_pos : 0 < r.eF := h.heF0
  have htp9_le_one : r.tp / 2 ^ 9 ≤ 1 := by
    have : r.tp ≤ 1 / 2 ^ 160 := h.htp1
    calc
      r.tp / 2 ^ 9 ≤ (1 / 2 ^ 160) / 2 ^ 9 := by gcongr
      _ = 1 / (2 ^ 160 * 2 ^ 9) := by ring
      _ ≤ 1 := (div_le_one (by positivity)).mpr (by norm_num)
  have hLp_pos : 0 < r.Lp := by
    have htemp : r.Le - r.tp / 2 ^ 9 ≥ 17466 :=
      calc
        r.Le - r.tp / 2 ^ 9 ≥ 17467 - r.tp / 2 ^ 9 := sub_le_sub_right h.hLe _
        _ ≥ 17467 - 1 := sub_le_sub_left htp9_le_one _
        _ = 17466 := by norm_num
    have : r.Lp ≥ r.Le - r.tp / 2 ^ 9 := h.hLp1
    linarith
  have hNe_pos : 0 < r.Ne := by
    have hpos : 0 < 15 * 2 ^ 17 * r.d ^ 3 * r.n ^ 4 := by positivity
    have : r.Ne = 15 * 2 ^ 17 * r.d ^ 3 * r.n ^ 4 := h.hNe
    linarith
  have hLp_ge_one : 1 ≤ r.Lp := by
    have htemp : r.Le - r.tp / 2 ^ 9 ≥ 17466 :=
      calc
        r.Le - r.tp / 2 ^ 9 ≥ 17467 - r.tp / 2 ^ 9 := sub_le_sub_right h.hLe _
        _ ≥ 17467 - 1 := sub_le_sub_left htp9_le_one _
        _ = 17466 := by norm_num
    have : r.Lp ≥ r.Le - r.tp / 2 ^ 9 := h.hLp1
    linarith
  have hLp_rat1 : 1 ≤ r.Le / r.Lp :=
    (one_le_div hLp_pos).mpr h.hLp2
  have hLp_rat2 : r.Le / r.Lp ≤ 1 + r.tp / 2 ^ 22 := by
    have hLp_ge_2pow13 : (2 : ℝ) ^ 13 ≤ r.Lp := by
      have h1 : (2 : ℝ) ^ 13 ≤ 17466 := by norm_num
      have h2 : 17466 ≤ r.Le - r.tp / 2 ^ 9 :=
        calc
          17466 = 17467 - 1 := by norm_num
          _ ≤ r.Le - r.tp / 2 ^ 9 := sub_le_sub h.hLe htp9_le_one
      have : r.Lp ≥ r.Le - r.tp / 2 ^ 9 := h.hLp1
      linarith
    have h_div_bound : (r.tp / 2 ^ 9) / r.Lp ≤ r.tp / 2 ^ 22 := by
      calc
        (r.tp / 2 ^ 9) / r.Lp = r.tp / (2 ^ 9 * r.Lp) := by ring
        _ ≤ r.tp / (2 ^ 9 * (2 : ℝ) ^ 13) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) (by nlinarith)
        _ = r.tp / 2 ^ 22 := by norm_num
    have h_le_minus_lp : r.Le - r.Lp ≤ r.tp / 2 ^ 9 := by
      have h := h.hLp1
      -- h: r.Le - r.tp / 2 ^ 9 ≤ r.Lp
      -- rearr: r.Le - r.Lp ≤ r.tp / 2 ^ 9
      linarith
    calc
      r.Le / r.Lp = (r.Lp + (r.Le - r.Lp)) / r.Lp := by ring
      _ = 1 + (r.Le - r.Lp) / r.Lp := by field_simp [hLp_pos.ne.symm]
      _ ≤ 1 + (r.tp / 2 ^ 9) / r.Lp := by
        have : (r.Le - r.Lp) / r.Lp ≤ (r.tp / 2 ^ 9) / r.Lp :=
          div_le_div_of_nonneg_right h_le_minus_lp (by positivity)
        linarith
      _ ≤ 1 + r.tp / 2 ^ 22 := by linarith
  have hlam_pos : 0 < r.lam := by
    unfold lam
    positivity
  set x := 1 / (725 * r.d * r.Lp ^ 2) with hx_def
  have hx_div_lam : x / r.lam = (r.Le / r.Lp) ^ 2 := by
    dsimp [x, lam]
    field_simp
  have hLe_ge_one : 1 ≤ r.Le := le_trans (by norm_num : (1 : ℝ) ≤ 17467) h.hLe
  have hLe_sq_ge_one : 1 ≤ r.Le ^ 2 := by nlinarith
  have h_d_Le2_le_Ne : r.d * r.Le ^ 2 ≤ r.Ne := by
    have htemp := h.hsm
    -- htemp: r.Le ^ 4 * r.d * r.n ≤ r.Ne
    have hLe4_ge_Le2 : r.Le ^ 2 ≤ r.Le ^ 4 := by
      calc
        r.Le ^ 2 = r.Le ^ 2 * 1 := by ring
        _ ≤ r.Le ^ 2 * r.Le ^ 2 := mul_le_mul_of_nonneg_left hLe_sq_ge_one (by positivity)
        _ = r.Le ^ 4 := by ring
    calc
      r.d * r.Le ^ 2 = r.Le ^ 2 * r.d := mul_comm _ _
      _ ≤ r.Le ^ 4 * r.d := mul_le_mul_of_nonneg_right hLe4_ge_Le2 (by positivity)
      _ = r.Le ^ 4 * r.d * 1 := by ring
      _ ≤ r.Le ^ 4 * r.d * r.n := mul_le_mul_of_nonneg_left h.hn (by positivity)
      _ ≤ r.Ne := htemp
  have hNe_ge_one : 1 ≤ r.Ne := by
    rw [h.hNe]
    have hd3 : 1 ≤ r.d ^ 3 := by
      have h1 : 1 ≤ r.d := h.hd
      calc
        1 = 1 ^ 3 := by norm_num
        _ ≤ r.d ^ 3 := by gcongr
    have hn4 : 1 ≤ r.n ^ 4 := by
      have h1 : 1 ≤ r.n := h.hn
      calc
        1 = 1 ^ 4 := by norm_num
        _ ≤ r.n ^ 4 := by gcongr
    have hbase : 1 ≤ 15 * 2 ^ 17 := by norm_num
    nlinarith
  have h_d_Le2_le_Ne2 : r.d * r.Le ^ 2 ≤ r.Ne ^ 2 := by
    have hNe_sq : r.Ne ≤ r.Ne ^ 2 := by
      nlinarith
    calc
      r.d * r.Le ^ 2 ≤ r.Ne := h_d_Le2_le_Ne
      _ ≤ r.Ne ^ 2 := hNe_sq
  have h_eF_Ne2_le : r.eF * r.Ne ^ 2 ≤ r.tp / 2 ^ 40 := by
    have htemp := h.heF1
    -- htemp: r.eF * (2 ^ 40 * r.Ne ^ 2 * r.d ^ 4) ≤ r.tp
    have hd4 : 1 ≤ r.d ^ 4 := by
      have h1 : 1 ≤ r.d := h.hd
      calc
        1 = 1 ^ 4 := by norm_num
        _ ≤ r.d ^ 4 := by gcongr
    have hineq : r.eF * r.Ne ^ 2 * 2 ^ 40 ≤ r.tp := by
      calc
        r.eF * r.Ne ^ 2 * 2 ^ 40 = r.eF * (2 ^ 40 * r.Ne ^ 2 * r.d ^ 4) * (r.d ^ 4)⁻¹ := by
          field_simp
        _ ≤ r.tp * (r.d ^ 4)⁻¹ := by
          have hpos_inv : 0 ≤ (r.d ^ 4)⁻¹ := by positivity
          nlinarith
        _ ≤ r.tp := by
          have h_inv_le_one : (r.d ^ 4)⁻¹ ≤ 1 := by
            calc
              (r.d ^ 4)⁻¹ = 1 / r.d ^ 4 := by ring
              _ ≤ 1 := (div_le_one (by positivity)).mpr hd4
          nlinarith
    rw [div_eq_mul_inv]
    calc
      r.eF * r.Ne ^ 2 = (r.eF * r.Ne ^ 2 * 2 ^ 40) * (2 ^ 40)⁻¹ := by field_simp
      _ ≤ r.tp * (2 ^ 40)⁻¹ := mul_le_mul_of_nonneg_right hineq (by positivity)
      _ = r.tp / 2 ^ 40 := by ring
  have h_diff_bound : |r.lm - x| / r.lam ≤ 725 * r.tp / 2 ^ 40 := by
    have h_lm_x : |r.lm - x| ≤ r.eF / 2 := h.hlm
    have h_one_div_lam : 1 / r.lam = 725 * r.d * r.Le ^ 2 := by
      dsimp [lam]
      field_simp
    have h_mid : |r.lm - x| * (725 * r.d * r.Le ^ 2) ≤ 725 * r.eF * r.Ne ^ 2 / 2 := by
      calc
        |r.lm - x| * (725 * r.d * r.Le ^ 2) ≤ (r.eF / 2) * (725 * r.d * r.Le ^ 2) :=
          mul_le_mul_of_nonneg_right h_lm_x (by positivity)
        _ = 725 * r.eF * (r.d * r.Le ^ 2) / 2 := by ring
        _ ≤ 725 * r.eF * r.Ne ^ 2 / 2 :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h_d_Le2_le_Ne2 (by positivity)) (by norm_num)
    calc
      |r.lm - x| / r.lam = |r.lm - x| * (1 / r.lam) := by ring
      _ = |r.lm - x| * (725 * r.d * r.Le ^ 2) := by rw [h_one_div_lam]
      _ ≤ 725 * r.eF * r.Ne ^ 2 / 2 := h_mid
      _ ≤ 725 * (r.tp / 2 ^ 40) / 2 := by
        have htemp : 725 * r.eF * r.Ne ^ 2 ≤ 725 * (r.tp / 2 ^ 40) := by nlinarith
        exact div_le_div_of_nonneg_right htemp (by norm_num)
      _ = 725 * r.tp / 2 ^ 41 := by ring
      _ ≤ 725 * r.tp / 2 ^ 40 :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) (by norm_num : (2 : ℝ) ^ 40 ≤ (2 : ℝ) ^ 41)
  have h_x_div_lam_bound : |x / r.lam - 1| ≤ 3 * r.tp / 2 ^ 22 := by
    have h_sq_diff : x / r.lam - 1 = (r.Le / r.Lp) ^ 2 - 1 := by rw [hx_div_lam]
    have h_sq_diff_nonneg : 0 ≤ (r.Le / r.Lp) ^ 2 - 1 := by
      have : 1 ≤ r.Le / r.Lp := hLp_rat1
      nlinarith
    have h_sq_diff_bound : (r.Le / r.Lp) ^ 2 - 1 ≤ 3 * r.tp / 2 ^ 22 := by
      have hratio_le : r.Le / r.Lp ≤ 1 + r.tp / 2 ^ 22 := hLp_rat2
      have hratio_ge_one : 1 ≤ r.Le / r.Lp := hLp_rat1
      have htp_small : r.tp / 2 ^ 22 ≤ 1 := by
        have : r.tp ≤ 1 / 2 ^ 160 := h.htp1
        calc
          r.tp / 2 ^ 22 ≤ (1 / 2 ^ 160) / 2 ^ 22 := by gcongr
          _ = 1 / (2 ^ 160 * 2 ^ 22) := by ring
          _ ≤ 1 := (div_le_one (by positivity)).mpr (by norm_num)
      have h_sq_bound : (r.Le / r.Lp) ^ 2 - 1 ≤ (1 + r.tp / 2 ^ 22) ^ 2 - 1 := by
        nlinarith
      calc
        (r.Le / r.Lp) ^ 2 - 1 ≤ (1 + r.tp / 2 ^ 22) ^ 2 - 1 := h_sq_bound
        _ = 2 * (r.tp / 2 ^ 22) + (r.tp / 2 ^ 22) ^ 2 := by ring
        _ ≤ 2 * (r.tp / 2 ^ 22) + (r.tp / 2 ^ 22) * 1 := by
          have : (r.tp / 2 ^ 22) ^ 2 ≤ (r.tp / 2 ^ 22) * 1 := by nlinarith
          nlinarith
        _ = 2 * (r.tp / 2 ^ 22) + r.tp / 2 ^ 22 := by ring
        _ = 3 * r.tp / 2 ^ 22 := by ring
    rw [h_sq_diff]
    rw [abs_of_nonneg h_sq_diff_nonneg]
    exact h_sq_diff_bound
  have h_main_decomp : |r.lm / r.lam - 1| ≤ |r.lm - x| / r.lam + |x / r.lam - 1| := by
    have h_eq : r.lm / r.lam - 1 = (r.lm - x) / r.lam + (x / r.lam - 1) := by
      field_simp [hlam_pos.ne.symm]
      ring
    calc
      |r.lm / r.lam - 1| = |(r.lm - x) / r.lam + (x / r.lam - 1)| := by rw [h_eq]
      _ ≤ |(r.lm - x) / r.lam| + |x / r.lam - 1| := abs_add_le _ _
      _ = |r.lm - x| / |r.lam| + |x / r.lam - 1| := by rw [abs_div]
      _ = |r.lm - x| / r.lam + |x / r.lam - 1| := by rw [abs_of_pos hlam_pos]
  have h_sum_bound : 725 * r.tp / 2 ^ 40 + 3 * r.tp / 2 ^ 22 ≤ r.tp / 2 ^ 16 := by
    have h_ineq : (725 : ℝ) / 2 ^ 40 + 3 / 2 ^ 22 ≤ (1 : ℝ) / 2 ^ 16 := by
      have hpos40 : 0 < (2 : ℝ) ^ 40 := by norm_num
      have hpos22 : 0 < (2 : ℝ) ^ 22 := by norm_num
      have hpos16 : 0 < (2 : ℝ) ^ 16 := by norm_num
      have hcalc : (725 : ℝ) + 3 * 2 ^ 18 ≤ (2 : ℝ) ^ 24 := by norm_num
      field_simp [hpos40.ne.symm, hpos22.ne.symm, hpos16.ne.symm]
      -- goal after field_simp: 725 + 2^18 * 3 ≤ 2^24
      -- which is exactly hcalc (modulo commutativity)
      simpa [mul_comm, add_comm] using hcalc
    calc
      725 * r.tp / 2 ^ 40 + 3 * r.tp / 2 ^ 22 = r.tp * ((725 : ℝ) / 2 ^ 40 + 3 / 2 ^ 22) := by ring
      _ ≤ r.tp * ((1 : ℝ) / 2 ^ 16) := mul_le_mul_of_nonneg_left h_ineq (by positivity)
      _ = r.tp / 2 ^ 16 := by ring
  calc
    |r.lm / r.lam - 1| ≤ |r.lm - x| / r.lam + |x / r.lam - 1| := h_main_decomp
    _ ≤ 725 * r.tp / 2 ^ 40 + 3 * r.tp / 2 ^ 22 := by
      exact add_le_add h_diff_bound h_x_div_lam_bound
    _ ≤ r.tp / 2 ^ 16 := h_sum_bound

theorem Ne_one (h : r.OK) : (1 : ℝ) ≤ r.Ne := by
  have hL1 : (1 : ℝ) ≤ r.Le := le_trans (by norm_num) h.hLe
  have : (1 : ℝ) ≤ r.Le ^ 4 * r.d * r.n :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hL1) h.hd) h.hn
  linarith [h.hsm]

theorem eta_rel (h : r.OK) : |r.et / r.eta - 1| ≤ r.tp / 2 ^ 16 := by
  obtain ⟨hd0, hn0, hNe0, hLe0, hLp0, -, -, -, hsd1, hsn1, heqb, heFb⟩ := h.base
  obtain ⟨hrd1, hrd2, -, hrn1, hrn2⟩ := h.root_rat
  obtain ⟨hl1, hl2, -⟩ := h.Lp_rat
  have het := h.het
  have htp := h.htp0
  have htp1 := h.htp1
  have heq0 := h.heq0
  have heF0 := h.heF0
  have hrd0 : 1 ≤ r.rd := h.hrd0
  have hrn0 : 1 ≤ r.rn := h.hrn0
  have hNe1 : (1 : ℝ) ≤ r.Ne := Ne_one h
  have heta0 : 0 < r.eta := by unfold EncR.eta; positivity
  set x := r.rd / Real.sqrt r.d
  set y := Real.sqrt r.n / r.rn
  set z := r.Le / r.Lp
  -- the exact quotient
  have hq : r.rd / (r.Lp * r.rn) / r.eta = x * y * z := by
    unfold EncR.eta
    simp only [x, y, z]
    field_simp
  have heps : r.eq ≤ r.tp / 2 ^ 18 := heqb
  have hx0 : 0 ≤ x := by positivity
  have hy1 : 1 ≤ y := hrn1
  have hz1 : 1 ≤ z := hl1
  -- upper: `x y z ≤ (1 + eq)(1 + tp/2^22)`, lower: `x y z ≥ 1 - eq`
  have hup : x * y * z - 1 ≤ 3 * (r.tp / 2 ^ 18) := by
    have a : x * y ≤ 1 * (1 + r.eq) := mul_le_mul hrd2 hrn2 (by linarith) (by norm_num)
    have b : x * y * z ≤ (1 + r.eq) * (1 + r.tp / 2 ^ 22) :=
      mul_le_mul (by linarith) hl2 (by linarith) (by positivity)
    have c : (1 + r.eq) * (1 + r.tp / 2 ^ 22) ≤ 1 + 3 * (r.tp / 2 ^ 18) := by
      have t1 : r.tp ≤ 1 := le_trans htp1 (by norm_num)
      have : r.eq * (r.tp / 2 ^ 22) ≤ r.tp / 2 ^ 18 := by
        have : r.eq ≤ 1 := by linarith [show r.tp / 2 ^ 18 ≤ 1 by linarith]
        calc r.eq * (r.tp / 2 ^ 22) ≤ 1 * (r.tp / 2 ^ 22) := by gcongr
          _ ≤ r.tp / 2 ^ 18 := by linarith
      nlinarith
    linarith
  have hlo : 1 - x * y * z ≤ r.tp / 2 ^ 18 := by
    have a : x * 1 ≤ x * y := mul_le_mul_of_nonneg_left hy1 hx0
    have b : x * y * 1 ≤ x * y * z := mul_le_mul_of_nonneg_left hz1 (by positivity)
    linarith
  -- the rounding
  have hR : |r.et - r.rd / (r.Lp * r.rn)| / r.eta ≤ r.tp / 2 ^ 40 := by
    rw [div_le_iff₀ heta0]
    have hinv : 1 / r.eta ≤ r.Ne := by
      unfold EncR.eta
      rw [one_div_div, div_le_iff₀ (by linarith)]
      have hsnn : Real.sqrt r.n ≤ r.n := by
        rw [Real.sqrt_le_left (by linarith)]; exact le_self_pow₀ h.hn (by norm_num)
      have hL1 : (1 : ℝ) ≤ r.Le := le_trans (by norm_num) h.hLe
      have a1 : r.Le * Real.sqrt r.n ≤ r.Le * r.n := by gcongr
      have a2 : r.Le * r.n ≤ r.Le ^ 4 * r.d * r.n := by
        have : r.Le ≤ r.Le ^ 4 * r.d := by
          calc r.Le ≤ r.Le ^ 4 := le_self_pow₀ hL1 (by norm_num)
            _ ≤ r.Le ^ 4 * r.d := le_mul_of_one_le_right (by positivity) h.hd
        exact mul_le_mul_of_nonneg_right this hn0.le
      have a3 : r.Le ^ 4 * r.d * r.n ≤ r.Ne * Real.sqrt r.d := by
        have := mul_le_mul h.hsm hsd1 (by norm_num) hNe0.le
        linarith
      linarith
    have heFN : r.eF * r.Ne ≤ r.tp / 2 ^ 40 := by
      have : r.eF * r.Ne ≤ r.eF * r.Ne ^ 2 :=
        mul_le_mul_of_nonneg_left (le_self_pow₀ hNe1 (by norm_num)) heF0.le
      linarith
    have : r.eF / 2 ≤ r.tp / 2 ^ 40 * r.eta := by
      have h1 : r.eF ≤ r.eF * (r.Ne * r.eta) := by
        have : 1 ≤ r.Ne * r.eta := by
          have := hinv
          rw [div_le_iff₀ heta0] at this; linarith
        exact le_mul_of_one_le_right heF0.le this
      have h2 : r.eF * (r.Ne * r.eta) = r.eF * r.Ne * r.eta := by ring
      have h3 : r.eF * r.Ne * r.eta ≤ r.tp / 2 ^ 40 * r.eta := mul_le_mul_of_nonneg_right heFN heta0.le
      linarith
    linarith
  have hdec : r.et / r.eta - 1 = (r.et - r.rd / (r.Lp * r.rn)) / r.eta + (x * y * z - 1) := by
    rw [← hq]; field_simp; ring
  rw [hdec]
  have h2 : |x * y * z - 1| ≤ 3 * (r.tp / 2 ^ 18) := by
    rw [abs_le]; constructor <;> linarith
  calc _ ≤ |(r.et - r.rd / (r.Lp * r.rn)) / r.eta| + |x * y * z - 1| := abs_add_le _ _
    _ ≤ r.tp / 2 ^ 40 + 3 * (r.tp / 2 ^ 18) := by
        rw [abs_div, abs_of_pos heta0]; linarith
    _ ≤ r.tp / 2 ^ 16 := by
        have : r.tp / 2 ^ 40 ≤ r.tp / 2 ^ 18 := by gcongr <;> norm_num
        linarith

theorem sig2_rel (h : r.OK) : |r.sg / r.sig2 - 1| ≤ r.tp / 2 ^ 16 := by
  rcases base h with ⟨hd_pos, hn_pos, hNe_pos, hLe_pos, hLp_pos, hLp_le_hLh, hn_le_Ne, hd_le_Ne, hsqrt_d_ge_one, hsqrt_n_ge_one, heq_bound, heF_Ne_bound⟩
  rcases Lp_rat h with ⟨hLe_div_Lp_ge_one, hLe_div_Lp_le_one_plus, hLp_div_Le_ge_one_minus, hLp_div_Le_le_one, hLh_div_Le_ge_one, hLh_div_Le_le_one_plus⟩
  have heF_nonneg : 0 ≤ r.eF := le_of_lt h.heF0
  have hNe_ge_one : 1 ≤ r.Ne := by
    rw [h.hNe]
    have hd3 : (1 : ℝ) ≤ r.d ^ 3 := by
      calc
        (1 : ℝ) = (1 : ℝ) * (1 : ℝ) * (1 : ℝ) := by norm_num
        _ ≤ r.d * r.d * r.d := by
          have h1 : (1 : ℝ) * (1 : ℝ) ≤ r.d * r.d := mul_le_mul h.hd h.hd (by linarith) (by linarith)
          have h2 : (1 : ℝ) * (1 : ℝ) * (1 : ℝ) ≤ r.d * r.d * r.d :=
            mul_le_mul h1 h.hd (by positivity) (by linarith)
          exact h2
        _ = r.d ^ 3 := by ring
    have hn4 : (1 : ℝ) ≤ r.n ^ 4 := by
      calc
        (1 : ℝ) = (1 : ℝ) * (1 : ℝ) * (1 : ℝ) * (1 : ℝ) := by norm_num
        _ ≤ r.n * r.n * r.n * r.n := by
          have h1 : (1 : ℝ) * (1 : ℝ) ≤ r.n * r.n := mul_le_mul h.hn h.hn (by linarith) (by linarith)
          have h2 : (1 : ℝ) * (1 : ℝ) * (1 : ℝ) ≤ r.n * r.n * r.n :=
            mul_le_mul h1 h.hn (by positivity) (by linarith)
          have h3 : (1 : ℝ) * (1 : ℝ) * (1 : ℝ) * (1 : ℝ) ≤ r.n * r.n * r.n * r.n :=
            mul_le_mul h2 h.hn (by positivity) (by linarith)
          exact h3
        _ = r.n ^ 4 := by ring
    have h_factor : (1 : ℝ) ≤ 15 * 2 ^ 17 := by norm_num
    nlinarith
  have hLe_le_Ne : r.Le ≤ r.Ne := by
    have hLe4_le_Ne : r.Le ^ 4 ≤ r.Ne := by
      have hprod : r.Le ^ 4 * r.d * r.n ≤ r.Ne := h.hsm
      have hpos : 0 ≤ r.Le ^ 4 := pow_nonneg (by linarith) 4
      have h_mul : r.Le ^ 4 ≤ r.Le ^ 4 * r.d * r.n := by
        calc
          r.Le ^ 4 = r.Le ^ 4 * 1 := by ring
          _ ≤ r.Le ^ 4 * r.d := mul_le_mul_of_nonneg_left h.hd hpos
          _ = r.Le ^ 4 * r.d * 1 := by ring
          _ ≤ r.Le ^ 4 * r.d * r.n := mul_le_mul_of_nonneg_left h.hn (by nlinarith)
      nlinarith
    by_contra! hgt
    have hLe4_gt_Ne : r.Ne < r.Le ^ 4 := by
      have h_pow : r.Ne ^ 4 < r.Le ^ 4 := by
        have h_sq : r.Ne ^ 2 < r.Le ^ 2 := by
          simpa [sq] using mul_self_lt_mul_self (by linarith) hgt
        have h_cube : r.Ne ^ 3 < r.Le ^ 3 := by
          calc
            r.Ne ^ 3 = r.Ne * r.Ne ^ 2 := by ring
            _ < r.Le * r.Ne ^ 2 := mul_lt_mul_of_pos_right hgt (pow_pos hNe_pos 2)
            _ < r.Le * r.Le ^ 2 := mul_lt_mul_of_pos_left h_sq hLe_pos
            _ = r.Le ^ 3 := by ring
        calc
          r.Ne ^ 4 = r.Ne * r.Ne ^ 3 := by ring
          _ < r.Le * r.Ne ^ 3 := mul_lt_mul_of_pos_right hgt (pow_pos hNe_pos 3)
          _ < r.Le * r.Le ^ 3 := mul_lt_mul_of_pos_left h_cube hLe_pos
          _ = r.Le ^ 4 := by ring
      have h_Ne4_ge_Ne : r.Ne ≤ r.Ne ^ 4 := by
        calc
          r.Ne = r.Ne * 1 := by ring
          _ ≤ r.Ne * r.Ne := mul_le_mul_of_nonneg_left hNe_ge_one (by linarith)
          _ = r.Ne ^ 2 := by ring
          _ = r.Ne ^ 2 * 1 := by ring
          _ ≤ r.Ne ^ 2 * r.Ne ^ 2 := mul_le_mul_of_nonneg_left (by
            calc
              1 = 1 * 1 := by norm_num
              _ ≤ r.Ne * r.Ne := mul_le_mul hNe_ge_one hNe_ge_one (by linarith) (by linarith)
              _ = r.Ne ^ 2 := by ring
            ) (sq_nonneg r.Ne)
          _ = r.Ne ^ 4 := by ring
      nlinarith
    nlinarith
  set x := 1 / (8 * r.Lp) with hx_def
  have h_sg_bound : |r.sg - x| ≤ r.eF / 2 := h.hsg
  have h_eq : r.sg / r.sig2 - 1 = (r.sg - x) * (8 * r.Le) + (r.Le / r.Lp - 1) := by
    dsimp [EncR.sig2, x]
    field_simp [show r.Lp ≠ 0 from by linarith, show r.Le ≠ 0 from by linarith]
    ring
  rw [h_eq]
  have h_triangle : |(r.sg - x) * (8 * r.Le) + (r.Le / r.Lp - 1)| ≤ |(r.sg - x) * (8 * r.Le)| + |r.Le / r.Lp - 1| :=
    abs_add_le _ _
  have h_first_term : |(r.sg - x) * (8 * r.Le)| ≤ r.tp / 2 ^ 38 := by
    calc
      |(r.sg - x) * (8 * r.Le)| = |r.sg - x| * |8 * r.Le| := abs_mul _ _
      _ = |r.sg - x| * (8 * r.Le) := by
        rw [abs_of_pos (by positivity : 0 < 8 * r.Le)]
      _ ≤ (r.eF / 2) * (8 * r.Le) := by
        gcongr
      _ = 4 * r.eF * r.Le := by ring
      _ ≤ 4 * r.eF * r.Ne := by
        gcongr
      _ ≤ 4 * r.eF * (r.Ne ^ 2) := by
        have h_Ne_le_Ne_sq : r.Ne ≤ r.Ne ^ 2 := by
          calc
            r.Ne = r.Ne * 1 := by ring
            _ ≤ r.Ne * r.Ne := mul_le_mul_of_nonneg_left hNe_ge_one (by linarith)
            _ = r.Ne ^ 2 := by ring
        gcongr
      _ = 4 * (r.eF * r.Ne ^ 2) := by ring
      _ ≤ 4 * (r.tp / 2 ^ 40) := by
        gcongr
      _ = r.tp / 2 ^ 38 := by ring
  have h_second_term : |r.Le / r.Lp - 1| ≤ r.tp / 2 ^ 22 := by
    have h_nonneg : 0 ≤ r.Le / r.Lp - 1 := by linarith
    rw [abs_of_nonneg h_nonneg]
    linarith
  have h_ineq : r.tp / 2 ^ 38 + r.tp / 2 ^ 22 ≤ r.tp / 2 ^ 16 := by
    have htp_pos : 0 < r.tp := h.htp0
    have htp_nonneg : 0 ≤ r.tp := by linarith
    have h_num : (1 : ℝ) + (2 : ℝ) ^ 16 ≤ (2 : ℝ) ^ 22 := by norm_num
    have hpos_denom : 0 < (2 : ℝ) ^ 38 := by norm_num
    have h_main : (1 : ℝ) / (2 : ℝ) ^ 38 + (1 : ℝ) / (2 : ℝ) ^ 22 ≤ (1 : ℝ) / (2 : ℝ) ^ 16 := by
      calc
        (1 : ℝ) / (2 : ℝ) ^ 38 + (1 : ℝ) / (2 : ℝ) ^ 22 = ((1 : ℝ) + (2 : ℝ) ^ 16) / (2 : ℝ) ^ 38 := by
          field_simp [show (2 : ℝ) ^ 22 ≠ 0 from by norm_num, show (2 : ℝ) ^ 38 ≠ 0 from by norm_num]
        _ ≤ (2 : ℝ) ^ 22 / (2 : ℝ) ^ 38 := by
          rw [div_le_div_iff_of_pos_right hpos_denom]
          exact h_num
        _ = (1 : ℝ) / (2 : ℝ) ^ 16 := by ring
    have h := mul_le_mul_of_nonneg_left h_main htp_nonneg
    simpa [div_eq_mul_inv, mul_add] using h
  nlinarith

theorem rho_le (h : r.OK) : r.ro ≤ r.rho := by
  unfold rho
  have hd_nonneg : 0 ≤ r.d := by
    have h1 : 1 ≤ r.d := h.hd
    linarith
  have htp_bound : r.tp ≤ 1 / 2 ^ 160 := h.htp1
  have hLe_nonneg : 0 ≤ r.Le := by
    have h1 : 17467 ≤ r.Le := h.hLe
    linarith
  have hLp_nonneg : 0 ≤ r.Lp := by
    have : r.tp / 2 ^ 9 ≤ r.Le := by
      have hLe : 17467 ≤ r.Le := h.hLe
      have htp_bound : r.tp ≤ 1 / 2 ^ 160 := h.htp1
      have h : (1 : ℝ) / 2 ^ 160 / 2 ^ 9 ≤ 17467 := by norm_num
      linarith
    linarith [h.hLp1, this]
  have h_pow : r.Lp ^ 3 ≤ r.Le ^ 3 := by
    gcongr
    exact h.hLp2
  have h_mul : 1450 * r.d ^ 2 * r.Lp ^ 3 ≤ 1450 * r.d ^ 2 * r.Le ^ 3 := by
    nlinarith
  exact le_trans h.hro2 h_mul

theorem rho_rel (h : r.OK) : |r.ro / r.rho - 1| ≤ r.tp / 16 := by
  rcases h.base with ⟨hdpos, hnpos, hNe, hLe, hLp, hLpLe, hnNe, hdNe, hsqrd1, hsqrn1, heq_le, heF_le⟩
  rcases h.Lp_rat with ⟨hLeLp, hLpLe_bound, hLpLe_low, hLpLe_up, hLeLh, hLhLe⟩
  have hd1 : 1 ≤ r.d := h.hd
  have hn1 : 1 ≤ r.n := h.hn
  have hLe1 : 1 ≤ r.Le := le_trans (by norm_num : (1 : ℝ) ≤ 17467) h.hLe
  have hLp_nonneg : 0 ≤ r.Lp := by linarith
  have hLe_nonneg : 0 ≤ r.Le := by linarith
  have hrho_pos : 0 < r.rho := by
    dsimp [EncR.rho]
    positivity
  have hrho_ge_one : 1 ≤ r.rho := by
    dsimp [EncR.rho]
    have hd_sq : 1 ≤ r.d ^ 2 := by
      calc
        1 = (1 : ℝ) ^ 2 := by norm_num
        _ ≤ r.d ^ 2 := by gcongr
    have hLe_cu : 1 ≤ r.Le ^ 3 := by
      calc
        1 = (1 : ℝ) ^ 3 := by norm_num
        _ ≤ r.Le ^ 3 := by gcongr
    nlinarith
  have heF_le_tp : r.eF ≤ r.tp / 2 ^ 40 := by
    have hNe_ge_one : 1 ≤ r.Ne := by
      rw [h.hNe]
      have hd3 : 1 ≤ r.d ^ 3 := by
        calc
          1 = (1 : ℝ) ^ 3 := by norm_num
          _ ≤ r.d ^ 3 := by gcongr
      have hn4 : 1 ≤ r.n ^ 4 := by
        calc
          1 = (1 : ℝ) ^ 4 := by norm_num
          _ ≤ r.n ^ 4 := by gcongr
      nlinarith
    have hNe_sq_ge_one : 1 ≤ r.Ne ^ 2 := by
      calc
        1 = (1 : ℝ) ^ 2 := by norm_num
        _ ≤ r.Ne ^ 2 := by gcongr
    calc
      r.eF = r.eF * 1 := by ring
      _ ≤ r.eF * r.Ne ^ 2 := mul_le_mul_of_nonneg_left hNe_sq_ge_one h.heF0.le
      _ ≤ r.tp / 2 ^ 40 := heF_le
  have h_tp_div_pos : 0 ≤ r.tp / 2 ^ 22 := div_nonneg (by linarith) (by norm_num)
  set x := r.Lp / r.Le with hx_def
  have hx_up : x ≤ 1 := hLpLe_up
  have hx_low : 1 - r.tp / 2 ^ 22 ≤ x := hLpLe_low
  have hx_nonneg : 0 ≤ x := div_nonneg hLp_nonneg hLe_nonneg
  have h_tp_div_le_two : r.tp / 2 ^ 22 ≤ 2 := by
    have h_one_div : (1 : ℝ) / 2 ^ 160 ≤ 1 := by
      exact (div_le_one (by norm_num : 0 < (2 : ℝ) ^ 160)).mpr (by norm_num)
    have htp_le_one : r.tp ≤ 1 := le_trans h.htp1 h_one_div
    nlinarith
  have h_cube_ineq (a : ℝ) (ha : a ≤ 2) : 1 - 3 * a ≤ (1 - a) ^ 3 := by
    have h_nonneg : 0 ≤ 2 + (-a) := by linarith
    have h_ineq := one_add_le_pow_of_two_add_nonneg h_nonneg 3
    simpa [sub_eq_add_neg] using h_ineq
  have h_upper : r.ro / r.rho - 1 ≤ r.tp / 16 := by
    have h_ro_div_rho_le_one : r.ro / r.rho ≤ 1 := by
      calc
        r.ro / r.rho ≤ (1450 * r.d ^ 2 * r.Lp ^ 3) / r.rho := by
          gcongr
          exact h.hro2
        _ = (1450 * r.d ^ 2 * r.Lp ^ 3) / (1450 * r.d ^ 2 * r.Le ^ 3) := rfl
        _ = (r.Lp / r.Le) ^ 3 := by
          field_simp [ne_of_gt hdpos, ne_of_gt hLe]
        _ = x ^ 3 := rfl
        _ ≤ 1 ^ 3 := by gcongr
        _ = 1 := by norm_num
    linarith
  have h_lower : -(r.ro / r.rho - 1) ≤ r.tp / 16 := by
    have h_ro_div_rho_ge : x ^ 3 - r.eF / r.rho ≤ r.ro / r.rho := by
      have hx_cube_eq : x ^ 3 = (1450 * r.d ^ 2 * r.Lp ^ 3) / r.rho := by
        dsimp [x, EncR.rho]
        field_simp [ne_of_gt hdpos, ne_of_gt hLe]
      rw [hx_cube_eq]
      calc
        (1450 * r.d ^ 2 * r.Lp ^ 3) / r.rho - r.eF / r.rho =
            (1450 * r.d ^ 2 * r.Lp ^ 3 - r.eF) / r.rho := by ring
        _ ≤ r.ro / r.rho := by
          gcongr
          exact h.hro1
    have h_one_minus_x_cube_le : 1 - x ^ 3 ≤ 3 * (1 - x) := by
      have h_factor : 1 - x ^ 3 = (1 - x) * (1 + x + x ^ 2) := by ring
      rw [h_factor]
      have h_sum : 1 + x + x ^ 2 ≤ 3 := by
        have hx_sq_le_x : x ^ 2 ≤ x := by
          calc
            x ^ 2 = x * x := by ring
            _ ≤ x * 1 := mul_le_mul_of_nonneg_left hx_up hx_nonneg
            _ = x := by ring
        linarith
      have h_nonneg : 0 ≤ 1 - x := by linarith
      calc
        (1 - x) * (1 + x + x ^ 2) ≤ (1 - x) * 3 := mul_le_mul_of_nonneg_left h_sum h_nonneg
        _ = 3 * (1 - x) := by ring
    have h_cube_lower : 1 - 3 * (r.tp / 2 ^ 22) ≤ (1 - r.tp / 2 ^ 22) ^ 3 :=
      h_cube_ineq (r.tp / 2 ^ 22) h_tp_div_le_two
    have h_chain : 1 - r.ro / r.rho ≤ r.tp / 16 := by
      have h1 : 1 - r.ro / r.rho ≤ 1 - (x ^ 3 - r.eF / r.rho) := by linarith
      have h2 : 1 - (x ^ 3 - r.eF / r.rho) = (1 - x ^ 3) + r.eF / r.rho := by ring
      have h3 : (1 - x ^ 3) + r.eF / r.rho ≤ 3 * (1 - x) + r.eF / r.rho := by linarith
      have h4 : 3 * (1 - x) + r.eF / r.rho ≤ 3 * (r.tp / 2 ^ 22) + r.eF / r.rho := by
        have hx_sub : 1 - x ≤ r.tp / 2 ^ 22 := by linarith
        gcongr
      have h5 : 3 * (r.tp / 2 ^ 22) + r.eF / r.rho ≤ 3 * (r.tp / 2 ^ 22) + r.eF := by
        have hdiv : r.eF / r.rho ≤ r.eF := div_le_self h.heF0.le hrho_ge_one
        linarith
      have h6 : 3 * (r.tp / 2 ^ 22) + r.eF ≤ 3 * (r.tp / 2 ^ 22) + r.tp / 2 ^ 40 := by
        gcongr
      have h7 : 3 * (r.tp / 2 ^ 22) + r.tp / 2 ^ 40 ≤ r.tp / 16 := by
        have hpos : 0 ≤ r.tp := by linarith
        have h : (3 : ℝ) / 2 ^ 22 + (1 : ℝ) / 2 ^ 40 ≤ (1 : ℝ) / 16 := by norm_num
        calc
          3 * (r.tp / 2 ^ 22) + r.tp / 2 ^ 40 = r.tp * ((3 : ℝ) / 2 ^ 22 + (1 : ℝ) / 2 ^ 40) := by ring
          _ ≤ r.tp * ((1 : ℝ) / 16) := by gcongr
          _ = r.tp / 16 := by ring
      linarith
    linarith
  rw [abs_le]
  constructor
  · linarith
  · linarith

theorem mul_rel (x y δ1 δ2 : ℝ) (hx : |x - 1| ≤ δ1) (hy : |y - 1| ≤ δ2) (h2 : 0 ≤ δ2) :
    |x * y - 1| ≤ δ1 * (1 + δ2) + δ2 := by
  have hy' : |y| ≤ 1 + δ2 := by
    have := abs_sub_abs_le_abs_sub y 1
    simp only [abs_one] at this
    linarith
  have hδ1 : 0 ≤ δ1 := le_trans (abs_nonneg _) hx
  calc |x * y - 1| = |(x - 1) * y + (y - 1)| := by ring_nf
    _ ≤ |(x - 1) * y| + |y - 1| := abs_add_le _ _
    _ = |x - 1| * |y| + |y - 1| := by rw [abs_mul]
    _ ≤ δ1 * (1 + δ2) + δ2 := by gcongr

theorem eta_lam_inv (h : r.OK) : 1 / (r.eta * r.lam) ≤ 725 * r.Ne := by
  obtain ⟨hd0, hn0, hNe0, hLe0, -, -, -, -, hsd1, hsn1, -, -⟩ := h.base
  have hd := h.hd
  have hn := h.hn
  have hsm := h.hsm
  have hL1 : (1 : ℝ) ≤ r.Le := le_trans (by norm_num) h.hLe
  unfold EncR.eta EncR.lam
  have hsn0 : 0 < Real.sqrt r.n := by positivity
  have e : 1 / (Real.sqrt r.d / (r.Le * Real.sqrt r.n) * (1 / (725 * r.d * r.Le ^ 2))) =
      725 * r.d * r.Le ^ 3 * Real.sqrt r.n / Real.sqrt r.d := by
    field_simp
  rw [e, div_le_iff₀ (by linarith)]
  have hsnn : Real.sqrt r.n ≤ r.n := by
    rw [Real.sqrt_le_left (by linarith)]; exact le_self_pow₀ hn (by norm_num)
  have a1 : r.d * r.Le ^ 3 * Real.sqrt r.n ≤ r.d * r.Le ^ 3 * r.n := by gcongr
  have a2 : r.d * r.Le ^ 3 * r.n ≤ r.Le ^ 4 * r.d * r.n := by
    have h4 : r.Le ^ 3 ≤ r.Le ^ 4 := pow_le_pow_right₀ hL1 (by norm_num)
    have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h4 hd0.le) hn0.le
    linarith
  have a3 : r.Le ^ 4 * r.d * r.n ≤ r.Ne * Real.sqrt r.d := by
    have := mul_le_mul hsm hsd1 (by norm_num) hNe0.le
    linarith
  linarith

theorem kapc_rel (h : r.OK) : |r.kp / r.kc - 1| ≤ r.tp / 16 := by
  obtain ⟨hd0, hn0, hNe0, hLe0, hLp0, -, -, -, hsd1, hsn1, -, heFb⟩ := h.base
  have hlr := h.lam_rel
  have her := h.eta_rel
  have hkp := h.hkp
  have htp := h.htp0
  have htp1 := h.htp1
  have heF0 := h.heF0
  have hd := h.hd
  have hn := h.hn
  have hLe := h.hLe
  have hsm := h.hsm
  set δ : ℝ := r.tp / 2 ^ 16 with hδ
  have hδ0 : 0 ≤ δ := by positivity
  have hδs : δ ≤ 1 / 2 ^ 170 := by
    rw [hδ]; calc r.tp / 2 ^ 16 ≤ 1 / 2 ^ 160 / 2 ^ 16 := by gcongr
      _ = 1 / 2 ^ 176 := by norm_num
      _ ≤ 1 / 2 ^ 170 := by norm_num
  -- `lam` is tiny
  have hlam0 : 0 < r.lam := by unfold EncR.lam; positivity
  have hlam1 : r.lam ≤ 1 / 4 := by
    unfold EncR.lam
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : (1 : ℝ) ≤ r.d * r.Le ^ 2 := one_le_mul_of_one_le_of_one_le hd (by nlinarith)
    nlinarith
  -- `lm` near `lam`
  have hlm : |r.lm - r.lam| ≤ r.lam * δ := by
    have e : r.lm - r.lam = r.lam * (r.lm / r.lam - 1) := by field_simp
    rw [e, abs_mul, abs_of_pos hlam0]
    exact mul_le_mul_of_nonneg_left hlr hlam0.le
  have hlmd : r.lam * δ ≤ 1 / 16 := by
    have : r.lam * δ ≤ 1 / 4 * (1 / 2 ^ 170) := mul_le_mul hlam1 hδs hδ0 (by norm_num)
    linarith [show (1 : ℝ) / 4 * (1 / 2 ^ 170) ≤ 1 / 16 by norm_num]
  have hlm1 : 1 / 2 ≤ 1 - r.lm := by
    have := (abs_le.mp hlm).2; linarith
  have hlam2 : 1 / 2 ≤ 1 - r.lam := by linarith
  -- the factor `(1 - lam)/(1 - lm)`
  have hC : |(1 - r.lam) / (1 - r.lm) - 1| ≤ δ := by
    have e : (1 - r.lam) / (1 - r.lm) - 1 = (r.lm - r.lam) / (1 - r.lm) := by
      field_simp; ring
    rw [e, abs_div, abs_of_pos (by linarith : (0 : ℝ) < 1 - r.lm), div_le_iff₀ (by linarith)]
    have : r.lam * δ ≤ δ * (1 - r.lm) := by nlinarith
    linarith
  have hC2 : |((1 - r.lam) / (1 - r.lm)) * ((1 - r.lam) / (1 - r.lm)) - 1| ≤ δ * (1 + δ) + δ :=
    mul_rel _ _ δ δ hC hC hδ0
  have hAB : |(r.et / r.eta) * (r.lm / r.lam) - 1| ≤ δ * (1 + δ) + δ := mul_rel _ _ δ δ her hlr hδ0
  have hδ2 : δ * (1 + δ) + δ ≤ 3 * δ := by nlinarith
  have hP : |((r.et / r.eta) * (r.lm / r.lam)) * (((1 - r.lam) / (1 - r.lm)) * ((1 - r.lam) / (1 - r.lm))) - 1| ≤
      3 * δ * (1 + 3 * δ) + 3 * δ :=
    mul_rel _ _ (3 * δ) (3 * δ) (le_trans hAB hδ2) (le_trans hC2 hδ2) (by positivity)
  -- `y/kc` is that product
  have heta0 : 0 < r.eta := by unfold EncR.eta; positivity
  have hkc0 : 0 < r.kc := by unfold EncR.kc; positivity
  have hy : r.et * r.lm / (4 * (1 - r.lm) ^ 2) / r.kc =
      ((r.et / r.eta) * (r.lm / r.lam)) * (((1 - r.lam) / (1 - r.lm)) * ((1 - r.lam) / (1 - r.lm))) := by
    unfold EncR.kc
    have : (1 - r.lm) ≠ 0 := by linarith
    have : (1 - r.lam) ≠ 0 := by linarith
    field_simp
  -- the rounding: `1/kc ≤ 4 · 725 Ne`
  have hinv : 1 / r.kc ≤ 2900 * r.Ne := by
    unfold EncR.kc
    rw [one_div_div]
    have h1 : 4 * (1 - r.lam) ^ 2 ≤ 4 := by nlinarith
    have h2 : 1 / (r.eta * r.lam) ≤ 725 * r.Ne := eta_lam_inv h
    have : 4 * (1 - r.lam) ^ 2 / (r.eta * r.lam) = 4 * (1 - r.lam) ^ 2 * (1 / (r.eta * r.lam)) := by ring
    rw [this]
    calc 4 * (1 - r.lam) ^ 2 * (1 / (r.eta * r.lam)) ≤ 4 * (725 * r.Ne) :=
          mul_le_mul h1 h2 (by positivity) (by norm_num)
      _ = 2900 * r.Ne := by ring
  have hR : |(r.kp - r.et * r.lm / (4 * (1 - r.lm) ^ 2)) / r.kc| ≤ 1450 * (r.tp / 2 ^ 40) := by
    rw [abs_div, abs_of_pos hkc0, div_eq_mul_one_div]
    have hNe1 : (1 : ℝ) ≤ r.Ne := Ne_one h
    have heFN : r.eF * r.Ne ≤ r.tp / 2 ^ 40 := by
      have : r.eF * r.Ne ≤ r.eF * r.Ne ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ heF0.le; exact le_self_pow₀ hNe1 (by norm_num)
      linarith
    calc |r.kp - r.et * r.lm / (4 * (1 - r.lm) ^ 2)| * (1 / r.kc) ≤ r.eF / 2 * (2900 * r.Ne) :=
          mul_le_mul hkp hinv (by positivity) (by positivity)
      _ = 1450 * (r.eF * r.Ne) := by ring
      _ ≤ 1450 * (r.tp / 2 ^ 40) := by gcongr
  have hdec : r.kp / r.kc - 1 = (r.kp - r.et * r.lm / (4 * (1 - r.lm) ^ 2)) / r.kc +
      (r.et * r.lm / (4 * (1 - r.lm) ^ 2) / r.kc - 1) := by ring
  rw [hdec, hy]
  calc _ ≤ |(r.kp - r.et * r.lm / (4 * (1 - r.lm) ^ 2)) / r.kc| +
        |((r.et / r.eta) * (r.lm / r.lam)) * (((1 - r.lam) / (1 - r.lm)) * ((1 - r.lam) / (1 - r.lm))) - 1| :=
        abs_add_le _ _
    _ ≤ 1450 * (r.tp / 2 ^ 40) + (3 * δ * (1 + 3 * δ) + 3 * δ) := add_le_add hR hP
    _ ≤ r.tp / 16 := by
        rw [hδ]
        have : r.tp / 2 ^ 16 * (1 + 3 * (r.tp / 2 ^ 16)) ≤ r.tp / 2 ^ 16 * 2 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have : r.tp ≤ 1 := le_trans htp1 (by norm_num)
          linarith
        nlinarith

theorem nu_rel (h : r.OK) : |r.nu * (1 - r.lam) - 1| ≤ r.tp / 16 := by
  have hlr := h.lam_rel
  have hnu := h.hnu
  have htp := h.htp0
  have htp1 := h.htp1
  have heF0 := h.heF0
  have hNe1 : (1 : ℝ) ≤ r.Ne := Ne_one h
  have hd := h.hd
  set δ : ℝ := r.tp / 2 ^ 16 with hδ
  have hδ0 : 0 ≤ δ := by positivity
  have hδs : δ ≤ 1 := by
    rw [hδ]; have : r.tp ≤ 1 := le_trans htp1 (by norm_num)
    calc r.tp / 2 ^ 16 ≤ 1 / 2 ^ 16 := by gcongr
      _ ≤ 1 := by norm_num
  have hlam0 : 0 < r.lam := by unfold EncR.lam; have := h.hLe; positivity
  have hlam1 : r.lam ≤ 1 / 4 := by
    unfold EncR.lam
    rw [div_le_div_iff₀ (by have := h.hLe; positivity) (by norm_num)]
    have hL1 : (1 : ℝ) ≤ r.Le := le_trans (by norm_num) h.hLe
    have : (1 : ℝ) ≤ r.d * r.Le ^ 2 := one_le_mul_of_one_le_of_one_le hd (one_le_pow₀ hL1)
    linarith
  have hlm : |r.lm - r.lam| ≤ r.lam * δ := by
    have e : r.lm - r.lam = r.lam * (r.lm / r.lam - 1) := by field_simp
    rw [e, abs_mul, abs_of_pos hlam0]
    exact mul_le_mul_of_nonneg_left hlr hlam0.le
  have hlmd : r.lam * δ ≤ 1 / 4 := by
    calc r.lam * δ ≤ 1 / 4 * 1 := mul_le_mul hlam1 hδs hδ0 (by norm_num)
      _ = 1 / 4 := by ring
  have hlm1 : 1 / 2 ≤ 1 - r.lm := by have := (abs_le.mp hlm).2; linarith
  have hC : |(1 - r.lam) / (1 - r.lm) - 1| ≤ δ := by
    have e : (1 - r.lam) / (1 - r.lm) - 1 = (r.lm - r.lam) / (1 - r.lm) := by
      have : (1 - r.lm) ≠ 0 := by linarith
      field_simp; ring
    rw [e, abs_div, abs_of_pos (by linarith : (0 : ℝ) < 1 - r.lm), div_le_iff₀ (by linarith)]
    have : r.lam * δ ≤ δ * (1 - r.lm) := by
      have : r.lam ≤ 1 - r.lm := by linarith
      nlinarith
    linarith
  have heF : r.eF ≤ r.tp / 2 ^ 40 := by
    have h1 : (1 : ℝ) ≤ r.Ne ^ 2 * r.d ^ 4 :=
      one_le_mul_of_one_le_of_one_le (one_le_pow₀ hNe1) (one_le_pow₀ hd)
    have h2 : r.eF * 2 ^ 40 ≤ r.eF * (2 ^ 40 * (r.Ne ^ 2 * r.d ^ 4)) := by
      apply mul_le_mul_of_nonneg_left _ heF0.le
      calc (2 : ℝ) ^ 40 = 2 ^ 40 * 1 := by ring
        _ ≤ 2 ^ 40 * (r.Ne ^ 2 * r.d ^ 4) := by gcongr
    have e : r.eF * (2 ^ 40 * (r.Ne ^ 2 * r.d ^ 4)) = r.eF * (2 ^ 40 * r.Ne ^ 2 * r.d ^ 4) := by ring
    rw [le_div_iff₀ (by norm_num)]
    linarith [h.heF1]
  have hdec : r.nu * (1 - r.lam) - 1 = (r.nu - 1 / (1 - r.lm)) * (1 - r.lam) + ((1 - r.lam) / (1 - r.lm) - 1) := by
    have : (1 - r.lm) ≠ 0 := by linarith
    field_simp; ring
  rw [hdec]
  have t1 : |(r.nu - 1 / (1 - r.lm)) * (1 - r.lam)| ≤ r.eF / 2 := by
    rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < 1 - r.lam)]
    calc |r.nu - 1 / (1 - r.lm)| * (1 - r.lam) ≤ r.eF / 2 * 1 :=
          mul_le_mul hnu (by linarith) (by linarith) (by positivity)
      _ = r.eF / 2 := by ring
  calc _ ≤ |(r.nu - 1 / (1 - r.lm)) * (1 - r.lam)| + |(1 - r.lam) / (1 - r.lm) - 1| := abs_add_le _ _
    _ ≤ r.eF / 2 + δ := add_le_add t1 hC
    _ ≤ r.tp / 16 := by
        rw [hδ]
        have : r.tp / 2 ^ 40 ≤ r.tp / 32 := by gcongr <;> norm_num
        have : r.tp / 2 ^ 16 ≤ r.tp / 32 := by gcongr <;> norm_num
        linarith

theorem R_le (h : r.OK) : r.R ≤ r.Rp := by
  have hd_nonneg : 0 ≤ r.d := le_trans (by norm_num : (0 : ℝ) ≤ 1) h.hd
  have h134d_nonneg : 0 ≤ 134 * r.d := by nlinarith
  calc
    r.R = 134 * r.d * Real.sqrt r.la := rfl
    _ ≤ 134 * r.d * Real.sqrt r.l1 :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt h.hl1a) h134d_nonneg
    _ ≤ 134 * r.d * r.sR :=
      mul_le_mul_of_nonneg_left h.hsR1 h134d_nonneg
    _ ≤ r.Rp := h.hRp1

set_option maxHeartbeats 600000 in
theorem R_rel (h : r.OK) : |r.Rp / r.R - 1| ≤ r.tp / 2 ^ 14 := by
  rcases h with ⟨hd, hn, hNe, hLe, hsm, hla1, hla2, htp0, htp1, heq0, heq1, heF0, heF1, hLp1, hLp2, hLh1, hLh2, hl1a, hl1b, hrd0, hrd1, hrd2, hrn0, hrn1, hrn2, hsR1, hsR2, hsW1, hsW2, hsU1, hsU2, hep1, hep2, hlm, het, hsg, hro1, hro2, hkp, hnu, hRp1, hRp2, hsb1, hsb2, hWp1, hWp2, hA0, hB0⟩
  have hdpos : 0 < r.d := by linarith
  have hlapos : 0 < r.la := by linarith
  have hRpos : 0 < r.R := by
    have hsqrt_pos : 0 < Real.sqrt r.la := Real.sqrt_pos.mpr hlapos
    exact mul_pos (mul_pos (by norm_num) hdpos) hsqrt_pos
  have hRp_ge_R : r.R ≤ r.Rp := by
    calc
      r.R = 134 * r.d * Real.sqrt r.la := rfl
      _ ≤ 134 * r.d * Real.sqrt r.l1 :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hl1a) (by positivity)
      _ ≤ 134 * r.d * r.sR :=
        mul_le_mul_of_nonneg_left hsR1 (by positivity)
      _ ≤ r.Rp := hRp1
  have h_nonneg : 0 ≤ r.Rp / r.R - 1 := by
    have hdiv : 1 ≤ r.Rp / r.R := ((one_le_div hRpos).mpr hRp_ge_R)
    linarith
  have habs : |r.Rp / r.R - 1| = r.Rp / r.R - 1 := abs_of_nonneg h_nonneg
  rw [habs]
  have h_sqrt_la_pos : 0 < Real.sqrt r.la := Real.sqrt_pos.mpr hlapos
  have h_sqrt_la_ge_one : 1 ≤ Real.sqrt r.la := by
    calc
      1 = Real.sqrt (1 : ℝ) := by norm_num
      _ ≤ Real.sqrt r.la := Real.sqrt_le_sqrt hla1
  have h_eq_bound : r.eq ≤ r.tp / 2 ^ 18 := by
    calc
      r.eq = r.eq * 1 := by ring
      _ ≤ r.eq * (1 + r.Le) :=
        mul_le_mul_of_nonneg_left (by linarith) (by linarith [heq0])
      _ ≤ r.tp / 2 ^ 18 := heq1
  have h_eF_bound : r.eF ≤ r.tp / 2 ^ 40 := by
    have hpos : (0 : ℝ) < 2 ^ 40 := by positivity
    apply (le_div_iff₀ hpos).mpr
    have hNe_ge_one : 1 ≤ r.Ne := by
      rw [hNe]
      have h15 : (1 : ℝ) ≤ 15 * 2 ^ 17 := by norm_num
      have hd3 : (1 : ℝ) ≤ r.d ^ 3 := by
        have : 1 ^ 3 ≤ r.d ^ 3 := pow_le_pow_left₀ (by linarith) hd 3
        simpa using this
      have hn4 : (1 : ℝ) ≤ r.n ^ 4 := by
        have : 1 ^ 4 ≤ r.n ^ 4 := pow_le_pow_left₀ (by linarith) hn 4
        simpa using this
      have hstep1 : (1 : ℝ) * 1 ≤ (15 * 2 ^ 17) * r.d ^ 3 :=
        mul_le_mul h15 hd3 (by positivity) (by positivity)
      have hstep2 : ((1 : ℝ) * 1) * 1 ≤ ((15 * 2 ^ 17) * r.d ^ 3) * r.n ^ 4 :=
        mul_le_mul hstep1 hn4 (by positivity) (by positivity)
      calc
        (1 : ℝ) = (1 : ℝ) * 1 * 1 := by norm_num
        _ ≤ ((15 * 2 ^ 17) * r.d ^ 3) * r.n ^ 4 := hstep2
    calc
      r.eF * 2 ^ 40 ≤ r.eF * (2 ^ 40 * r.Ne ^ 2 * r.d ^ 4) := by
        refine mul_le_mul_of_nonneg_left ?_ (by linarith)
        have h : 1 ≤ r.Ne ^ 2 * r.d ^ 4 := by
          have hNe_sq : (1 : ℝ) ^ 2 ≤ r.Ne ^ 2 := by
            have : 1 ^ 2 ≤ r.Ne ^ 2 := pow_le_pow_left₀ (by linarith) hNe_ge_one 2
            simpa using this
          have hd_pow : (1 : ℝ) ^ 4 ≤ r.d ^ 4 := by
            have : 1 ^ 4 ≤ r.d ^ 4 := pow_le_pow_left₀ (by linarith) hd 4
            simpa using this
          calc
            (1 : ℝ) = (1 : ℝ) ^ 2 * (1 : ℝ) ^ 4 := by norm_num
            _ ≤ r.Ne ^ 2 * r.d ^ 4 :=
              mul_le_mul hNe_sq hd_pow (by positivity) (by positivity)
        nlinarith
      _ ≤ r.tp := heF1
  have h_sqrt_diff : Real.sqrt r.l1 ≤ Real.sqrt r.la + (r.l1 - r.la) := by
    have h_nonneg_l1 : 0 ≤ r.l1 := by linarith
    have h_nonneg_la : 0 ≤ r.la := by linarith
    have h_nonneg_diff_sqrt : 0 ≤ Real.sqrt r.l1 - Real.sqrt r.la := by
      have h_sqrt_le : Real.sqrt r.la ≤ Real.sqrt r.l1 := Real.sqrt_le_sqrt hl1a
      linarith
    have h_sum_sqrt_ge_one : 1 ≤ Real.sqrt r.l1 + Real.sqrt r.la := by
      linarith
    have h_diff_sq : (Real.sqrt r.l1 - Real.sqrt r.la) * (Real.sqrt r.l1 + Real.sqrt r.la) = r.l1 - r.la := by
      calc
        (Real.sqrt r.l1 - Real.sqrt r.la) * (Real.sqrt r.l1 + Real.sqrt r.la) =
            (Real.sqrt r.l1) ^ 2 - (Real.sqrt r.la) ^ 2 := by ring
        _ = r.l1 - r.la := by rw [Real.sq_sqrt h_nonneg_l1, Real.sq_sqrt h_nonneg_la]
    have h_ineq : Real.sqrt r.l1 - Real.sqrt r.la ≤ r.l1 - r.la := by
      calc
        Real.sqrt r.l1 - Real.sqrt r.la = (Real.sqrt r.l1 - Real.sqrt r.la) * 1 := by ring
        _ ≤ (Real.sqrt r.l1 - Real.sqrt r.la) * (Real.sqrt r.l1 + Real.sqrt r.la) :=
          mul_le_mul_of_nonneg_left h_sum_sqrt_ge_one h_nonneg_diff_sqrt
        _ = r.l1 - r.la := h_diff_sq
    calc
      Real.sqrt r.l1 = (Real.sqrt r.l1 - Real.sqrt r.la) + Real.sqrt r.la := by ring
      _ ≤ (r.l1 - r.la) + Real.sqrt r.la := by linarith
      _ = Real.sqrt r.la + (r.l1 - r.la) := by ring
  have h_main : r.Rp / r.R - 1 ≤ r.tp / 2 ^ 14 := by
    have hR_eq : r.R = 134 * r.d * Real.sqrt r.la := rfl
    have hRp_upper : r.Rp ≤ 134 * r.d * (Real.sqrt r.la + r.tp / 2 ^ 15 + 2 * r.eq) + r.eF := by
      have h1 : r.Rp ≤ 134 * r.d * r.sR + r.eF := hRp2
      have h2 : 134 * r.d * r.sR ≤ 134 * r.d * (Real.sqrt r.l1 + 2 * r.eq) :=
        mul_le_mul_of_nonneg_left hsR2 (by positivity)
      have h3 : 134 * r.d * (Real.sqrt r.l1 + 2 * r.eq) ≤ 134 * r.d * ((Real.sqrt r.la + (r.l1 - r.la)) + 2 * r.eq) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      have h4 : 134 * r.d * ((Real.sqrt r.la + (r.l1 - r.la)) + 2 * r.eq) ≤ 134 * r.d * (Real.sqrt r.la + (r.tp / 2 ^ 15) + 2 * r.eq) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      linarith
    have h_denom_pos : 0 < 134 * r.d * Real.sqrt r.la := by positivity
    have h_term1 : (r.tp / 2 ^ 15) / Real.sqrt r.la ≤ r.tp / 2 ^ 15 :=
      div_le_self (by positivity) h_sqrt_la_ge_one
    have h_term2 : (2 * r.eq) / Real.sqrt r.la ≤ 2 * r.eq :=
      div_le_self (by positivity) h_sqrt_la_ge_one
    have h_denom_ge : (134 : ℝ) ≤ 134 * r.d * Real.sqrt r.la := by
      nlinarith
    have h_term3 : r.eF / (134 * r.d * Real.sqrt r.la) ≤ r.eF / 134 :=
      div_le_div_of_nonneg_left (by linarith) (by norm_num) h_denom_ge
    have h_simplify : (134 * r.d * (Real.sqrt r.la + r.tp / 2 ^ 15 + 2 * r.eq) + r.eF) / (134 * r.d * Real.sqrt r.la) - 1 =
        (r.tp / 2 ^ 15) / Real.sqrt r.la + (2 * r.eq) / Real.sqrt r.la + r.eF / (134 * r.d * Real.sqrt r.la) := by
      field_simp [h_sqrt_la_pos.ne.symm]
      ring
    have h_bound : r.Rp / (134 * r.d * Real.sqrt r.la) - 1 ≤
        (r.tp / 2 ^ 15) / Real.sqrt r.la + (2 * r.eq) / Real.sqrt r.la + r.eF / (134 * r.d * Real.sqrt r.la) := by
      calc
        r.Rp / (134 * r.d * Real.sqrt r.la) - 1 ≤
            (134 * r.d * (Real.sqrt r.la + r.tp / 2 ^ 15 + 2 * r.eq) + r.eF) / (134 * r.d * Real.sqrt r.la) - 1 :=
          sub_le_sub_right (div_le_div_of_nonneg_right hRp_upper (by positivity)) 1
        _ = (r.tp / 2 ^ 15) / Real.sqrt r.la + (2 * r.eq) / Real.sqrt r.la + r.eF / (134 * r.d * Real.sqrt r.la) := h_simplify
    have h_sum : (r.tp / 2 ^ 15) / Real.sqrt r.la + (2 * r.eq) / Real.sqrt r.la + r.eF / (134 * r.d * Real.sqrt r.la) ≤
        r.tp / 2 ^ 15 + r.tp / 2 ^ 17 + r.tp / 2 ^ 40 := by
      have h12 : (r.tp / 2 ^ 15) / Real.sqrt r.la + (2 * r.eq) / Real.sqrt r.la ≤ r.tp / 2 ^ 15 + 2 * r.eq := by
        linarith
      have h3 : r.eF / (134 * r.d * Real.sqrt r.la) ≤ r.tp / 2 ^ 40 := by
        calc
          r.eF / (134 * r.d * Real.sqrt r.la) ≤ r.eF / 134 := h_term3
          _ ≤ (r.tp / 2 ^ 40) / 134 := div_le_div_of_nonneg_right h_eF_bound (by norm_num)
          _ = r.tp / (134 * 2 ^ 40) := by ring
          _ ≤ r.tp / 2 ^ 40 :=
            div_le_div_of_nonneg_left (by linarith) (by positivity)
              (show (2 : ℝ) ^ 40 ≤ 134 * (2 : ℝ) ^ 40 from by
                calc
                  (2 : ℝ) ^ 40 = 1 * (2 : ℝ) ^ 40 := by ring
                  _ ≤ 134 * (2 : ℝ) ^ 40 :=
                    mul_le_mul_of_nonneg_right (by norm_num) (by positivity))
      linarith
    have h_final : r.tp / 2 ^ 15 + r.tp / 2 ^ 17 + r.tp / 2 ^ 40 ≤ r.tp / 2 ^ 14 := by
      have htp_nonneg : 0 ≤ r.tp := by linarith
      have h_coeff : (1 : ℝ) / 2 ^ 15 + (1 : ℝ) / 2 ^ 17 + (1 : ℝ) / 2 ^ 40 ≤ (1 : ℝ) / 2 ^ 14 := by
        have h_small : (1 : ℝ) / 2 ^ 17 + (1 : ℝ) / 2 ^ 40 ≤ (1 : ℝ) / 2 ^ 15 := by
          have h1 : (1 : ℝ) / 2 ^ 17 ≤ (1 : ℝ) / 2 ^ 16 := by
            refine (one_div_le_one_div ?_ ?_).mpr ?_
            · positivity
            · positivity
            · norm_num
          have h2 : (1 : ℝ) / 2 ^ 40 ≤ (1 : ℝ) / 2 ^ 16 := by
            refine (one_div_le_one_div ?_ ?_).mpr ?_
            · positivity
            · positivity
            · norm_num
          have hsum : (1 : ℝ) / 2 ^ 16 + (1 : ℝ) / 2 ^ 16 = (1 : ℝ) / 2 ^ 15 := by ring
          linarith
        linarith
      calc
        r.tp / 2 ^ 15 + r.tp / 2 ^ 17 + r.tp / 2 ^ 40 = r.tp * ((1 : ℝ) / 2 ^ 15 + (1 : ℝ) / 2 ^ 17 + (1 : ℝ) / 2 ^ 40) := by ring
        _ ≤ r.tp * ((1 : ℝ) / 2 ^ 14) := mul_le_mul_of_nonneg_left h_coeff htp_nonneg
        _ = r.tp / 2 ^ 14 := by ring
    rw [hR_eq]
    linarith
  exact h_main

theorem sb_le (h : r.OK) : r.sb ≤ r.sbR := by
  have hd_pos : 0 < r.d :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) h.hd
  have hn_pos : 0 < r.n :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) h.hn
  have hla_pos : 0 < r.la :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) h.hla1
  have hNe_pos : 0 < r.Ne := by
    rw [h.hNe]
    positivity
  have hR_pos : 0 < R r := by
    dsimp [R]
    have hsqrt : 0 < Real.sqrt r.la := Real.sqrt_pos.mpr hla_pos
    positivity
  have hl1_pos : 0 < r.l1 :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (h.hla1.trans h.hl1a)
  have hRp_pos : 0 < r.Rp := by
    have hsR_pos : 0 < r.sR :=
      lt_of_lt_of_le (Real.sqrt_pos.mpr hl1_pos) h.hsR1
    have h134dsR_pos : 0 < 134 * r.d * r.sR := by positivity
    exact lt_of_lt_of_le h134dsR_pos h.hRp1
  have hR_le_Rp : R r ≤ r.Rp := by
    calc
      R r = 134 * r.d * Real.sqrt r.la := rfl
      _ ≤ 134 * r.d * Real.sqrt r.l1 :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt h.hl1a) (by positivity)
      _ ≤ 134 * r.d * r.sR :=
        mul_le_mul_of_nonneg_left h.hsR1 (by positivity)
      _ ≤ r.Rp := h.hRp1
  have h_sbR_eq : r.sbR = 1 / (r.Ne ^ 2 * (R r * (R r + 1))) := by
    dsimp [sbR, R]
    field_simp [hNe_pos.ne.symm, hR_pos.ne.symm]
  have h_main : 1 / (r.Ne ^ 2 * r.Rp * (r.Rp + 1)) ≤ r.sbR := by
    rw [h_sbR_eq]
    have hden1 : 0 < r.Ne ^ 2 * (R r * (R r + 1)) := by
      positivity
    have h_denom_le : r.Ne ^ 2 * (R r * (R r + 1)) ≤ r.Ne ^ 2 * r.Rp * (r.Rp + 1) := by
      have hprod : R r * (R r + 1) ≤ r.Rp * (r.Rp + 1) := by
        nlinarith
      nlinarith
    exact one_div_le_one_div_of_le hden1 h_denom_le
  calc
    r.sb ≤ 1 / (r.Ne ^ 2 * r.Rp * (r.Rp + 1)) := h.hsb2
    _ ≤ r.sbR := h_main

set_option maxHeartbeats 600000 in
theorem sb_rel (h : r.OK) : |r.sb / r.sbR - 1| ≤ r.tp / 16 := by
  have htp_pos : 0 < r.tp := h.htp0
  have heF_pos : 0 < r.eF := h.heF0
  have htp_nonneg : 0 ≤ r.tp := by linarith
  have hd_pos : 0 < r.d := by linarith [h.hd]
  have hla_pos : 0 < r.la := by linarith [h.hla1]
  have hNe_pos : 0 < r.Ne := by
    rw [h.hNe]
    have : 0 < 15 * 2 ^ 17 := by norm_num
    have hd3 : 0 < r.d ^ 3 := pow_pos hd_pos 3
    have hn4 : 0 < r.n ^ 4 := pow_pos (by linarith [h.hn]) 4
    positivity
  have hR_pos : 0 < r.R := by
    dsimp [EncR.R]
    positivity
  have hsR_pos : 0 < r.sR := by
    have hl1_pos : 0 < r.l1 := by
      have hsqrt_la_pos' : 0 < Real.sqrt r.la := Real.sqrt_pos.mpr hla_pos
      nlinarith [h.hl1a, hsqrt_la_pos']
    have h_sqrt_l1_pos : 0 < Real.sqrt r.l1 := Real.sqrt_pos.mpr hl1_pos
    nlinarith [h.hsR1, h_sqrt_l1_pos]
  have hRp_pos : 0 < r.Rp := by
    have hpos : 0 < 134 * r.d * r.sR := by positivity
    nlinarith [h.hRp1, hpos, hsR_pos]
  have hsbR_pos : 0 < r.sbR := by
    dsimp [EncR.sbR]
    positivity
  -- From sb_le, we have r.sb / r.sbR ≤ 1
  have h_sb_div_sbR_le_one : r.sb / r.sbR ≤ 1 := by
    rw [div_le_one hsbR_pos]
    exact h.sb_le
  -- So |r.sb / r.sbR - 1| = 1 - r.sb / r.sbR
  have habs_eq : |r.sb / r.sbR - 1| = 1 - r.sb / r.sbR := by
    rw [abs_of_nonpos (sub_nonpos.mpr h_sb_div_sbR_le_one)]
    ring
  rw [habs_eq]
  -- Need to show 1 - r.sb / r.sbR ≤ r.tp / 16
  -- From hsb1: 1/(Ne^2 * Rp * (Rp+1)) - eF ≤ r.sb
  have h_lower : (1 / (r.Ne ^ 2 * r.Rp * (r.Rp + 1)) - r.eF) / r.sbR ≤ r.sb / r.sbR :=
    div_le_div_of_nonneg_right h.hsb1 (by positivity)
  have h_sbR_eq : r.sbR = 1 / (r.Ne ^ 2 * r.R * (r.R + 1)) := by
    dsimp [EncR.sbR, EncR.R]
    have hNe_ne : r.Ne ≠ 0 := by linarith
    have hR_ne : r.R ≠ 0 := by linarith
    field_simp [hNe_ne, hR_ne]
  have h_lower_bound : r.R * (r.R + 1) / (r.Rp * (r.Rp + 1)) - r.eF * r.Ne ^ 2 * r.R * (r.R + 1) ≤ r.sb / r.sbR := by
    calc
      r.R * (r.R + 1) / (r.Rp * (r.Rp + 1)) - r.eF * r.Ne ^ 2 * r.R * (r.R + 1)
          = ((1 / (r.Ne ^ 2 * r.Rp * (r.Rp + 1))) / r.sbR) - (r.eF / r.sbR) := by
        rw [h_sbR_eq]
        field_simp [show r.Ne ≠ 0 from by linarith, show r.R ≠ 0 from by linarith, show r.Rp ≠ 0 from by linarith]
      _ = (1 / (r.Ne ^ 2 * r.Rp * (r.Rp + 1)) - r.eF) / r.sbR := by ring
      _ ≤ r.sb / r.sbR := h_lower
  -- Now we need to show: 1 - tp/16 ≤ R*(R+1)/(Rp*(Rp+1)) - eF*Ne^2*R*(R+1)
  -- This follows from two inequalities:
  -- (A) R*(R+1)/(Rp*(Rp+1)) ≥ 1 - tp/2^13
  -- (B) eF*Ne^2*R*(R+1) ≤ tp/2^23
  -- Then: 1 - tp/16 = 1 - tp/2^13 - tp/2^23 + (tp/2^13 + tp/2^23 - tp/16)
  --       ≤ 1 - tp/2^13 - tp/2^23  (since tp/2^13 + tp/2^23 ≤ tp/16)
  --       ≤ (A) - (B)
  have hRp_div_R_le : r.Rp / r.R ≤ 1 + r.tp / 2 ^ 14 := by
    have h_le : r.Rp / r.R - 1 ≤ r.tp / 2 ^ 14 := by
      have := abs_le.mp h.R_rel
      exact this.2
    linarith
  -- (A) R*(R+1)/(Rp*(Rp+1)) ≥ 1 - tp/2^13
  have h_A : 1 - r.tp / 2 ^ 13 ≤ r.R * (r.R + 1) / (r.Rp * (r.Rp + 1)) := by
    -- Step A1: (R+1)/(Rp+1) ≥ R/Rp  (since R ≤ Rp)
    have h_ratio_le : r.R / r.Rp ≤ (r.R + 1) / (r.Rp + 1) := by
      have h_cross : r.R * (r.Rp + 1) ≤ (r.R + 1) * r.Rp := by nlinarith [h.R_le]
      have hRp_ne : r.Rp ≠ 0 := by linarith
      calc
        r.R / r.Rp = (r.R * (r.Rp + 1)) / (r.Rp * (r.Rp + 1)) := by
          field_simp [hRp_ne]
        _ ≤ ((r.R + 1) * r.Rp) / (r.Rp * (r.Rp + 1)) :=
          (div_le_div_of_nonneg_right h_cross (by positivity))
        _ = (r.R + 1) / (r.Rp + 1) := by
          field_simp [hRp_ne]
    -- Step A2: (R/Rp)^2 ≤ R*(R+1)/(Rp*(Rp+1))
    have h_sq_bound : (r.R / r.Rp) ^ 2 ≤ r.R * (r.R + 1) / (r.Rp * (r.Rp + 1)) := by
      have h_nonneg : 0 ≤ r.R / r.Rp := div_nonneg (by linarith) (by linarith)
      calc
        (r.R / r.Rp) ^ 2 = (r.R / r.Rp) * (r.R / r.Rp) := by ring
        _ ≤ (r.R / r.Rp) * ((r.R + 1) / (r.Rp + 1)) := mul_le_mul_of_nonneg_left h_ratio_le h_nonneg
        _ = r.R * (r.R + 1) / (r.Rp * (r.Rp + 1)) := by
          field_simp [show r.Rp ≠ 0 from by linarith, show r.Rp + 1 ≠ 0 from by nlinarith]
    -- Step A3: 1/(1 + tp/2^14) ≤ R/Rp
    have h_R_div_Rp_ge : 1 / (1 + r.tp / 2 ^ 14) ≤ r.R / r.Rp := by
      have h_pos1 : 0 < 1 + r.tp / 2 ^ 14 := by nlinarith
      have h_eq : r.Rp / r.R = 1 / (r.R / r.Rp) := by field_simp
      rw [h_eq] at hRp_div_R_le
      have h_mul : 1 ≤ (r.R / r.Rp) * (1 + r.tp / 2 ^ 14) := by
        have hpos_a : 0 < r.R / r.Rp := div_pos hR_pos hRp_pos
        calc
          1 = (1 / (r.R / r.Rp)) * (r.R / r.Rp) := by field_simp
          _ ≤ (1 + r.tp / 2 ^ 14) * (r.R / r.Rp) := mul_le_mul_of_nonneg_right hRp_div_R_le hpos_a.le
          _ = (r.R / r.Rp) * (1 + r.tp / 2 ^ 14) := mul_comm _ _
      calc
        1 / (1 + r.tp / 2 ^ 14) ≤ ((r.R / r.Rp) * (1 + r.tp / 2 ^ 14)) / (1 + r.tp / 2 ^ 14) :=
          div_le_div_of_nonneg_right h_mul (by nlinarith)
        _ = r.R / r.Rp := by field_simp [show 1 + r.tp / 2 ^ 14 ≠ 0 from by nlinarith]
    -- Step A4: 1/(1 + tp/2^14)^2 ≥ 1 - 2*tp/2^14 = 1 - tp/2^13
    have h_bernoulli : 1 - r.tp / 2 ^ 13 ≤ 1 / ((1 + r.tp / 2 ^ 14) ^ 2) := by
      have hpos_sq : 0 < (1 + r.tp / 2 ^ 14) ^ 2 := by nlinarith
      apply (le_div_iff₀' hpos_sq).mpr
      have h_poly : ((2:ℝ)^14 + r.tp)^2 * ((2:ℝ)^13 - r.tp) ≤ (2:ℝ)^41 := by
        have h_diff : ((2:ℝ)^14 + r.tp)^2 * ((2:ℝ)^13 - r.tp) = (2:ℝ)^41 - 24576*r.tp^2 - r.tp^3 := by
          ring
        rw [h_diff]
        nlinarith [htp_nonneg]
      have h_div : ((2:ℝ)^14 + r.tp)^2 * ((2:ℝ)^13 - r.tp) / (2:ℝ)^41 ≤ 1 := by
        rw [div_le_one (by norm_num : 0 < (2:ℝ)^41)]
        exact h_poly
      have h_eq : ((2:ℝ)^14 + r.tp)^2 * ((2:ℝ)^13 - r.tp) / (2:ℝ)^41 = (1 + r.tp / 2 ^ 14) ^ 2 * (1 - r.tp / 2 ^ 13) := by
        field_simp
      rw [h_eq] at h_div
      exact h_div
    -- Step A5: Combine
    calc
      1 - r.tp / 2 ^ 13 ≤ 1 / ((1 + r.tp / 2 ^ 14) ^ 2) := h_bernoulli
      _ ≤ (r.R / r.Rp) ^ 2 := by
        have h_nonneg : 0 ≤ 1 / (1 + r.tp / 2 ^ 14) := div_nonneg (by nlinarith) (by nlinarith)
        have h_sq : (1 / (1 + r.tp / 2 ^ 14)) ^ 2 ≤ (r.R / r.Rp) ^ 2 := by
          nlinarith
        simpa [div_pow] using h_sq
      _ ≤ r.R * (r.R + 1) / (r.Rp * (r.Rp + 1)) := h_sq_bound
  -- (B) eF*Ne^2*R*(R+1) ≤ tp/2^23
  have h_B : r.eF * r.Ne ^ 2 * r.R * (r.R + 1) ≤ r.tp / 2 ^ 23 := by
    -- Step B1: Bound R^2 ≤ 53868 * d^3
    have hR_sq_le : r.R ^ 2 ≤ 53868 * r.d ^ 3 := by
      dsimp [EncR.R]
      have hla_sq : (Real.sqrt r.la) ^ 2 = r.la := Real.sq_sqrt (by linarith)
      have h_la_le : r.la ≤ 2 * r.d + 1 := h.hla2
      have hd_ge_one : 1 ≤ r.d := h.hd
      -- R^2 = (134*d*sqrt(la))^2 = 134^2 * d^2 * la = 17956 * d^2 * la
      -- ≤ 17956 * d^2 * (2d+1) = 35912*d^3 + 17956*d^2 ≤ 35912*d^3 + 17956*d^3 = 53868*d^3
      -- (since d ≥ 1, d^2 ≤ d^3)
      nlinarith
    -- Step B2: R*(R+1) ≤ 2*R^2 ≤ 107736 * d^3
    have hR_R1_le : r.R * (r.R + 1) ≤ 107736 * r.d ^ 3 := by
      have hR_ge_one : 1 ≤ r.R := by
        dsimp [EncR.R]
        have h134 : (1:ℝ) ≤ 134 * r.d := by nlinarith [h.hd]
        have h_sqrt_la_ge_one : 1 ≤ Real.sqrt r.la := by
          calc
            1 = Real.sqrt 1 := by norm_num
            _ ≤ Real.sqrt r.la := Real.sqrt_le_sqrt h.hla1
        nlinarith
      have h : r.R * (r.R + 1) ≤ 2 * r.R ^ 2 := by
        nlinarith
      nlinarith
    -- Step B3: eF*Ne^2*d^4 ≤ tp/2^40  (from heF1)
    have h_eF_Ne_d4 : r.eF * r.Ne ^ 2 * r.d ^ 4 ≤ r.tp / (2:ℝ)^40 := by
      have h := h.heF1
      -- h: r.eF * ((2:ℝ)^40 * r.Ne ^ 2 * r.d ^ 4) ≤ r.tp
      -- We want: r.eF * r.Ne ^ 2 * r.d ^ 4 ≤ r.tp / (2:ℝ)^40
      -- Multiply both sides by (2:ℝ)^40
      have hpos : 0 < (2:ℝ)^40 := by norm_num
      apply (le_div_iff₀' hpos).mpr
      -- Goal: (2:ℝ)^40 * (r.eF * r.Ne ^ 2 * r.d ^ 4) ≤ r.tp
      -- h says: r.eF * ((2:ℝ)^40 * r.Ne ^ 2 * r.d ^ 4) ≤ r.tp
      -- These are equal by ring
      simpa [mul_comm, mul_left_comm, mul_assoc] using h
    -- Step B4: d^3 ≤ d^4  (since d ≥ 1)
    have h_d3_le_d4 : r.d ^ 3 ≤ r.d ^ 4 := by
      have hd_ge_one : 1 ≤ r.d := h.hd
      calc
        r.d ^ 3 = 1 * r.d ^ 3 := by ring
        _ ≤ r.d * r.d ^ 3 := mul_le_mul_of_nonneg_right hd_ge_one (by positivity)
        _ = r.d ^ 4 := by ring
    -- Step B5: Combine
    have h_intermediate : r.eF * r.Ne ^ 2 * r.R * (r.R + 1) ≤ 107736 * (r.tp / (2:ℝ)^40) := by
      have h_nonneg_eF_Ne_sq : 0 ≤ r.eF * r.Ne ^ 2 := by positivity
      calc
        r.eF * r.Ne ^ 2 * r.R * (r.R + 1) = (r.eF * r.Ne ^ 2) * (r.R * (r.R + 1)) := by ring
        _ ≤ (r.eF * r.Ne ^ 2) * (107736 * r.d ^ 3) :=
          mul_le_mul_of_nonneg_left hR_R1_le h_nonneg_eF_Ne_sq
        _ = 107736 * (r.eF * r.Ne ^ 2 * r.d ^ 3) := by ring
        _ ≤ 107736 * (r.eF * r.Ne ^ 2 * r.d ^ 4) := by
          have hpos' : (0:ℝ) ≤ 107736 := by norm_num
          refine mul_le_mul_of_nonneg_left ?_ hpos'
          have h_nonneg_eF_Ne_sq' : 0 ≤ r.eF * r.Ne ^ 2 := by positivity
          refine mul_le_mul_of_nonneg_left h_d3_le_d4 h_nonneg_eF_Ne_sq'
        _ ≤ 107736 * (r.tp / (2:ℝ)^40) := by
          have hpos' : (0:ℝ) ≤ 107736 := by norm_num
          exact mul_le_mul_of_nonneg_left h_eF_Ne_d4 hpos'
    -- Step B6: 107736 / 2^40 ≤ 1/2^23
    have h_final : 107736 * (r.tp / (2:ℝ)^40) ≤ r.tp / 2 ^ 23 := by
      have hpos23 : 0 < (2:ℝ)^23 := by norm_num
      apply (le_div_iff₀' hpos23).mpr
      -- Goal: (2:ℝ)^23 * (107736 * (r.tp / (2:ℝ)^40)) ≤ r.tp
      -- i.e., 107736 * r.tp * (2:ℝ)^23 / (2:ℝ)^40 ≤ r.tp
      -- Multiply both sides by (2:ℝ)^40: 107736 * r.tp * (2:ℝ)^23 ≤ r.tp * (2:ℝ)^40
      have h_const : (107736 : ℝ) * (2:ℝ)^23 ≤ (2:ℝ)^40 := by norm_num
      have h_mul : (107736 : ℝ) * r.tp * (2:ℝ)^23 ≤ r.tp * (2:ℝ)^40 := by
        have h := mul_le_mul_of_nonneg_left h_const htp_nonneg
        -- h: r.tp * (107736 * 2^23) ≤ r.tp * 2^40
        simpa [mul_comm, mul_left_comm, mul_assoc] using h
      -- Now we need to relate this to the goal
      -- Goal: (2:ℝ)^23 * (107736 * (r.tp / (2:ℝ)^40)) ≤ r.tp
      -- = 107736 * r.tp * (2:ℝ)^23 / (2:ℝ)^40 ≤ r.tp
      -- Multiply by (2:ℝ)^40: 107736 * r.tp * (2:ℝ)^23 ≤ r.tp * (2:ℝ)^40
      -- This is exactly h_mul
      calc
        (2:ℝ)^23 * (107736 * (r.tp / (2:ℝ)^40)) = (107736 * r.tp * (2:ℝ)^23) / (2:ℝ)^40 := by ring
        _ ≤ (r.tp * (2:ℝ)^40) / (2:ℝ)^40 :=
          div_le_div_of_nonneg_right h_mul (by norm_num : 0 ≤ (2:ℝ)^40)
        _ = r.tp := by field_simp
    exact h_intermediate.trans h_final
  -- Combine (A) and (B): tp/2^13 + tp/2^23 ≤ tp/16
  have h_tp_sum : r.tp / 2 ^ 13 + r.tp / 2 ^ 23 ≤ r.tp / 16 := by
    have h_norm : (1 : ℝ) / 2 ^ 13 + (1 : ℝ) / 2 ^ 23 ≤ (1 : ℝ) / 16 := by norm_num
    have h_diff_nonpos : (1 : ℝ) / 2 ^ 13 + (1 : ℝ) / 2 ^ 23 - (1 : ℝ) / 16 ≤ 0 := by norm_num
    have h_nonpos : r.tp * ((1 : ℝ) / 2 ^ 13 + (1 : ℝ) / 2 ^ 23 - (1 : ℝ) / 16) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos htp_nonneg h_diff_nonpos
    linarith
  have h_combined : 1 - r.tp / 16 ≤ r.R * (r.R + 1) / (r.Rp * (r.Rp + 1)) - r.eF * r.Ne ^ 2 * r.R * (r.R + 1) := by
    linarith
  -- Final step
  linarith

theorem W_le (h : r.OK) : r.W0 ≤ r.Wp := by
  obtain ⟨hd, -, hNe, -, hLp, -⟩ := h.base
  have hR := h.R_le
  have hsq : Real.sqrt (r.Ne / r.Le) ≤ r.sW := by
    refine le_trans (Real.sqrt_le_sqrt ?_) h.hsW1
    exact div_le_div_of_nonneg_left hNe.le hLp h.hLp2
  have h4 : 4 * r.d * Real.sqrt (r.Ne / r.Le) ≤ 4 * r.d * r.sW :=
    mul_le_mul_of_nonneg_left hsq (by positivity)
  have := h.hWp1
  simp only [EncR.W0]
  linarith

theorem W_rel (h : r.OK) : |r.Wp / r.W0 - 1| ≤ r.tp / 16 := by
  obtain ⟨hd0, hn0, hNe0, hLe0, hLp0, -, -, -, -, -, heqb, heFb⟩ := h.base
  obtain ⟨hr1, hr2, -⟩ := h.Lp_rat
  have hRr := h.R_rel
  have hWl := h.W_le
  have htp := h.htp0
  have heq0 := h.heq0
  have heF0 := h.heF0
  have hd := h.hd
  have hRd : 134 * r.d ≤ r.R := by
    unfold EncR.R
    have : 1 ≤ Real.sqrt r.la := by rw [Real.one_le_sqrt]; exact h.hla1
    nlinarith
  have hR0 : 0 < r.R := by linarith
  have hS0 : 0 ≤ Real.sqrt (r.Ne / r.Le) := Real.sqrt_nonneg _
  have hW0R : r.R ≤ r.W0 := by
    unfold EncR.W0
    have : 0 ≤ 4 * r.d * Real.sqrt (r.Ne / r.Le) := by positivity
    linarith
  have hW0 : 0 < r.W0 := by linarith
  have hRp : r.Rp ≤ r.R * (1 + r.tp / 2 ^ 14) := by
    have h1 := (abs_le.mp hRr).2
    have e : r.Rp / r.R - 1 = (r.Rp - r.R) / r.R := by field_simp
    rw [e, div_le_iff₀ hR0] at h1
    nlinarith
  have hsq : Real.sqrt (r.Ne / r.Lp) ≤ Real.sqrt (r.Ne / r.Le) * (1 + r.tp / 2 ^ 22) := by
    have e : r.Ne / r.Lp = r.Ne / r.Le * (r.Le / r.Lp) := by field_simp
    rw [e, Real.sqrt_mul (by positivity)]
    apply mul_le_mul_of_nonneg_left _ hS0
    refine le_trans ?_ hr2
    rw [Real.sqrt_le_left (by linarith)]
    nlinarith
  have hsW := h.hsW2
  have hWp := h.hWp2
  -- `Wp ≤ W0 (1 + tp/2^14) + 8 d eq + eF`
  have hup : r.Wp ≤ r.W0 * (1 + r.tp / 2 ^ 14) + 8 * r.d * r.eq + r.eF := by
    have a1 : 4 * r.d * r.sW ≤ 4 * r.d * (Real.sqrt (r.Ne / r.Le) * (1 + r.tp / 2 ^ 22) + 2 * r.eq) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity); linarith
    have a2 : 4 * r.d * (Real.sqrt (r.Ne / r.Le) * (1 + r.tp / 2 ^ 22)) ≤
        4 * r.d * (Real.sqrt (r.Ne / r.Le) * (1 + r.tp / 2 ^ 14)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply mul_le_mul_of_nonneg_left _ hS0
      have : r.tp / 2 ^ 22 ≤ r.tp / 2 ^ 14 := by gcongr <;> norm_num
      linarith
    have e : r.W0 * (1 + r.tp / 2 ^ 14) =
        r.R * (1 + r.tp / 2 ^ 14) + 4 * r.d * (Real.sqrt (r.Ne / r.Le) * (1 + r.tp / 2 ^ 14)) := by
      unfold EncR.W0; ring
    nlinarith
  -- the small terms over `W0`
  have hNe1 : (1 : ℝ) ≤ r.Ne := Ne_one h
  have heF : r.eF ≤ r.tp / 2 ^ 40 := by
    have : r.eF ≤ r.eF * r.Ne ^ 2 := le_mul_of_one_le_right heF0.le (one_le_pow₀ hNe1)
    linarith
  have hsmall : 8 * r.d * r.eq + r.eF ≤ r.W0 * (r.tp / 2 ^ 17) := by
    have b1 : 8 * r.d * r.eq ≤ 8 * r.d * (r.tp / 2 ^ 18) := by gcongr
    have b2 : r.W0 * (r.tp / 2 ^ 17) ≥ 134 * r.d * (r.tp / 2 ^ 17) := by
      apply mul_le_mul_of_nonneg_right (le_trans hRd hW0R) (by positivity)
    have b3 : r.tp / 2 ^ 40 ≤ r.d * (r.tp / 2 ^ 40) := le_mul_of_one_le_left (by positivity) hd
    nlinarith
  have hub : r.Wp / r.W0 - 1 ≤ r.tp / 16 := by
    rw [sub_le_iff_le_add, div_le_iff₀ hW0]
    nlinarith
  have hlb : 0 ≤ r.Wp / r.W0 - 1 := by
    rw [sub_nonneg, le_div_iff₀ hW0]; linarith
  rw [abs_of_nonneg hlb]; exact hub

theorem A0_rel (h : r.OK) : |r.A0 / Real.sqrt r.sig2 - 1| ≤ r.tp * Real.sqrt (8 * r.Le) + r.tp / 16 := by
  have hbase := base h
  have hsig2_rel := sig2_rel h
  have htp_pos : 0 < r.tp := h.htp0
  have heq_pos : 0 < r.eq := h.heq0
  have hpos_sig2 : 0 < r.sig2 := by
    dsimp [EncR.sig2]
    have hLe : 0 < r.Le := by linarith
    positivity
  have hpos_sqrt_sig2 : 0 < Real.sqrt r.sig2 := Real.sqrt_pos.mpr hpos_sig2
  have h_sg_nonneg : 0 ≤ r.sg := by
    have hpos_ratio : 0 < 1 - r.tp / ((2 : ℝ) ^ 16) := by
      have htp_small : r.tp ≤ 1 / ((2 : ℝ) ^ 160) := h.htp1
      nlinarith
    have h_lower : 1 - r.tp / ((2 : ℝ) ^ 16) ≤ r.sg / r.sig2 := by
      have h_abs := abs_le.mp hsig2_rel
      linarith
    have h_sg_div_pos : 0 < r.sg / r.sig2 := by linarith
    rcases div_pos_iff.mp h_sg_div_pos with ⟨hsgh, hs2h⟩ | ⟨hsgl, hs2l⟩
    · exact hsgh.le
    · linarith
  have h_sqrt_sg_nonneg : 0 ≤ Real.sqrt r.sg := Real.sqrt_nonneg _
  -- key lemma: |√sg - √sig2| ≤ √sig2 * r.tp/2^16
  have h_sqrt_diff : |Real.sqrt r.sg - Real.sqrt r.sig2| ≤ Real.sqrt r.sig2 * (r.tp / ((2 : ℝ) ^ 16)) := by
    have hsum_pos : 0 < Real.sqrt r.sg + Real.sqrt r.sig2 := by positivity
    have hprod_eq : (Real.sqrt r.sg - Real.sqrt r.sig2) * (Real.sqrt r.sg + Real.sqrt r.sig2) = r.sg - r.sig2 := by
      ring_nf
      rw [Real.sq_sqrt h_sg_nonneg, Real.sq_sqrt (by positivity : 0 ≤ r.sig2)]
    have h_diff_eq : Real.sqrt r.sg - Real.sqrt r.sig2 = (r.sg - r.sig2) / (Real.sqrt r.sg + Real.sqrt r.sig2) := by
      field_simp [hsum_pos.ne']
      nlinarith
    rw [h_diff_eq, abs_div, abs_of_pos hsum_pos]
    have h_num_bound : |r.sg - r.sig2| ≤ r.sig2 * (r.tp / ((2 : ℝ) ^ 16)) := by
      have h_div_bound : |r.sg / r.sig2 - 1| ≤ r.tp / ((2 : ℝ) ^ 16) := hsig2_rel
      have h_eq_div : r.sg / r.sig2 - 1 = (r.sg - r.sig2) / r.sig2 := by
        field_simp [hpos_sig2.ne']
      rw [h_eq_div, abs_div, abs_of_pos hpos_sig2] at h_div_bound
      have h_mul : |r.sg - r.sig2| ≤ r.sig2 * (r.tp / ((2 : ℝ) ^ 16)) := by
        have htemp := mul_le_mul_of_nonneg_right h_div_bound hpos_sig2.le
        have hleft : (|r.sg - r.sig2| / r.sig2) * r.sig2 = |r.sg - r.sig2| := by
          field_simp [hpos_sig2.ne']
        rw [hleft] at htemp
        simpa [mul_comm] using htemp
      exact h_mul
    have h_denom_bound : Real.sqrt r.sig2 ≤ Real.sqrt r.sg + Real.sqrt r.sig2 := by nlinarith
    have h_nonneg_prod : 0 ≤ r.sig2 * (r.tp / ((2 : ℝ) ^ 16)) := by
      apply mul_nonneg hpos_sig2.le
      apply div_nonneg htp_pos.le (by norm_num)
    calc
      |r.sg - r.sig2| / (Real.sqrt r.sg + Real.sqrt r.sig2) ≤ (r.sig2 * (r.tp / ((2 : ℝ) ^ 16))) / (Real.sqrt r.sg + Real.sqrt r.sig2) := by
        refine div_le_div_of_nonneg_right h_num_bound (by positivity)
      _ ≤ (r.sig2 * (r.tp / ((2 : ℝ) ^ 16))) / Real.sqrt r.sig2 := by
        refine div_le_div_of_nonneg_left h_nonneg_prod hpos_sqrt_sig2 h_denom_bound
      _ = Real.sqrt r.sig2 * (r.tp / ((2 : ℝ) ^ 16)) := by
        field_simp [hpos_sqrt_sig2.ne']
        rw [Real.sq_sqrt (by positivity : 0 ≤ r.sig2)]
  -- bound |r.A0 - √sig2|
  have h_A0_sqrt_sig2 : |r.A0 - Real.sqrt r.sig2| ≤ r.tp + Real.sqrt r.sig2 * (r.tp / ((2 : ℝ) ^ 16)) := by
    have h_tri : |r.A0 - Real.sqrt r.sig2| ≤ |r.A0 - r.sU| + |r.sU - Real.sqrt r.sg| + |Real.sqrt r.sg - Real.sqrt r.sig2| := by
      calc
        |r.A0 - Real.sqrt r.sig2| = |(r.A0 - r.sU) + (r.sU - Real.sqrt r.sg) + (Real.sqrt r.sg - Real.sqrt r.sig2)| := by ring_nf
        _ ≤ |r.A0 - r.sU| + |r.sU - Real.sqrt r.sg| + |Real.sqrt r.sg - Real.sqrt r.sig2| := abs_add_three _ _ _
    have h1 : |r.A0 - r.sU| ≤ r.tp / 2 := h.hA0
    have h2 : |r.sU - Real.sqrt r.sg| ≤ 2 * r.eq := by
      rw [abs_le]
      constructor
      · -- -(2*r.eq) ≤ r.sU - √r.sg
        -- From hsU1: √r.sg ≤ r.sU, so 0 ≤ r.sU - √r.sg
        -- From heq_pos: 0 < r.eq, so -(2*r.eq) < 0
        -- So -(2*r.eq) < 0 ≤ r.sU - √r.sg
        have h_nonneg : 0 ≤ r.sU - Real.sqrt r.sg := sub_nonneg.mpr h.hsU1
        have h_neg : -(2 * r.eq) ≤ 0 := by
          have : 0 ≤ 2 * r.eq := by nlinarith
          linarith
        linarith
      · -- r.sU - √r.sg ≤ 2*r.eq
        -- From hsU2: r.sU ≤ √r.sg + 2*r.eq
        -- Subtract √r.sg from both sides
        have h := sub_le_sub_right h.hsU2 (Real.sqrt r.sg)
        simpa [add_sub_cancel_left] using h
    have h_eq_bound : r.tp / 2 + 2 * r.eq ≤ r.tp := by
      have heq_bound : r.eq ≤ r.tp / ((2 : ℝ) ^ 18) := by
        rcases hbase with ⟨_, _, _, _, _, _, _, _, _, _, heq_bound', _⟩
        exact heq_bound'
      have hpow : (2 : ℝ) ^ 18 = 262144 := by norm_num
      rw [hpow] at heq_bound
      -- heq_bound: r.eq ≤ r.tp / 262144
      -- So 2*r.eq ≤ r.tp / 131072 ≤ r.tp / 2
      have h_two_eq : 2 * r.eq ≤ r.tp / 2 := by
        have htemp : 2 * r.eq ≤ 2 * (r.tp / 262144) := by nlinarith
        have htemp2 : 2 * (r.tp / 262144) = r.tp / 131072 := by ring
        rw [htemp2] at htemp
        have h_div_le : r.tp / 131072 ≤ r.tp / 2 := by
          refine div_le_div_of_nonneg_left htp_pos.le (by norm_num) (by norm_num : (2 : ℝ) ≤ 131072)
        nlinarith
      linarith
    nlinarith
  -- divide by √sig2
  have h_div : |r.A0 / Real.sqrt r.sig2 - 1| ≤ r.tp / Real.sqrt r.sig2 + r.tp / ((2 : ℝ) ^ 16) := by
    have h_sub_eq : r.A0 / Real.sqrt r.sig2 - 1 = (r.A0 - Real.sqrt r.sig2) / Real.sqrt r.sig2 := by
      field_simp [hpos_sqrt_sig2.ne']
    rw [h_sub_eq, abs_div, abs_of_pos hpos_sqrt_sig2]
    calc
      |r.A0 - Real.sqrt r.sig2| / Real.sqrt r.sig2 ≤ (r.tp + Real.sqrt r.sig2 * (r.tp / ((2 : ℝ) ^ 16))) / Real.sqrt r.sig2 := by
        refine div_le_div_of_nonneg_right h_A0_sqrt_sig2 (by positivity)
      _ = r.tp / Real.sqrt r.sig2 + (Real.sqrt r.sig2 * (r.tp / ((2 : ℝ) ^ 16))) / Real.sqrt r.sig2 := by ring
      _ = r.tp / Real.sqrt r.sig2 + r.tp / ((2 : ℝ) ^ 16) := by
        field_simp [hpos_sqrt_sig2.ne']
  -- final bound using 1/√sig2 = √(8*r.Le) and tp/2^16 ≤ tp/16
  have h_sqrt_inv : 1 / Real.sqrt r.sig2 = Real.sqrt (8 * r.Le) := by
    have hLe : 0 < r.Le := by linarith
    have hpos_one : 0 ≤ (1 : ℝ) := by norm_num
    calc
      1 / Real.sqrt r.sig2 = Real.sqrt (1) / Real.sqrt r.sig2 := by norm_num
      _ = Real.sqrt (1 / r.sig2) := by rw [Real.sqrt_div hpos_one _]
      _ = Real.sqrt (1 / (1 / (8 * r.Le))) := rfl
      _ = Real.sqrt (8 * r.Le) := by field_simp [hLe.ne']
  have h_tp_div : r.tp / ((2 : ℝ) ^ 16) ≤ r.tp / 16 := by
    have hpow : (16 : ℝ) ≤ (2 : ℝ) ^ 16 := by norm_num
    exact div_le_div_of_nonneg_left htp_pos.le (by norm_num) hpow
  calc
    |r.A0 / Real.sqrt r.sig2 - 1| ≤ r.tp / Real.sqrt r.sig2 + r.tp / ((2 : ℝ) ^ 16) := h_div
    _ = r.tp * (1 / Real.sqrt r.sig2) + r.tp / ((2 : ℝ) ^ 16) := by ring
    _ = r.tp * Real.sqrt (8 * r.Le) + r.tp / ((2 : ℝ) ^ 16) := by rw [h_sqrt_inv]
    _ ≤ r.tp * Real.sqrt (8 * r.Le) + r.tp / 16 := by
      simpa [add_comm] using add_le_add_right h_tp_div (r.tp * Real.sqrt (8 * r.Le))

theorem sqrt_sg_rel (h : r.OK) : 0 < Real.sqrt r.sig2 ∧ Real.sqrt r.sig2 ≤ 1 ∧
    |Real.sqrt r.sg - Real.sqrt r.sig2| ≤ Real.sqrt r.sig2 * (r.tp / 2 ^ 16) ∧
    1 / Real.sqrt r.sig2 = Real.sqrt (8 * r.Le) := by
  have hsr := h.sig2_rel
  have htp := h.htp0
  have htp1 := h.htp1
  have hL1 : (1 : ℝ) ≤ r.Le := le_trans (by norm_num) h.hLe
  have hs2 : 0 < r.sig2 := by unfold EncR.sig2; positivity
  have hs21 : r.sig2 ≤ 1 := by
    unfold EncR.sig2; rw [div_le_one (by positivity)]; linarith
  have hs0 : 0 < Real.sqrt r.sig2 := Real.sqrt_pos.mpr hs2
  have hs1 : Real.sqrt r.sig2 ≤ 1 := by rw [Real.sqrt_le_one]; exact hs21
  have hdiff : |r.sg - r.sig2| ≤ r.sig2 * (r.tp / 2 ^ 16) := by
    have e : r.sg / r.sig2 - 1 = (r.sg - r.sig2) / r.sig2 := by field_simp
    rw [e, abs_div, abs_of_pos hs2, div_le_iff₀ hs2] at hsr
    linarith
  have hsg0 : 0 ≤ r.sg := by
    have := (abs_le.mp hdiff).1
    have : r.sig2 * (r.tp / 2 ^ 16) ≤ r.sig2 := by
      apply mul_le_of_le_one_right hs2.le
      have : r.tp ≤ 1 := le_trans htp1 (by norm_num)
      linarith
    linarith
  refine ⟨hs0, hs1, ?_, ?_⟩
  · have hsum : Real.sqrt r.sig2 ≤ Real.sqrt r.sg + Real.sqrt r.sig2 := by
      linarith [Real.sqrt_nonneg r.sg]
    have hsum0 : 0 < Real.sqrt r.sg + Real.sqrt r.sig2 := by linarith
    have e : Real.sqrt r.sg - Real.sqrt r.sig2 = (r.sg - r.sig2) / (Real.sqrt r.sg + Real.sqrt r.sig2) := by
      rw [eq_div_iff hsum0.ne']
      have h1 := Real.sq_sqrt hsg0
      have h2 := Real.sq_sqrt hs2.le
      nlinarith
    rw [e, abs_div, abs_of_pos hsum0, div_le_iff₀ hsum0]
    calc |r.sg - r.sig2| ≤ r.sig2 * (r.tp / 2 ^ 16) := hdiff
      _ = Real.sqrt r.sig2 * (r.tp / 2 ^ 16) * Real.sqrt r.sig2 := by
          rw [mul_comm (Real.sqrt r.sig2) _, mul_assoc, Real.mul_self_sqrt hs2.le]; ring
      _ ≤ Real.sqrt r.sig2 * (r.tp / 2 ^ 16) * (Real.sqrt r.sg + Real.sqrt r.sig2) := by
          apply mul_le_mul_of_nonneg_left hsum; positivity
  · unfold EncR.sig2
    rw [Real.sqrt_div' 1 (by positivity : (0 : ℝ) ≤ 8 * r.Le), Real.sqrt_one, one_div_div, div_one]

theorem B0_rel (h : r.OK) : |r.B0 * Real.sqrt r.sig2 - 1| ≤ r.tp + r.tp / 16 := by
  obtain ⟨hs0, hs1, hus, hinv⟩ := sqrt_sg_rel h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, heqb, -⟩ := h.base
  set s := Real.sqrt r.sig2 with hs
  have htp := h.htp0
  have htp1 := h.htp1
  have heq0 := h.heq0
  have heq1 := h.heq1
  have hL1 : (1 : ℝ) ≤ r.Le := le_trans (by norm_num) h.hLe
  have hU1 := h.hsU1
  have hU2 := h.hsU2
  have hB := h.hB0
  have hUs : |r.sU - s| ≤ 2 * r.eq + s * (r.tp / 2 ^ 16) := by
    have h1 : |r.sU - Real.sqrt r.sg| ≤ 2 * r.eq := by
      rw [abs_le]; constructor <;> linarith
    calc |r.sU - s| = |(r.sU - Real.sqrt r.sg) + (Real.sqrt r.sg - s)| := by ring_nf
      _ ≤ |r.sU - Real.sqrt r.sg| + |Real.sqrt r.sg - s| := abs_add_le _ _
      _ ≤ 2 * r.eq + s * (r.tp / 2 ^ 16) := add_le_add h1 hus
  have heqs : r.eq * (1 / s) ≤ r.tp / 2 ^ 15 := by
    rw [hinv]
    have hsq : Real.sqrt (8 * r.Le) ≤ 8 * (1 + r.Le) := by
      rw [Real.sqrt_le_left (by positivity)]; nlinarith
    calc r.eq * Real.sqrt (8 * r.Le) ≤ r.eq * (8 * (1 + r.Le)) := mul_le_mul_of_nonneg_left hsq heq0.le
      _ = 8 * (r.eq * (1 + r.Le)) := by ring
      _ ≤ 8 * (r.tp / 2 ^ 18) := by linarith
      _ = r.tp / 2 ^ 15 := by ring
  have heq_s : r.eq ≤ s * r.tp / 32768 := by
    have := mul_le_mul_of_nonneg_left heqs hs0.le
    have e : s * (r.eq * (1 / s)) = r.eq := by field_simp
    have e2 : s * (r.tp / 2 ^ 15) = s * r.tp / 32768 := by ring
    linarith
  have hst : s * r.tp ≤ s := mul_le_of_le_one_right hs0.le (le_trans htp1 (by norm_num))
  have e16 : s * (r.tp / 2 ^ 16) = s * r.tp / 65536 := by ring
  have hsU : s / 2 ≤ r.sU := by
    have := (abs_le.mp hUs).1
    have hst0 : 0 ≤ s * r.tp := by positivity
    linarith
  have hsU0 : 0 < r.sU := by linarith
  have hdec : r.B0 * s - 1 = (r.B0 - 1 / r.sU) * s + (s - r.sU) / r.sU := by
    field_simp; ring
  rw [hdec]
  have t1 : |(r.B0 - 1 / r.sU) * s| ≤ r.tp / 2 := by
    rw [abs_mul, abs_of_pos hs0]
    calc |r.B0 - 1 / r.sU| * s ≤ r.tp / 2 * 1 := mul_le_mul hB hs1 hs0.le (by positivity)
      _ = r.tp / 2 := by ring
  have t2 : |(s - r.sU) / r.sU| ≤ (2 * r.eq + s * (r.tp / 2 ^ 16)) / (s / 2) := by
    rw [abs_div, abs_of_pos hsU0, abs_sub_comm]
    exact div_le_div₀ (by positivity) hUs (by positivity) hsU
  have t3 : (2 * r.eq + s * (r.tp / 2 ^ 16)) / (s / 2) ≤ r.tp / 2 ^ 12 := by
    rw [div_le_iff₀ (by positivity)]
    have e : r.tp / 2 ^ 12 * (s / 2) = s * r.tp / 8192 := by ring
    linarith
  calc _ ≤ |(r.B0 - 1 / r.sU) * s| + |(s - r.sU) / r.sU| := abs_add_le _ _
    _ ≤ r.tp / 2 + r.tp / 2 ^ 12 := by linarith
    _ ≤ r.tp + r.tp / 16 := by
        have : r.tp / 2 ^ 12 ≤ r.tp / 16 := by gcongr <;> norm_num
        linarith

end AdversarialBco.Bit.PieceA.EncR.OK
