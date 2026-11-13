/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XTriZ

@[expose] public section

/-!
# TRI-M, the constants in integers and the scan

The constants of `triPosQ` (Bit/RoutQ.lean) as integer formulas the program computes (`eloI`, `kgN`, `d2N`, the
numerators and denominators of the ceilings), their equalities with the rational definitions, the polynomial bounds
`2^L ≤ 2^32 d^4` and `2^{L_h} ≤ 2^42 d^6` from the minimality of `triSQ d`, the scan (`scan_spec`), the
invariance of `triUQ` under positive scalings, the floor identity of the diagonal entry.
-/

namespace AdversarialBco.Bit.TriM

open AdversarialBco.Bit AdversarialBco.Bit.RQ Matrix

/-- `20000 / E_lo`. -/
def eloI (d : ℕ) : ℕ := 258986112 * d ^ 2 * triLh (triSQ d) * (2 ^ triLh (triSQ d) - 1)

/-- `b = triBQ d`, an integer. -/
def bI (d : ℕ) : ℕ := 161 * 2 ^ (triLa (triSQ d) - 10)

/-- `r = triRQ d`, an integer. -/
def rI (d : ℕ) : ℕ := 2 ^ (triLa (triSQ d) - 3)

/-- The numerator of the argument of `triKgQ` over `20000`. -/
def kgN (d : ℕ) : ℕ := 16 * bI d * (d + 1) * d * (8 * d + 2) * eloI d

/-- `Δ² 4^{j_a}`. -/
def d2N (d : ℕ) : ℕ :=
  4 * d * rI d ^ 2 * 4 ^ triJaQ d + d * (bI d * 2 ^ triJaQ d - 1) ^ 2 + 2 * d * (d - 1) * bI d ^ 2 * 4 ^ triJaQ d

/-- The argument of `triBvQ` is `bvN / bvD`. -/
def bvN (d : ℕ) : ℕ := 64 * (d + 1) ^ 2 * d2N d * eloI d ^ 2

/-- The argument of `triBvQ` is `bvN / bvD`. -/
def bvD (d : ℕ) : ℕ := 4 ^ triJaQ d * 400000000

/-- `G_up`, an integer. -/
def guN (d : ℕ) : ℕ := Nat.sqrt (8 * d * triKgQ d) + 2 + 2 ^ (triJaQ d - 3)

/-- `(G_up + β_up) 2^{B_v}`. -/
def gbN (d : ℕ) : ℕ := guN d * 2 ^ triBvQ d + d + 1

/-- The argument of `triNeQ` is `neN / neD`. -/
def neN (d ℓ : ℕ) : ℕ := 8 * d2N d * eloI d ^ 2 * (9 * gbN d ^ 2 + 8 * guN d ^ 2 * ℓ * 4 ^ triBvQ d)

/-- The argument of `triNeQ` is `neN / neD`. -/
def neD (d : ℕ) : ℕ := 9 * 4 ^ (triBvQ d + triJaQ d) * 400000000

/-- The argument of `triJsQ` is `jsN / jsD`. -/
def jsN (d ℓ : ℕ) : ℕ := gbN d ^ 2 * 2 ^ triNeQ d ℓ * 4 ^ triJaQ d

/-- The argument of `triJsQ` is `jsN / jsD`. -/
def jsD (d : ℕ) : ℕ := 4 ^ triBvQ d * d2N d


theorem triSQ_bounds (d : ℕ) : 4 ≤ triSQ d ∧ triSQ d ≤ 7 * (d + 10) := by
  have hspec := Nat.find_spec (pg_par_exists d)
  have hlower : 4 ≤ triSQ d := hspec.1
  have hupper : triSQ d ≤ 7 * (d + 10) := by
    apply Nat.find_min' (pg_par_exists d)
    have hlower' : 4 ≤ 7 * (d + 10) := by omega
    have hineq : 2086812 * d ^ 2 * ((50 * (7 * (d + 10)) ^ 2 + 68) / 69) ≤
        125 * (2 ^ (5 * (7 * (d + 10)) ^ 2 / 7) - 1) ^ 2 := by
      set x := d + 10 with hx
      have hx1 : 10 ≤ x := by omega
      have h57 : 5 * (7 * x) ^ 2 / 7 = 35 * x ^ 2 := by
        rw [show 5 * (7 * x) ^ 2 = 7 * (35 * x ^ 2) by ring, Nat.mul_div_cancel_left _ (by norm_num)]
      rw [h57]
      have hdiv : (50 * (7 * x) ^ 2 + 68) / 69 ≤ 2518 * x ^ 2 := by
        calc (50 * (7 * x) ^ 2 + 68) / 69 ≤ 50 * (7 * x) ^ 2 + 68 := Nat.div_le_self _ _
          _ ≤ 2518 * x ^ 2 := by nlinarith
      have hdx : d ^ 2 ≤ x ^ 2 := Nat.pow_le_pow_left (by omega) 2
      have hL : 2086812 * d ^ 2 * ((50 * (7 * x) ^ 2 + 68) / 69) ≤ 2 ^ 33 * x ^ 4 := by
        calc 2086812 * d ^ 2 * ((50 * (7 * x) ^ 2 + 68) / 69) ≤ 2086812 * x ^ 2 * (2518 * x ^ 2) :=
            Nat.mul_le_mul (Nat.mul_le_mul_left _ hdx) hdiv
          _ = 5254592616 * x ^ 4 := by ring
          _ ≤ 2 ^ 33 * x ^ 4 := Nat.mul_le_mul_right _ (by norm_num)
      have hx4 : x ^ 4 ≤ 2 ^ (4 * x) := by
        rw [mul_comm, pow_mul]
        exact Nat.pow_le_pow_left (Nat.lt_two_pow_self).le 4
      have hk : 33 + 4 * x ≤ 35 * x ^ 2 := by nlinarith
      have hK : 4 ≤ 2 ^ (35 * x ^ 2) := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ (35 * x ^ 2) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
      have hR : 2 ^ (35 * x ^ 2) ≤ 125 * (2 ^ (35 * x ^ 2) - 1) ^ 2 := by
        obtain ⟨j, hj⟩ : ∃ j, 2 ^ (35 * x ^ 2) = j + 1 := ⟨2 ^ (35 * x ^ 2) - 1, by omega⟩
        rw [hj, Nat.add_sub_cancel]
        have hj3 : 3 ≤ j := by omega
        nlinarith
      calc 2086812 * d ^ 2 * ((50 * (7 * x) ^ 2 + 68) / 69) ≤ 2 ^ 33 * x ^ 4 := hL
        _ ≤ 2 ^ 33 * 2 ^ (4 * x) := Nat.mul_le_mul_left _ hx4
        _ = 2 ^ (33 + 4 * x) := (pow_add _ _ _).symm
        _ ≤ 2 ^ (35 * x ^ 2) := Nat.pow_le_pow_right (by norm_num) hk
        _ ≤ 125 * (2 ^ (35 * x ^ 2) - 1) ^ 2 := hR
    exact And.intro hlower' hineq
  exact And.intro hlower hupper

theorem triJaQ_ge {d : ℕ} (hd : 1 ≤ d) : 6 ≤ triJaQ d := by
  have h2pos : 1 < 2 := by norm_num
  have hsq : 4 ≤ triSQ d := (triSQ_bounds d).1
  have hprod : 32 < 9 * d * triSQ d := by
    have hd' : 1 ≤ d := hd
    nlinarith
  by_contra! h
  unfold triJaQ at h
  have hclog : Nat.clog 2 (9 * d * triSQ d) ≤ 5 := Nat.le_of_lt_succ h
  have hle := (Nat.clog_le_iff_le_pow h2pos).mp hclog
  have h32 : (2 : ℕ) ^ 5 = 32 := by norm_num
  rw [h32] at hle
  omega

theorem pow_triLa_le {d : ℕ} (hd : 1 ≤ d) : 2 ^ triLa (triSQ d) ≤ 2 ^ 32 * d ^ 4 := by
  set s := triSQ d with hs
  have hbounds := triSQ_bounds d
  rcases hbounds with ⟨hs4, hs_upper⟩
  -- hs4 : 4 ≤ s, hs_upper : s ≤ 7 * (d + 10)
  by_cases hs4eq : s = 4
  · -- case s = 4
    rw [hs4eq]
    have h_triLa4 : triLa 4 = 11 := by
      norm_num [triLa]
    rw [h_triLa4]
    have h_pow : 2^11 ≤ 2^32 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h_dpow : 1 ≤ d^4 := by
      have hdpos : 0 < d := by omega
      exact Nat.one_le_pow 4 d hdpos
    nlinarith
  · -- case s ≠ 4, so s ≥ 5
    have hs5 : 5 ≤ s := by omega
    have hs1_lt_s : s - 1 < s := by omega
    have hs1_ge_4 : 4 ≤ s - 1 := by omega
    -- From Nat.find_min at s-1
    have hfind_min := Nat.find_min (pg_par_exists d) hs1_lt_s
    have h_not_prop : ¬ (2086812 * d ^ 2 * ((50 * (s - 1) ^ 2 + 68) / 69) ≤ 125 * (2 ^ (5 * (s - 1) ^ 2 / 7) - 1) ^ 2) := by
      intro hprop
      apply hfind_min
      exact ⟨hs1_ge_4, hprop⟩
    have h_lt : 125 * (2 ^ (5 * (s - 1) ^ 2 / 7) - 1) ^ 2 < 2086812 * d ^ 2 * ((50 * (s - 1) ^ 2 + 68) / 69) := by
      omega
    set X := 2 ^ (5 * (s - 1) ^ 2 / 7) with hX
    have h_lt' : 125 * (X - 1) ^ 2 < 2086812 * d ^ 2 * ((50 * (s - 1) ^ 2 + 68) / 69) := by
      simpa [hX] using h_lt
    -- Prove (50*(s-1)^2 + 68)/69 ≤ s^2
    have h_div_le : (50 * (s - 1) ^ 2 + 68) / 69 ≤ s ^ 2 := by
      have hineq' : 50 * (s - 1) ^ 2 + 68 ≤ 69 * s ^ 2 := by
        nlinarith
      calc
        (50 * (s - 1) ^ 2 + 68) / 69 ≤ (69 * s ^ 2) / 69 := Nat.div_le_div_right hineq'
        _ = s ^ 2 := by rw [Nat.mul_div_cancel_left _ (by norm_num : 0 < 69)]
    -- Now combine: 125*(X-1)^2 < 2086812 * d^2 * s^2
    have h_lt'' : 125 * (X - 1) ^ 2 < 2086812 * d ^ 2 * (s ^ 2) := by
      apply lt_of_lt_of_le h_lt' ?_
      apply Nat.mul_le_mul_left (2086812 * d ^ 2)
      exact h_div_le
    -- We have 2086812 < 125 * 16900 = 2112500
    -- So 125*(X-1)^2 < 125*16900*d^2*s^2
    have h_lt_cancel : (X - 1) ^ 2 < 16900 * d ^ 2 * (s ^ 2) := by
      have h1 : 2086812 * d ^ 2 * (s ^ 2) ≤ (125 * 16900) * d ^ 2 * (s ^ 2) := by
        have hcoeff : 2086812 ≤ 125 * 16900 := by norm_num
        nlinarith
      have h2 : 125 * (X - 1) ^ 2 < (125 * 16900) * d ^ 2 * (s ^ 2) :=
        lt_of_lt_of_le h_lt'' h1
      -- Rewrite RHS: (125 * 16900) * d^2 * s^2 = 125 * (16900 * d^2 * s^2)
      have h2' : 125 * (X - 1) ^ 2 < 125 * (16900 * d ^ 2 * s ^ 2) := by
        calc
          125 * (X - 1) ^ 2 < (125 * 16900) * d ^ 2 * (s ^ 2) := h2
          _ = 125 * (16900 * d ^ 2 * s ^ 2) := by ring
      exact Nat.lt_of_mul_lt_mul_left h2'
    -- Now (X-1)^2 < 16900*d^2*s^2 = (130*d*s)^2
    have h_sq_eq : 16900 * d ^ 2 * (s ^ 2) = (130 * d * s) ^ 2 := by
      ring
    rw [h_sq_eq] at h_lt_cancel
    -- Using Nat.pow_lt_pow_iff_left with n=2 (nonzero)
    have h_two_ne_zero : 2 ≠ 0 := by norm_num
    have h_lt_base : X - 1 < 130 * d * s :=
      ((Nat.pow_lt_pow_iff_left h_two_ne_zero).mp h_lt_cancel)
    -- So X ≤ 130*d*s
    have hX_le : X ≤ 130 * d * s := by omega
    -- Now bound s: s ≤ 7*(d+10) ≤ 7*11*d = 77*d for d ≥ 1
    have hs_le_77d : s ≤ 77 * d := by
      have hd' : d + 10 ≤ 11 * d := by
        omega
      calc
        s ≤ 7 * (d + 10) := hs_upper
        _ ≤ 7 * (11 * d) := Nat.mul_le_mul_left 7 hd'
        _ = 77 * d := by ring
    -- So X ≤ 130 * 77 * d^2 = 10010 * d^2
    have hX_le' : X ≤ 10010 * d ^ 2 := by
      calc
        X ≤ 130 * d * s := hX_le
        _ ≤ 130 * d * (77 * d) := Nat.mul_le_mul_left (130 * d) hs_le_77d
        _ = 10010 * d ^ 2 := by ring
    -- And 10010 < 16384 = 2^14
    have hX_lt : X < 2^14 * d ^ 2 := by
      have h_coeff : 10010 < 2^14 := by norm_num
      calc
        X ≤ 10010 * d ^ 2 := hX_le'
        _ < 2^14 * d ^ 2 := Nat.mul_lt_mul_of_pos_right h_coeff (by
          have hdpos : 0 < d := by omega
          exact pow_pos hdpos 2)
    -- Now we need: triLa s ≤ 2*(5*(s-1)^2/7) + 4
    -- First, prove 5*s^2 ≤ 10*(s-1)^2 + 16
    have h_ineq1 : 5 * s ^ 2 ≤ 10 * (s - 1) ^ 2 + 16 := by
      have hs1 : 1 ≤ s := by omega
      zify [hs1]
      nlinarith
    -- So triLa s = 5*s^2/7 ≤ (10*(s-1)^2 + 16)/7
    have h_triLa_le : triLa s ≤ (10 * (s - 1) ^ 2 + 16) / 7 := by
      rw [triLa]
      exact Nat.div_le_div_right h_ineq1
    -- Now prove (10*(s-1)^2 + 16)/7 ≤ 2*(5*(s-1)^2/7) + 4
    have h_div_bound : (10 * (s - 1) ^ 2 + 16) / 7 ≤ 2 * (5 * (s - 1) ^ 2 / 7) + 4 := by
      set q := 10 * (s - 1) ^ 2 / 7 with hq
      set r := 10 * (s - 1) ^ 2 % 7 with hr
      have hdiv_eq : 10 * (s - 1) ^ 2 = 7 * q + r := by
        rw [hq, hr]
        exact (Nat.div_add_mod _ _).symm
      have hr_lt_7 : r < 7 := Nat.mod_lt _ (by norm_num : 0 < 7)
      have hr_le_6 : r ≤ 6 := by omega
      -- (10*(s-1)^2 + 16)/7 = q + (r+16)/7
      have h_div_eq : (10 * (s - 1) ^ 2 + 16) / 7 = q + (r + 16) / 7 := by
        rw [hdiv_eq]
        calc
          (7 * q + r + 16) / 7 = (7 * q + (r + 16)) / 7 := by ring
          _ = (r + 16 + q * 7) / 7 := by ring
          _ = (r + 16) / 7 + q := by rw [Nat.add_mul_div_right (r + 16) q (by norm_num : 0 < 7)]
          _ = q + (r + 16) / 7 := by ring
      -- (r+16)/7 ≤ 3 because r+16 ≤ 22 < 28
      have h_r16_div_7 : (r + 16) / 7 ≤ 3 := by
        have h_r16_le_22 : r + 16 ≤ 22 := by omega
        have h22_div_7 : 22 / 7 ≤ 3 := by norm_num
        exact le_trans (Nat.div_le_div_right h_r16_le_22) h22_div_7
      -- So (10*(s-1)^2 + 16)/7 ≤ q + 3 = 10*(s-1)^2/7 + 3
      have h_bound1 : (10 * (s - 1) ^ 2 + 16) / 7 ≤ 10 * (s - 1) ^ 2 / 7 + 3 := by
        rw [← hq, h_div_eq]
        omega
      -- Now we need 10*(s-1)^2/7 + 3 ≤ 2*(5*(s-1)^2/7) + 4
      -- i.e., 10*(s-1)^2/7 ≤ 2*(5*(s-1)^2/7) + 1
      -- Let q' = 5*(s-1)^2/7, r' = 5*(s-1)^2 % 7
      set q' := 5 * (s - 1) ^ 2 / 7 with hq'
      set r' := 5 * (s - 1) ^ 2 % 7 with hr'
      have hdiv_eq' : 5 * (s - 1) ^ 2 = 7 * q' + r' := by
        rw [hq', hr']
        exact (Nat.div_add_mod _ _).symm
      have hr'_lt_7 : r' < 7 := Nat.mod_lt _ (by norm_num : 0 < 7)
      have hr'_le_6 : r' ≤ 6 := by omega
      -- 10*(s-1)^2/7 = (14q' + 2r')/7 = 2q' + (2r')/7
      have h_10div_eq : 10 * (s - 1) ^ 2 / 7 = 2 * q' + (2 * r') / 7 := by
        calc
          10 * (s - 1) ^ 2 / 7 = (2 * (5 * (s - 1) ^ 2)) / 7 := by ring
          _ = (2 * (7 * q' + r')) / 7 := by rw [hdiv_eq']
          _ = (14 * q' + 2 * r') / 7 := by ring
          _ = (7 * (2 * q') + 2 * r') / 7 := by ring
          _ = (2 * r' + 7 * (2 * q')) / 7 := by ring
          _ = (2 * r' + (2 * q') * 7) / 7 := by ring
          _ = 2 * r' / 7 + 2 * q' := by rw [Nat.add_mul_div_right (2 * r') (2 * q') (by norm_num : 0 < 7)]
          _ = 2 * q' + (2 * r') / 7 := by ring
      -- (2*r')/7 ≤ 1 because r' ≤ 6, so 2*r' ≤ 12 < 14
      have h_2r_div_7 : (2 * r') / 7 ≤ 1 := by
        have h2r_le_12 : 2 * r' ≤ 12 := by omega
        have h12_div_7 : 12 / 7 ≤ 1 := by norm_num
        exact le_trans (Nat.div_le_div_right h2r_le_12) h12_div_7
      -- So 10*(s-1)^2/7 ≤ 2q' + 1 = 2*(5*(s-1)^2/7) + 1
      have h_bound2 : 10 * (s - 1) ^ 2 / 7 ≤ 2 * (5 * (s - 1) ^ 2 / 7) + 1 := by
        rw [← hq', h_10div_eq]
        omega
      -- Combine: (10*(s-1)^2 + 16)/7 ≤ 10*(s-1)^2/7 + 3 ≤ 2*(5*(s-1)^2/7) + 1 + 3 = 2*(5*(s-1)^2/7) + 4
      omega
    -- Combine: triLa s ≤ 2*(5*(s-1)^2/7) + 4
    have h_triLa_le2 : triLa s ≤ 2 * (5 * (s - 1) ^ 2 / 7) + 4 :=
      le_trans h_triLa_le h_div_bound
    -- Now 2^(triLa s) ≤ 2^(2*(5*(s-1)^2/7) + 4) = 16 * X^2
    have h_pow_triLa : 2 ^ triLa s ≤ 16 * X ^ 2 := by
      have h_exp : 2 ^ triLa s ≤ 2 ^ (2 * (5 * (s - 1) ^ 2 / 7) + 4) :=
        Nat.pow_le_pow_right (by norm_num) h_triLa_le2
      have h_rhs : 2 ^ (2 * (5 * (s - 1) ^ 2 / 7) + 4) = 16 * X ^ 2 := by
        set A := 5 * (s - 1) ^ 2 / 7
        have hX' : X = 2 ^ A := hX
        calc
          2 ^ (2 * A + 4) = 2 ^ (2 * A) * 2 ^ 4 := by rw [Nat.pow_add]
          _ = 2 ^ (2 * A) * 16 := by norm_num
          _ = 2 ^ (A * 2) * 16 := by rw [mul_comm A 2]
          _ = (2 ^ A) ^ 2 * 16 := by rw [Nat.pow_mul]
          _ = X ^ 2 * 16 := by rw [hX']
          _ = 16 * X ^ 2 := by ring
      rw [h_rhs] at h_exp
      exact h_exp
    -- Now X < 2^14 * d^2, so X^2 < 2^28 * d^4
    have h_Xsq_lt : X ^ 2 < 2^28 * d ^ 4 := by
      have h_sq_lt : X ^ 2 < (2^14 * d ^ 2) ^ 2 :=
        Nat.pow_lt_pow_left hX_lt (by norm_num : 2 ≠ 0)
      have h_eq : (2^14 * d ^ 2) ^ 2 = 2^28 * d ^ 4 := by
        ring
      rw [h_eq] at h_sq_lt
      exact h_sq_lt
    -- So 16*X^2 < 16*2^28*d^4 = 2^32*d^4
    have h_final : 16 * X ^ 2 < 2^32 * d ^ 4 := by
      have h_lt' : 16 * X ^ 2 < 16 * (2^28 * d ^ 4) :=
        Nat.mul_lt_mul_of_pos_left h_Xsq_lt (by norm_num : 0 < 16)
      have h_eq : 16 * (2^28 * d ^ 4) = 2^32 * d ^ 4 := by
        ring
      rw [h_eq] at h_lt'
      exact h_lt'
    -- Combine: 2^(triLa s) ≤ 16*X^2 < 2^32*d^4
    exact le_trans h_pow_triLa (le_of_lt h_final)

-- Helper lemma: the inequality part of pg_par_exists for s = 7*(d+10)
theorem pg_par_exists_7dp10 (d : ℕ) : 2086812 * d ^ 2 * ((50 * (7*(d+10)) ^ 2 + 68) / 69) ≤ 125 * (2 ^ (5 * (7*(d+10)) ^ 2 / 7) - 1) ^ 2 := by
  set x := d + 10 with hx
  have hx1 : 10 ≤ x := by omega
  have h57 : 5 * (7 * x) ^ 2 / 7 = 35 * x ^ 2 := by
    rw [show 5 * (7 * x) ^ 2 = 7 * (35 * x ^ 2) by ring, Nat.mul_div_cancel_left _ (by norm_num)]
  rw [h57]
  have hdiv : (50 * (7 * x) ^ 2 + 68) / 69 ≤ 2518 * x ^ 2 := by
    calc (50 * (7 * x) ^ 2 + 68) / 69 ≤ 50 * (7 * x) ^ 2 + 68 := Nat.div_le_self _ _
      _ ≤ 2518 * x ^ 2 := by nlinarith
  have hdx : d ^ 2 ≤ x ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hL : 2086812 * d ^ 2 * ((50 * (7 * x) ^ 2 + 68) / 69) ≤ 2 ^ 33 * x ^ 4 := by
    calc 2086812 * d ^ 2 * ((50 * (7 * x) ^ 2 + 68) / 69) ≤ 2086812 * x ^ 2 * (2518 * x ^ 2) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ hdx) hdiv
      _ = 5254592616 * x ^ 4 := by ring
      _ ≤ 2 ^ 33 * x ^ 4 := Nat.mul_le_mul_right _ (by norm_num)
  have hx4 : x ^ 4 ≤ 2 ^ (4 * x) := by
    rw [mul_comm, pow_mul]
    exact Nat.pow_le_pow_left (Nat.lt_two_pow_self).le 4
  have hk : 33 + 4 * x ≤ 35 * x ^ 2 := by nlinarith
  have hK : 4 ≤ 2 ^ (35 * x ^ 2) := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (35 * x ^ 2) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  have hR : 2 ^ (35 * x ^ 2) ≤ 125 * (2 ^ (35 * x ^ 2) - 1) ^ 2 := by
    obtain ⟨j, hj⟩ : ∃ j, 2 ^ (35 * x ^ 2) = j + 1 := ⟨2 ^ (35 * x ^ 2) - 1, by omega⟩
    rw [hj, Nat.add_sub_cancel]
    have hj3 : 3 ≤ j := by omega
    nlinarith
  calc 2086812 * d ^ 2 * ((50 * (7 * x) ^ 2 + 68) / 69) ≤ 2 ^ 33 * x ^ 4 := hL
    _ ≤ 2 ^ 33 * 2 ^ (4 * x) := Nat.mul_le_mul_left _ hx4
    _ = 2 ^ (33 + 4 * x) := (pow_add _ _ _).symm
    _ ≤ 2 ^ (35 * x ^ 2) := Nat.pow_le_pow_right (by norm_num) hk
    _ ≤ 125 * (2 ^ (35 * x ^ 2) - 1) ^ 2 := hR

-- Helper lemma: triLh s ≤ 3 * triLa (s-1) for s ≥ 5
theorem triLh_le_three_triLa_pred (s : ℕ) (hs : 5 ≤ s) : triLh s ≤ 3 * triLa (s - 1) := by
  unfold triLh triLa
  have hpos69 : 0 < 69 := by norm_num
  have hpos7 : 0 < 7 := by norm_num

  set q1 := (50*s^2 + 68)/69 with hq1
  set r1 := (50*s^2 + 68)%69 with hr1
  set q2 := 5*(s-1)^2/7 with hq2
  set r2 := 5*(s-1)^2%7 with hr2

  have hA : 50*s^2 + 68 = 69*q1 + r1 :=
    (Nat.div_add_mod (50*s^2 + 68) 69).symm
  have hC : 5*(s-1)^2 = 7*q2 + r2 :=
    (Nat.div_add_mod (5*(s-1)^2) 7).symm
  have hr1_lt : r1 < 69 := Nat.mod_lt _ hpos69
  have hr2_lt : r2 < 7 := Nat.mod_lt _ hpos7

  -- Key polynomial inequality: 7*(50*s^2+68) + 1242 ≤ 207*(5*(s-1)^2)
  have h_ineq : 7*(50*s^2 + 68) + 1242 ≤ 207*(5*(s-1)^2) := by
    -- Convert to ℤ for nlinarith, then cast back
    have hs1 : 1 ≤ s := by omega
    have h_ineq_ℤ : (7 : ℤ)*(50*(s:ℤ)^2 + 68) + 1242 ≤ (207 : ℤ)*(5*((s:ℤ)-1)^2) := by
      nlinarith
    apply (Nat.cast_le (α := ℤ)).mp
    simpa [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_sub hs1, Nat.cast_ofNat] using h_ineq_ℤ

  -- Substitute hA and hC
  have h_ineq' : 7*(69*q1 + r1) + 1242 ≤ 207*(7*q2 + r2) := by
    simpa [hA, hC] using h_ineq
  ring_nf at h_ineq'
  -- h_ineq': 1242 + 483*q1 + 7*r1 ≤ 1449*q2 + 207*r2  (or similar)

  -- Since r2 < 7, we have 207*r2 ≤ 1242
  have h_r2_le : 207*r2 ≤ 1242 := by
    have hr2_le6 : r2 ≤ 6 := by omega
    nlinarith

  -- From h_ineq', we get the main inequality
  have h_main : 483*q1 ≤ 1449*q2 := by
    -- h_ineq' gives an inequality between the expanded forms
    -- Rearranged: 483*q1 + 7*r1 + 1242 ≤ 1449*q2 + 207*r2
    -- Since 207*r2 ≤ 1242 and 7*r1 ≥ 0, we get 483*q1 ≤ 1449*q2
    omega

  -- 483*q1 ≤ 1449*q2 implies q1 ≤ 3*q2
  nlinarith

theorem pow_triLh_le {d : ℕ} (hd : 1 ≤ d) : 2 ^ triLh (triSQ d) ≤ 2 ^ 42 * d ^ 6 := by
  set s := triSQ d with hs
  have hspec := Nat.find_spec (pg_par_exists d)
  rcases hspec with ⟨hs4, hspec_ineq⟩
  -- hspec_ineq : 2086812 * d ^ 2 * triLh s ≤ 125 * (2 ^ triLa s - 1) ^ 2

  by_cases hs5 : s < 5
  · -- s < 5 and s ≥ 4, so s = 4
    have hs_eq4 : s = 4 := Nat.le_antisymm (by omega) hs4
    rw [hs_eq4]
    have h_triLh4 : triLh 4 = 12 := by
      unfold triLh; norm_num
    rw [h_triLh4]
    have h_pow : 2^12 ≤ 2^42 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h_d6 : 1 ≤ d^6 := by
      have hpos : 0 < d := by omega
      have := pow_pos hpos 6
      omega
    calc
      2^12 ≤ 2^42 := h_pow
      _ = 2^42 * 1 := by ring
      _ ≤ 2^42 * d^6 := Nat.mul_le_mul_left _ h_d6
  · -- s ≥ 5
    have hs5' : 5 ≤ s := by omega

    -- From Nat.find_le, s ≤ 7*(d+10) ≤ 77*d for d ≥ 1
    have hs_le_77d : s ≤ 77 * d := by
      have h_find_le : s ≤ 7*(d+10) :=
        Nat.find_le (h := pg_par_exists d) ⟨by omega, pg_par_exists_7dp10 d⟩
      -- 7*(d+10) ≤ 77*d for d ≥ 1
      have h_7dp10_le_77d : 7*(d+10) ≤ 77*d := by
        nlinarith
      exact le_trans h_find_le h_7dp10_le_77d

    -- Now the main argument
    have hs1_lt_s : s - 1 < s := by omega
    have hs1_ge4 : 4 ≤ s - 1 := by omega

    have hmin := Nat.find_min (pg_par_exists d) hs1_lt_s
    have hmin' : ¬ (2086812 * d^2 * triLh (s-1) ≤ 125 * (2^triLa (s-1) - 1)^2) := by
      intro h
      apply hmin
      exact ⟨hs1_ge4, h⟩

    have h_lt : 125 * (2^triLa (s-1) - 1)^2 < 2086812 * d^2 * triLh (s-1) := by omega

    set X := 2^triLa (s-1) with hX

    -- Bound triLh (s-1) ≤ s^2
    have h_triLh_bound : triLh (s-1) ≤ s^2 := by
      unfold triLh
      have hpos69 : 0 < 69 := by norm_num
      have h_ineq : 50*(s-1)^2 + 68 < 69*(s^2 + 1) := by
        nlinarith
      have h_div_lt : (50*(s-1)^2 + 68)/69 < s^2 + 1 :=
        (Nat.div_lt_iff_lt_mul hpos69).mpr (by
          -- goal: 50*(s-1)^2 + 68 < (s^2+1)*69
          -- h_ineq: 50*(s-1)^2 + 68 < 69*(s^2+1)
          rw [mul_comm (s^2+1) 69]
          exact h_ineq)
      omega

    -- From h_lt: 125*(X-1)^2 < 2086812*d^2*triLh(s-1) ≤ 2086812*d^2*s^2
    have h_bound2 : 125 * (X - 1)^2 < 2086812 * d^2 * s^2 := by
      apply lt_of_lt_of_le h_lt
      apply Nat.mul_le_mul_left (2086812 * d^2)
      exact h_triLh_bound

    -- From h_bound2: X-1 < 130*d*s
    have hX_bound : X - 1 < 130 * d * s := by
      by_contra! h
      -- h: X-1 ≥ 130*d*s
      have h_sq_le : (130*d*s)^2 ≤ (X-1)^2 := Nat.pow_le_pow_left h 2
      have h_mul : 125 * (X-1)^2 ≥ 125 * (130*d*s)^2 := Nat.mul_le_mul_left 125 h_sq_le
      have h_130_sq : (130*d*s)^2 = 16900 * d^2 * s^2 := by ring
      rw [h_130_sq] at h_mul
      -- h_mul: 125*(X-1)^2 ≥ 125*16900*d^2*s^2
      have h_130_sq' : 125*16900 = 2112500 := by norm_num
      -- h_mul: 125*(X-1)^2 ≥ 125*(16900*d^2*s^2)
      -- Rewrite RHS: 125*(16900*d^2*s^2) = 2112500*d^2*s^2
      have h_mul' : 125 * (X-1)^2 ≥ 2112500 * d^2 * s^2 := by
        calc
          125 * (X-1)^2 ≥ 125 * (16900 * d^2 * s^2) := h_mul
          _ = (125*16900) * d^2 * s^2 := by ring
          _ = 2112500 * d^2 * s^2 := by norm_num
      have h_lt' : 2086812 * d^2 * s^2 < 2112500 * d^2 * s^2 := by
        have h_lt_d2 : 2086812 * d^2 < 2112500 * d^2 :=
          Nat.mul_lt_mul_of_pos_right (by norm_num) (pow_pos (by omega) 2)
        exact Nat.mul_lt_mul_of_pos_right h_lt_d2 (pow_pos (by omega) 2)
      -- Now: 125*(X-1)^2 < 2086812*d^2*s^2 < 2112500*d^2*s^2 ≤ 125*(X-1)^2
      have h_contra : 125 * (X-1)^2 < 125 * (X-1)^2 := by
        apply lt_trans h_bound2
        apply lt_of_lt_of_le h_lt' h_mul'
      exact lt_irrefl _ h_contra

    have hX_le_130ds : X ≤ 130 * d * s := by omega

    -- X ≤ 10010*d^2
    have hX_le_10010d2 : X ≤ 10010 * d^2 := by
      calc
        X ≤ 130 * d * s := hX_le_130ds
        _ ≤ 130 * d * (77 * d) := Nat.mul_le_mul_left (130*d) hs_le_77d
        _ = 10010 * d^2 := by ring

    -- X^3 ≤ 10010^3 * d^6
    have hX3_le_10010_3_d6 : X^3 ≤ 10010^3 * d^6 := by
      calc
        X^3 ≤ (10010 * d^2)^3 := Nat.pow_le_pow_left hX_le_10010d2 3
        _ = 10010^3 * (d^2)^3 := by ring
        _ = 10010^3 * d^6 := by ring

    -- 10010^3 ≤ 2^42
    have h_10010_3_le_2_42 : 10010^3 ≤ 2^42 := by norm_num

    -- X^3 ≤ 2^42 * d^6
    have hX3_le_2_42_d6 : X^3 ≤ 2^42 * d^6 :=
      le_trans hX3_le_10010_3_d6 (Nat.mul_le_mul h_10010_3_le_2_42 (le_refl _))

    -- triLh s ≤ 3 * triLa (s-1)
    have h_triLh_le : triLh s ≤ 3 * triLa (s - 1) :=
      triLh_le_three_triLa_pred s hs5'

    -- 2^triLh s ≤ X^3
    have h_pow_le : 2^triLh s ≤ X^3 := by
      calc
        2^triLh s ≤ 2^(3 * triLa (s - 1)) := Nat.pow_le_pow_right (by norm_num) h_triLh_le
        _ = (2^triLa (s - 1))^3 := by rw [← pow_mul, mul_comm, pow_mul]
        _ = X^3 := by rw [hX]

    -- Final result
    exact le_trans h_pow_le hX3_le_2_42_d6

theorem eloI_pos {d : ℕ} (hd : 1 ≤ d) : 0 < eloI d := by
  unfold eloI
  have hspec := Nat.find_spec (pg_par_exists d)
  have hsq : 4 ≤ triSQ d := hspec.1
  have htri_pos : 0 < triLh (triSQ d) := by
    unfold triLh
    have hsq' : 16 ≤ (triSQ d) ^ 2 := by
      nlinarith
    have hnum : 69 ≤ 50 * (triSQ d) ^ 2 + 68 := by
      nlinarith
    exact Nat.div_pos hnum (by norm_num)
  have htri : 1 ≤ triLh (triSQ d) := by omega
  have hpow : 1 ≤ 2 ^ triLh (triSQ d) := by
    calc
      1 = 2 ^ 0 := by norm_num
      _ ≤ 2 ^ triLh (triSQ d) := Nat.pow_le_pow_right (by norm_num) (Nat.zero_le _)
  have hsub : 0 < 2 ^ triLh (triSQ d) - 1 := by
    have : 2 ≤ 2 ^ triLh (triSQ d) := by
      calc
        2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ triLh (triSQ d) := Nat.pow_le_pow_right (by norm_num) htri
    omega
  positivity

theorem d2N_pos {d : ℕ} (hd : 1 ≤ d) : 0 < d2N d := by
  unfold d2N
  have hpos : 0 < 4 * d * rI d ^ 2 * 4 ^ triJaQ d := by
    have hdpos : 0 < d := by omega
    have hrIpos : 0 < rI d := by
      unfold rI
      exact pow_pos (by norm_num) _
    positivity
  rw [add_assoc]
  exact Nat.add_pos_left hpos _

theorem ceil_div_nat (N D : ℕ) (hD : 0 < D) : ⌈(N : ℚ) / D⌉₊ = (N + D - 1) / D := by
  set k := (N + D - 1) / D
  by_cases hN : N = 0
  · subst N
    have hk0 : k = 0 := by
      dsimp [k]
      simp [hD]
    simp [hk0]
  · have hNpos : 0 < N := Nat.pos_of_ne_zero hN
    have hk : k ≠ 0 := by
      intro hk0
      have hdiv0 : (N + D - 1) / D = 0 := hk0
      have hlt : N + D - 1 < D := (Nat.div_eq_zero_iff_lt hD).mp hdiv0
      have hge : D ≤ N + D - 1 := by omega
      omega
    rw [Nat.ceil_eq_iff hk]
    have hD_rat : (0 : ℚ) < D := by exact_mod_cast hD
    have h_divmod := Nat.div_add_mod (N + D - 1) D
    set r := (N + D - 1) % D
    have hr_lt : r < D := Nat.mod_lt _ hD
    have h_eq : D * k + r = N + D - 1 := by
      rw [← h_divmod, mul_comm]
    -- From h_eq: D*k + r = N + D - 1
    -- So N + D = D*k + r + 1 (since N + D ≥ 1)
    have h_sum : N + D = D * k + r + 1 := by
      have hpos : 1 ≤ N + D := by omega
      have h_sub : N + D - 1 + 1 = N + D := Nat.sub_add_cancel hpos
      calc
        N + D = (N + D - 1) + 1 := by rw [h_sub]
        _ = (D * k + r) + 1 := by rw [← h_eq]
        _ = D * k + r + 1 := by ring
    have h_mul : (k - 1) * D + D = k * D := by
      have hk' : 1 ≤ k := Nat.one_le_of_lt (Nat.pos_of_ne_zero hk)
      calc
        (k - 1) * D + D = (k - 1) * D + 1 * D := by simp
        _ = ((k - 1) + 1) * D := by rw [Nat.add_mul]
        _ = k * D := by rw [Nat.sub_add_cancel hk']
    constructor
    · -- ↑(k - 1) < (N : ℚ) / D
      have h_nat : (k - 1) * D < N := by
        have h_total : (k - 1) * D + D + r + 1 = N + D := by
          calc
            (k - 1) * D + D + r + 1 = k * D + r + 1 := by rw [h_mul]
            _ = D * k + r + 1 := by rw [mul_comm]
            _ = N + D := by rw [h_sum]
        -- So (k-1)*D + r + 1 = N
        have h_eq2 : (k - 1) * D + r + 1 = N := by
          omega
        omega
      -- Convert to ℚ: (k-1 : ℚ) < (N : ℚ) / (D : ℚ)
      rw [lt_div_iff₀ hD_rat]
      -- Goal: ↑(k - 1) * ↑D < ↑N
      -- h_nat: (k - 1) * D < N
      -- Using Nat.cast_lt and Nat.cast_mul
      have h_cast := (Nat.cast_lt (α := ℚ)).mpr h_nat
      -- h_cast: ↑((k - 1) * D) < ↑N
      simpa [Nat.cast_mul] using h_cast
    · -- (N : ℚ) / D ≤ ↑k
      have h_nat : N ≤ k * D := by
        -- From h_sum: N + D = D * k + r + 1
        -- Since r < D, r + 1 ≤ D
        -- So N + D = D * k + r + 1 ≤ D * k + D = D * (k + 1)
        have h_ineq : N + D ≤ D * (k + 1) := by
          rw [h_sum]
          rw [mul_add]
          -- Goal: D * k + r + 1 ≤ D * k + D * 1
          -- i.e., D * k + r + 1 ≤ D * k + D
          have : r + 1 ≤ D := by omega
          omega
        -- h_ineq: N + D ≤ D * (k + 1)
        rw [mul_add] at h_ineq
        simp at h_ineq
        -- h_ineq: N ≤ D * k
        rw [mul_comm D k] at h_ineq
        -- h_ineq: N ≤ k * D
        exact h_ineq
      -- Convert to ℚ: (N : ℚ) / (D : ℚ) ≤ (k : ℚ)
      rw [div_le_iff₀ hD_rat]
      -- Goal: ↑N ≤ ↑k * ↑D
      -- h_nat: N ≤ k * D
      have h_cast := (Nat.cast_le (α := ℚ)).mpr h_nat
      -- h_cast: ↑N ≤ ↑(k * D)
      simpa [Nat.cast_mul] using h_cast

theorem triEloQ_eq {d : ℕ} (hd : 1 ≤ d) : triEloQ d = 20000 / (eloI d : ℚ) := by
  have hd0 : (d : ℚ) ≠ 0 := by
    intro hzero
    have hd0' : d = 0 := by exact_mod_cast hzero
    omega
  have hLpos : 1 ≤ triLh (triSQ d) := by
    have h := Nat.find_spec (pg_par_exists d)
    have hsq : 4 ≤ triSQ d := h.1
    unfold triLh
    have hnum : 69 ≤ 50 * (triSQ d) ^ 2 + 68 := by nlinarith
    exact Nat.succ_le_of_lt (Nat.div_pos hnum (by norm_num))
  have hL0 : (triLh (triSQ d) : ℚ) ≠ 0 := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mp hLpos
  have hR0 : ((2 : ℚ) ^ triLh (triSQ d) - 1) ≠ 0 := by
    have h_gt : (1 : ℚ) < (2 : ℚ) ^ triLh (triSQ d) := by
      have h_nat : 1 < 2 ^ triLh (triSQ d) := Nat.one_lt_two_pow (by omega : triLh (triSQ d) ≠ 0)
      exact_mod_cast h_nat
    linarith
  unfold triEloQ eloI triRhQ
  push_cast
  field_simp [hd0, hL0, hR0]
  have hRpos' : 1 ≤ 2 ^ triLh (triSQ d) := Nat.one_le_two_pow (n := triLh (triSQ d))
  simp [Nat.cast_sub hRpos', Nat.cast_pow]
  ring

theorem triD2Q_eq {d : ℕ} (hd : 1 ≤ d) : triD2Q d = (d2N d : ℚ) / 4 ^ triJaQ d := by
  unfold triD2Q triRQ triBQ triAQ d2N rI bI
  have hSQ : 4 ≤ triSQ d := (Nat.find_spec (pg_par_exists d)).1
  have hBpos : 1 ≤ 161 * 2 ^ (triLa (triSQ d) - 10) * 2 ^ triJaQ d := by
    have h1 : 1 ≤ (161 : ℕ) := by norm_num
    have h2 : 1 ≤ 2 ^ (triLa (triSQ d) - 10) := Nat.one_le_two_pow
    have h3 : 1 ≤ 2 ^ triJaQ d := Nat.one_le_two_pow
    nlinarith
  simp [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_sub hd, Nat.cast_sub hBpos, Nat.cast_one]
  field_simp [show (4 : ℚ) ^ triJaQ d ≠ 0 from by positivity]
  have h4 : (2 : ℚ) ^ triJaQ d * (2 : ℚ) ^ triJaQ d = (4 : ℚ) ^ triJaQ d := by
    calc
      (2 : ℚ) ^ triJaQ d * (2 : ℚ) ^ triJaQ d = ((2 : ℚ) * (2 : ℚ)) ^ triJaQ d := by rw [mul_pow]
      _ = (4 : ℚ) ^ triJaQ d := by norm_num
  simp [pow_two, h4]
  ring

theorem triKgQ_eq {d : ℕ} (hd : 1 ≤ d) : triKgQ d = max 2 (Nat.clog 2 ((kgN d + 19999) / 20000)) := by
  unfold triKgQ
  have h20000 : 0 < 20000 := by norm_num
  have h_expr : (16 : ℚ) * triBQ d * ((d : ℚ) + 1) * (d : ℚ) * (8 * (d : ℚ) + 2) / triEloQ d = (kgN d : ℚ) / (20000 : ℚ) := by
    rw [triEloQ_eq hd]
    have htriBQ_eq' : triBQ d = (bI d : ℚ) := by
      unfold triBQ bI
      simp
    rw [htriBQ_eq']
    unfold kgN bI
    have helo_pos : (eloI d : ℚ) ≠ 0 := by
      exact mod_cast (eloI_pos hd).ne.symm
    field_simp [helo_pos]
    have hcalc : (16 : ℕ) * (161 * 2 ^ (triLa (triSQ d) - 10)) * d * (d + 1) * (d * 8 + 2) * eloI d = (16 : ℕ) * (161 * 2 ^ (triLa (triSQ d) - 10)) * (d + 1) * d * (8 * d + 2) * eloI d := by
      ring
    exact_mod_cast hcalc
  have hceil : ⌈(16 : ℚ) * triBQ d * ((d : ℚ) + 1) * (d : ℚ) * (8 * (d : ℚ) + 2) / triEloQ d⌉₊ = (kgN d + 19999) / 20000 := by
    rw [h_expr]
    simpa using ceil_div_nat (kgN d) 20000 h20000
  rw [hceil]

theorem triBvQ_eq {d : ℕ} (hd : 1 ≤ d) : triBvQ d = Nat.clog 4 ((bvN d + bvD d - 1) / bvD d) := by
  unfold triBvQ
  have h_eq : (64 * (d + 1) ^ 2 * triD2Q d / triEloQ d ^ 2 : ℚ) = (bvN d : ℚ) / bvD d := by
    rw [triD2Q_eq hd, triEloQ_eq hd]
    unfold bvN bvD
    field_simp
    push_cast
    ring
  have h_pos : 0 < bvD d := by
    unfold bvD
    positivity
  rw [h_eq]
  rw [ceil_div_nat (bvN d) (bvD d) h_pos]

theorem triGuQ_eq {d : ℕ} (hd : 1 ≤ d) : triGuQ d = (guN d : ℚ) := by
  unfold triGuQ guN
  push_cast
  have hj := triJaQ_ge hd
  have h3 : 3 ≤ triJaQ d := by omega
  have h_eq : (2 : ℚ) ^ triJaQ d = (2 : ℚ) ^ (triJaQ d - 3) * (2 : ℚ) ^ 3 := by
    calc
      (2 : ℚ) ^ triJaQ d = (2 : ℚ) ^ ((triJaQ d - 3) + 3) := by rw [Nat.sub_add_cancel h3]
      _ = (2 : ℚ) ^ (triJaQ d - 3) * (2 : ℚ) ^ 3 := by rw [pow_add]
  have h8 : (2 : ℚ) ^ 3 = (8 : ℚ) := by norm_num
  rw [h_eq, h8]
  ring

theorem triNeQ_eq {d : ℕ} (hd : 1 ≤ d) (ℓ : ℕ) : triNeQ d ℓ = Nat.clog 2 ((neN d ℓ + neD d - 1) / neD d) := by
  have ceil_eq_ceilDiv (N D : ℕ) : ⌈(N : ℚ) / (D : ℚ)⌉₊ = N ⌈/⌉ D := by
    by_cases hD : D = 0
    · subst hD; simp
    · have hDpos : 0 < D := Nat.pos_of_ne_zero hD
      apply le_antisymm
      · rw [Nat.ceil_le]
        have h := le_smul_ceilDiv hDpos (b := N)
        have h' : (N : ℚ) ≤ ((N ⌈/⌉ D : ℕ) : ℚ) * (D : ℚ) := by
          simpa [smul_eq_mul, mul_comm] using mod_cast h
        rw [div_le_iff₀ (by exact mod_cast hDpos)]
        simpa [mul_comm] using h'
      · rw [ceilDiv_le_iff_le_smul hDpos]
        have hceil := Nat.le_ceil ((N : ℚ) / (D : ℚ))
        have hmul : (N : ℚ) ≤ (D : ℚ) * (⌈(N : ℚ) / (D : ℚ)⌉₊ : ℚ) := by
          calc
            (N : ℚ) = (N : ℚ) / (D : ℚ) * (D : ℚ) := by field_simp [show (D : ℚ) ≠ 0 from by exact_mod_cast hDpos.ne.symm]
            _ ≤ (⌈(N : ℚ) / (D : ℚ)⌉₊ : ℚ) * (D : ℚ) := by nlinarith
            _ = (D : ℚ) * (⌈(N : ℚ) / (D : ℚ)⌉₊ : ℚ) := by ring
        exact_mod_cast hmul
  have h_arg_eq : (16 * triD2Q d * (2 * (3 / 2 * (triGuQ d + triBuQ d)) ^ 2 + 4 * triGuQ d ^ 2 * ℓ) / (9 * triEloQ d ^ 2) : ℚ) = (neN d ℓ : ℚ) / (neD d : ℚ) := by
    rw [triD2Q_eq hd, triEloQ_eq hd, triGuQ_eq hd]
    unfold triBuQ neN neD gbN
    set d2N := d2N d with hd2N
    set eloI := eloI d with heloI
    set G := guN d with hG
    set V := triBvQ d with hV
    set J := triJaQ d with hJ
    push_cast
    field_simp [show (4 : ℚ) ^ J ≠ 0 from by positivity, show (2 : ℚ) ^ V ≠ 0 from by positivity,
      show (20000 : ℚ) ≠ 0 from by norm_num, show (9 : ℚ) ≠ 0 from by norm_num,
      show (400000000 : ℚ) ≠ 0 from by norm_num]
    have h_pow1 : (4 : ℚ) ^ (V + J) = (4 : ℚ) ^ V * (4 : ℚ) ^ J := by rw [pow_add]
    have h_pow2 : ((2 : ℚ) ^ V) ^ 2 = (4 : ℚ) ^ V := by
      calc
        ((2 : ℚ) ^ V) ^ 2 = (2 : ℚ) ^ (V * 2) := by rw [pow_mul]
        _ = ((2 : ℚ) ^ 2) ^ V := by rw [mul_comm, pow_mul]
        _ = (4 : ℚ) ^ V := by norm_num
    rw [h_pow1, h_pow2]
    ring
  calc
    triNeQ d ℓ = Nat.clog 2 ⌈16 * triD2Q d * (2 * (3 / 2 * (triGuQ d + triBuQ d)) ^ 2 + 4 * triGuQ d ^ 2 * ℓ) / (9 * triEloQ d ^ 2)⌉₊ := rfl
    _ = Nat.clog 2 (⌈(neN d ℓ : ℚ) / (neD d : ℚ)⌉₊) := by rw [h_arg_eq]
    _ = Nat.clog 2 ((neN d ℓ : ℕ) ⌈/⌉ (neD d : ℕ)) := by rw [ceil_eq_ceilDiv]
    _ = Nat.clog 2 ((neN d ℓ + neD d - 1) / neD d) := by rw [Nat.ceilDiv_eq_add_pred_div]

theorem triJsQ_eq {d : ℕ} (hd : 1 ≤ d) (ℓ : ℕ) : triJsQ d ℓ = Nat.clog 4 ((jsN d ℓ + jsD d - 1) / jsD d) := by
  have hd2N_pos : 0 < d2N d := d2N_pos hd
  have hjsD_pos : 0 < jsD d := by
    dsimp [jsD]
    exact mul_pos (pow_pos (by norm_num) _) hd2N_pos
  have h_gbN : (gbN d : ℚ) = (guN d : ℚ) * (2 ^ triBvQ d : ℚ) + (d : ℚ) + 1 := by
    simp [gbN]
  have h_bu : (triBuQ d : ℚ) = ((d : ℚ) + 1) / (2 ^ triBvQ d : ℚ) := by
    simp [triBuQ]
  have h_sum : (triGuQ d + triBuQ d : ℚ) = (gbN d : ℚ) / (2 ^ triBvQ d : ℚ) := by
    rw [triGuQ_eq hd, h_bu]
    field_simp [show (2 ^ triBvQ d : ℚ) ≠ 0 from by norm_num]
    rw [h_gbN]
    ring
  have h_pow_sq : ((2 : ℚ) ^ triBvQ d) ^ 2 = (4 : ℚ) ^ triBvQ d := by
    calc
      ((2 : ℚ) ^ triBvQ d) ^ 2 = (2 : ℚ) ^ (triBvQ d * 2) := by rw [pow_mul]
      _ = (2 : ℚ) ^ (2 * triBvQ d) := by rw [mul_comm]
      _ = ((2 : ℚ) ^ 2) ^ triBvQ d := by rw [← pow_mul]
      _ = (4 : ℚ) ^ triBvQ d := by norm_num
  have h_expr_eq : (triGuQ d + triBuQ d) ^ 2 * (2 ^ triNeQ d ℓ : ℚ) / triD2Q d = (jsN d ℓ : ℚ) / (jsD d : ℚ) := by
    rw [h_sum, triD2Q_eq hd]
    dsimp [jsN, jsD]
    have hV : (2 : ℚ) ^ triBvQ d ≠ 0 := pow_ne_zero _ (by norm_num)
    have hD : (d2N d : ℚ) ≠ 0 := by exact_mod_cast hd2N_pos.ne.symm
    have hJ : (4 : ℚ) ^ triJaQ d ≠ 0 := pow_ne_zero _ (by norm_num)
    field_simp [hV, hD, hJ]
    rw [h_pow_sq]
    push_cast
    ring
  dsimp [triJsQ]
  rw [h_expr_eq]
  rw [ceil_div_nat (jsN d ℓ) (jsD d) hjsD_pos]

theorem triUQ_smul_rows {d m : ℕ} (α : Fin m → Fin d → ℚ) (β : Fin m → ℚ) (c : Fin m → ℚ)
    (hc : ∀ k, 0 < c k) (z : Fin d → ℚ) :
    triUQ (fun k => c k • α k) (fun k => c k * β k) z = triUQ α β z := by
  unfold triUQ
  have hc0 : ∀ k, c k ≠ 0 := fun k => (hc k).ne.symm
  have h_triQQ_eq : ∀ k, triQQ (fun k => c k • α k) (fun k => c k * β k) k z = triQQ α β k z := by
    intro k
    unfold triQQ
    calc
      (c k • α k) ⬝ᵥ z / (c k * β k) = (c k • (α k ⬝ᵥ z)) / (c k * β k) := by rw [smul_dotProduct]
      _ = (c k * (α k ⬝ᵥ z)) / (c k * β k) := rfl
      _ = (α k ⬝ᵥ z) / (β k) := by rw [mul_div_mul_left (α k ⬝ᵥ z) (β k) (hc0 k)]
  have h_branch_eq : ∀ k, (c k * β k)⁻¹ • (c k • α k) = (β k)⁻¹ • α k := by
    intro k
    by_cases hβ : β k = 0
    · rw [hβ, mul_zero]; simp
    · calc
        (c k * β k)⁻¹ • (c k • α k) = ((c k * β k)⁻¹ * c k) • α k := by rw [smul_smul]
        _ = ((c k)⁻¹ * (β k)⁻¹ * c k) • α k := by rw [mul_inv]
        _ = ((β k)⁻¹ * (c k)⁻¹ * c k) • α k := by rw [mul_comm (c k)⁻¹ (β k)⁻¹]
        _ = ((β k)⁻¹ * ((c k)⁻¹ * c k)) • α k := by rw [mul_assoc]
        _ = ((β k)⁻¹ * 1) • α k := by rw [inv_mul_cancel₀ (hc0 k)]
        _ = (β k)⁻¹ • α k := by rw [mul_one]
  simp_rw [h_triQQ_eq, h_branch_eq]

theorem triUQ_smul_pt {d m : ℕ} (α : Fin m → Fin d → ℚ) (β : Fin m → ℚ) (t : ℚ) (ht : 0 < t)
    (z : Fin d → ℚ) : triUQ α β (t • z) = triUQ α β z := by
  unfold triUQ triQQ
  simp only [dotProduct_smul, smul_eq_mul, mul_div_assoc]
  refine Finset.sum_congr rfl (λ k _ => ?_)
  simp [mul_pos_iff_of_pos_left ht, mul_le_mul_iff_of_pos_left ht, mul_lt_mul_iff_of_pos_left ht]

theorem qn_spec (N B : ℤ) :
    0 < (qn N B).2 ∧ ((qn N B).1 : ℚ) / (qn N B).2 = (N : ℚ) / B ∧
      (B ≠ 0 → (qn N B).2 = |B| ∧ (qn N B).1 = Int.sign B * N) := by
  unfold qn
  split_ifs with hBpos hBneg
  · -- case 0 < B: (N, B)
    refine ⟨hBpos, ?_, ?_⟩
    · simp
    · intro hB0
      have habs : |B| = B := abs_of_nonneg (Int.le_of_lt hBpos)
      have hsign : Int.sign B = 1 := by simp [hBpos]
      simp [habs, hsign]
  · -- case B < 0: (-N, -B)
    have hpos_negB : 0 < -B := by linarith
    refine ⟨hpos_negB, ?_, ?_⟩
    · push_cast
      have hB0 : (B : ℚ) ≠ 0 := by exact_mod_cast hBneg.ne
      field_simp [hB0]
    · intro hB0
      have hnegB : -B = |B| := by rw [abs_of_neg hBneg]
      have hsign : Int.sign B = -1 := by simp [hBneg]
      simp [hnegB, hsign]
  · -- case B = 0: (0, 1)
    have hBeq0 : B = 0 := by omega
    refine ⟨by norm_num, ?_, ?_⟩
    · subst hBeq0; simp
    · intro hB0
      exact (hB0 hBeq0).elim

theorem scan_max {d : ℕ} (N B : ℕ → ℤ) (a : ℕ → Fin d → ℤ) (M : ℕ) :
    (scan N B a M = scan0 ∧ ∀ j < M, (N j : ℚ) / B j ≤ 0) ∨
    ∃ k < M, B k ≠ 0 ∧ 0 < (N k : ℚ) / B k ∧ (∀ j < M, (N j : ℚ) / B j ≤ (N k : ℚ) / B k) ∧
      (∀ j < k, (N j : ℚ) / B j < (N k : ℚ) / B k) ∧
      scan N B a M = ⟨(qn (N k) (B k)).1, (qn (N k) (B k)).2, Int.sign (B k) • a k, (qn (N k) (B k)).2⟩ := by
  induction' M with M ih
  · left; refine ⟨rfl, ?_⟩; intro j hj; exfalso; exact Nat.not_lt_zero _ hj
  · rcases ih with (⟨hst_eq, hle⟩ | ⟨k, hk, hBk_ne, hBk_pos, hle_all, hlt_before, hst_eq⟩)
    · -- Case: scan N B a M = scan0 and all q j ≤ 0 for j < M
      let q := qn (N M) (B M)
      have hq2_pos : 0 < q.2 := (qn_spec (N M) (B M)).1
      have hq_div : (q.1 : ℚ) / (q.2 : ℚ) = (N M : ℚ) / (B M : ℚ) := (qn_spec (N M) (B M)).2.1
      have h_scan_step : scan N B a (M + 1) = scanStep scan0 (N M) (B M) (a M) := by
        simp [scan, hst_eq]
      rw [h_scan_step]
      by_cases hq1_pos : (0 : ℤ) < q.1
      · -- condition true
        right
        have hM_lt_succ : M < M + 1 := by omega
        have h_cond : (0 : ℤ) * q.2 < q.1 * (1 : ℤ) := by
          simpa [zero_mul, mul_one] using hq1_pos
        have h_scan_eq : scanStep scan0 (N M) (B M) (a M) =
          ⟨q.1, q.2, Int.sign (B M) • a M, q.2⟩ := by
          unfold scanStep scan0; rw [ite_eq_left h_cond]
        rw [h_scan_eq]
        refine ⟨M, hM_lt_succ, ?_, ?_, ?_, ?_, rfl⟩
        · intro hBeq; unfold q at hq1_pos; simp [qn, hBeq] at hq1_pos
        · rw [← hq_div]
          have hpos_q : (0 : ℚ) < (q.1 : ℚ) := by exact_mod_cast hq1_pos
          have hpos_q2 : (0 : ℚ) < (q.2 : ℚ) := by exact_mod_cast hq2_pos
          exact div_pos hpos_q hpos_q2
        · intro j hj
          rcases em (j < M) with (hjM | hjM)
          · have hle_j := hle j hjM
            rw [← hq_div]
            have hpos_q : (0 : ℚ) < (q.1 : ℚ) := by exact_mod_cast hq1_pos
            have hpos_q2 : (0 : ℚ) < (q.2 : ℚ) := by exact_mod_cast hq2_pos
            have hpos_div : (0 : ℚ) < (q.1 : ℚ) / (q.2 : ℚ) := div_pos hpos_q hpos_q2
            linarith
          · exact le_of_eq (by rw [show j = M by omega])
        · intro j hj
          have hle_j := hle j hj
          rw [← hq_div]
          have hpos_q : (0 : ℚ) < (q.1 : ℚ) := by exact_mod_cast hq1_pos
          have hpos_q2 : (0 : ℚ) < (q.2 : ℚ) := by exact_mod_cast hq2_pos
          have hpos_div : (0 : ℚ) < (q.1 : ℚ) / (q.2 : ℚ) := div_pos hpos_q hpos_q2
          linarith
      · -- condition false
        left
        have hq1_not_pos : ¬ (0 : ℤ) < q.1 := hq1_pos
        have h_cond : ¬ ((0 : ℤ) * q.2 < q.1 * (1 : ℤ)) := by
          simpa [zero_mul, mul_one] using hq1_not_pos
        have h_scan_eq : scanStep scan0 (N M) (B M) (a M) = scan0 := by
          unfold scanStep scan0; rw [ite_eq_right h_cond]
        rw [h_scan_eq]
        constructor
        · rfl
        · intro j hj
          rcases em (j < M) with (hjM | hjM)
          · exact hle j hjM
          · have hjM_eq : j = M := by omega
            have hq1_le0 : q.1 ≤ 0 := by omega
            have hpos_q2 : (0 : ℚ) < (q.2 : ℚ) := by exact_mod_cast hq2_pos
            simpa [hjM_eq, ← hq_div] using
              div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast hq1_le0) (by linarith)
    · -- Case: there exists k < M that is the max
      let qk := qn (N k) (B k)
      have hqk2_pos : 0 < qk.2 := (qn_spec (N k) (B k)).1
      have hqk_div : (qk.1 : ℚ) / (qk.2 : ℚ) = (N k : ℚ) / (B k : ℚ) := (qn_spec (N k) (B k)).2.1
      let qM := qn (N M) (B M)
      have hqM2_pos : 0 < qM.2 := (qn_spec (N M) (B M)).1
      have hqM_div : (qM.1 : ℚ) / (qM.2 : ℚ) = (N M : ℚ) / (B M : ℚ) := (qn_spec (N M) (B M)).2.1
      by_cases h_lt_int : qk.1 * qM.2 < qM.1 * qk.2
      · -- condition true: update to qM
        have h_lt_rat : (qk.1 : ℚ) / (qk.2 : ℚ) < (qM.1 : ℚ) / (qM.2 : ℚ) := by
          have hpos_k : (0 : ℚ) < (qk.2 : ℚ) := by exact_mod_cast hqk2_pos
          have hpos_M : (0 : ℚ) < (qM.2 : ℚ) := by exact_mod_cast hqM2_pos
          exact (div_lt_div_iff₀ hpos_k hpos_M).mpr (by exact_mod_cast h_lt_int)
        have hM_lt_succ : M < M + 1 := by omega
        have h_scan_eq_full : scan N B a (M + 1) = scanStep (scan N B a M) (N M) (B M) (a M) := by
          simp [scan]
        rw [h_scan_eq_full, hst_eq]
        have h_scan_step_val : scanStep ⟨qk.1, qk.2, Int.sign (B k) • a k, qk.2⟩ (N M) (B M) (a M) =
          ⟨qM.1, qM.2, Int.sign (B M) • a M, qM.2⟩ := by
          unfold scanStep; rw [ite_eq_left h_lt_int]
        rw [h_scan_step_val]
        right
        refine ⟨M, hM_lt_succ, ?_, ?_, ?_, ?_, rfl⟩
        · intro hBeq
          have hqM_zero : qM.1 = 0 := by unfold qM; simp [qn, hBeq]
          have hqM_one : qM.2 = 1 := by unfold qM; simp [qn, hBeq]
          rw [hqM_zero, hqM_one] at h_lt_rat
          simp at h_lt_rat
          rw [hqk_div] at h_lt_rat
          linarith
        · rw [← hqM_div]
          have hpos_qk : 0 < (qk.1 : ℚ) / (qk.2 : ℚ) := by
            rw [hqk_div]; exact hBk_pos
          linarith
        · intro j hj
          rcases em (j < M) with (hjM | hjM)
          · rw [hqk_div, hqM_div] at h_lt_rat
            by_cases hjk : j < k
            · have hlt_jk : (N j : ℚ) / B j < (N k : ℚ) / B k := hlt_before j hjk
              linarith
            · have hle_jk : (N j : ℚ) / B j ≤ (N k : ℚ) / B k := hle_all j hjM
              linarith
          · exact le_of_eq (by rw [show j = M by omega])
        · intro j hj
          rw [hqk_div, hqM_div] at h_lt_rat
          by_cases hjk : j < k
          · have hlt_jk : (N j : ℚ) / B j < (N k : ℚ) / B k := hlt_before j hjk
            linarith
          · have hle_jk : (N j : ℚ) / B j ≤ (N k : ℚ) / B k := hle_all j hj
            linarith
      · -- condition false: keep old max
        have h_not_lt_int : ¬ (qk.1 * qM.2 < qM.1 * qk.2) := h_lt_int
        have h_le_rat : (qM.1 : ℚ) / (qM.2 : ℚ) ≤ (qk.1 : ℚ) / (qk.2 : ℚ) := by
          have hpos_k : (0 : ℚ) < (qk.2 : ℚ) := by exact_mod_cast hqk2_pos
          have hpos_M : (0 : ℚ) < (qM.2 : ℚ) := by exact_mod_cast hqM2_pos
          have hle_int : qM.1 * qk.2 ≤ qk.1 * qM.2 := by omega
          have hle_rat' : (qM.1 : ℚ) * (qk.2 : ℚ) ≤ (qk.1 : ℚ) * (qM.2 : ℚ) := by exact_mod_cast hle_int
          exact (div_le_div_iff₀ hpos_M hpos_k).mpr hle_rat'
        have hk_lt_succ : k < M + 1 := by omega
        have h_scan_eq_full : scan N B a (M + 1) = scanStep (scan N B a M) (N M) (B M) (a M) := by
          simp [scan]
        rw [h_scan_eq_full, hst_eq]
        have h_scan_step_val : scanStep ⟨qk.1, qk.2, Int.sign (B k) • a k, qk.2⟩ (N M) (B M) (a M) =
          ⟨qk.1, qk.2, Int.sign (B k) • a k, qk.2⟩ := by
          unfold scanStep; rw [ite_eq_right h_not_lt_int]
        rw [h_scan_step_val]
        right
        refine ⟨k, hk_lt_succ, hBk_ne, hBk_pos, ?_, hlt_before, rfl⟩
        intro j hj
        rcases em (j < M) with (hjM | hjM)
        · exact hle_all j hjM
        · rw [show j = M by omega, ← hqM_div, ← hqk_div]; exact h_le_rat

theorem scan_spec {d : ℕ} (N B : ℕ → ℤ) (a : ℕ → Fin d → ℤ) (M : ℕ) :
    0 < (scan N B a M).bb ∧
    (fun i => ((scan N B a M).row i : ℚ) / (scan N B a M).bb) =
      ∑ k ∈ Finset.range M,
        if 0 < (N k : ℚ) / B k ∧ (∀ j < M, (N j : ℚ) / B j ≤ (N k : ℚ) / B k) ∧
            (∀ j < k, (N j : ℚ) / B j < (N k : ℚ) / B k)
          then (B k : ℚ)⁻¹ • (fun i => (a k i : ℚ)) else 0 := by
  rcases scan_max N B a M with ⟨h0, hle⟩ | ⟨k, hk, hBk, hpos, hmax, hstr, hsc⟩
  · rw [h0, Finset.sum_eq_zero (fun j hj => ite_eq_right (fun h => absurd (hle j (Finset.mem_range.mp hj))
      (not_le.mpr h.1)))]
    refine ⟨by simp [scan0], ?_⟩
    funext i
    simp [scan0]
  · rw [hsc]
    obtain ⟨hq2, -, hq3⟩ := qn_spec (N k) (B k)
    obtain ⟨e2, -⟩ := hq3 hBk
    refine ⟨hq2, ?_⟩
    rw [Finset.sum_eq_single k, ite_eq_left ⟨hpos, hmax, hstr⟩]
    · funext i
      simp only [Pi.smul_apply, smul_eq_mul, e2, Int.cast_mul, Int.cast_abs]
      rcases lt_or_gt_of_ne hBk with h | h
      · have hq : (B k : ℚ) < 0 := by exact_mod_cast h
        rw [Int.sign_eq_neg_one_of_neg h, abs_of_neg hq]
        field_simp
        push_cast
        ring
      · have hq : (0 : ℚ) < B k := by exact_mod_cast h
        rw [Int.sign_eq_one_of_pos h, abs_of_pos hq]
        field_simp
        push_cast
        ring
    · intro j hj hjk
      refine ite_eq_right fun ⟨_, hmj, hsj⟩ => ?_
      rcases lt_or_gt_of_ne hjk with h | h
      · exact absurd (hmj k hk) (not_le.mpr (hstr j h))
      · exact absurd (hmax j (Finset.mem_range.mp hj)) (not_le.mpr (hsj k h))
    · exact fun h => absurd (Finset.mem_range.mpr hk) h

theorem rdiag_eq (A Y Bb P2 PG PB Tii : ℤ) (d : ℕ) (hd : 1 ≤ d) (hBb : 0 < Bb) (hP2 : 0 < P2) (hPG : 0 < PG)
    (hPB : 0 < PB) (hT : 0 < Tii) :
    ⌊((A : ℚ) / Bb * ((Y : ℚ) / P2) - 1 / 8 / (d : ℚ) / ((Tii : ℚ) / PG)) * PB⌋ =
      (A * Y * (8 * d * Tii) - PG * Bb * P2) * PB / (Bb * P2 * (8 * d * Tii)) := by
  have hd_pos : (d : ℚ) ≠ 0 := by
    intro hzero
    have hd0 : (d : ℕ) = 0 := by exact_mod_cast hzero
    have : 1 ≤ (0 : ℕ) := by simpa [hd0] using hd
    exact Nat.not_succ_le_zero 0 this
  have h_denom_pos : 0 < Bb * P2 * (8 * (d : ℤ) * Tii) := by
    positivity
  have h_denom_nonneg : 0 ≤ Bb * P2 * (8 * (d : ℤ) * Tii) := by
    positivity
  let D : ℕ := (Bb * P2 * (8 * (d : ℤ) * Tii)).toNat
  have hD_eq : (D : ℤ) = Bb * P2 * (8 * (d : ℤ) * Tii) :=
    Int.toNat_of_nonneg h_denom_nonneg
  have hD_eq_ℚ : (D : ℚ) = (Bb : ℚ) * (P2 : ℚ) * (8 * (d : ℚ) * (Tii : ℚ)) := by
    exact_mod_cast hD_eq
  have h_expr : ((A : ℚ) / Bb * ((Y : ℚ) / P2) - 1 / 8 / (d : ℚ) / ((Tii : ℚ) / PG)) * PB =
      ((A * Y * (8 * d * Tii) - PG * Bb * P2) * PB : ℚ) / (Bb * P2 * (8 * d * Tii)) := by
    push_cast
    field_simp [show (Bb : ℚ) ≠ 0 from by exact_mod_cast hBb.ne.symm,
      show (P2 : ℚ) ≠ 0 from by exact_mod_cast hP2.ne.symm,
      show (PG : ℚ) ≠ 0 from by exact_mod_cast hPG.ne.symm,
      show (Tii : ℚ) ≠ 0 from by exact_mod_cast hT.ne.symm,
      hd_pos]
  rw [h_expr]
  simpa [hD_eq, hD_eq_ℚ] using Rat.floor_intCast_div_natCast ((A * Y * (8 * d * Tii) - PG * Bb * P2) * PB) D

end AdversarialBco.Bit.TriM
