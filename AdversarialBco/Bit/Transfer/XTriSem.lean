/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XTriM

@[expose] public section

/-!
# TRI-M, the bounds of the counts

The bounds of `2^{B_v}` and `2^{j_s}` (`pow_triBvQ_le`, `pow_triJsQ_le`) and `ceil_div_le_self`.
-/

open AdversarialBco.Bit AdversarialBco.Bit.RQ AdversarialBco.Bit.Transfer AdversarialBco.Bit.TriM Matrix

theorem AdversarialBco.Bit.TriM.pow_triBvQ_le {d : ℕ} (hd : 1 ≤ d) : 2 ^ triBvQ d ≤ 2 ^ 162 * d ^ 22 := by
  set x := (bvN d + bvD d - 1) / bvD d with hx
  have h_triBvQ_eq : triBvQ d = Nat.clog 4 x := by
    rw [hx, AdversarialBco.Bit.TriM.triBvQ_eq hd]
  by_cases hzero : triBvQ d = 0
  · -- case triBvQ d = 0
    rw [hzero, pow_zero]
    have hdpos : 0 < d := by omega
    have hpos : 0 < 2 ^ 162 * d ^ 22 := by
      apply mul_pos (pow_pos (by norm_num) _) (pow_pos hdpos _)
    omega
  · -- case triBvQ d ≥ 1
    have hpos : 0 < triBvQ d := Nat.pos_of_ne_zero hzero
    have hbvDpos : 0 < bvD d := by
      have h1 : 0 < 4 ^ triJaQ d := pow_pos (by norm_num) _
      have h2 : 0 < 400000000 := by norm_num
      exact mul_pos h1 h2
    have hbvD_ge_one : 1 ≤ bvD d := by omega
    have hx_gt_one : 1 < x := by
      have hclog_pos : 0 < Nat.clog 4 x := by
        rw [← h_triBvQ_eq]
        exact hpos
      by_contra! hle
      have hclog_zero : Nat.clog 4 x = 0 := Nat.clog_of_right_le_one hle 4
      rw [hclog_zero] at hclog_pos
      exact lt_irrefl _ hclog_pos
    have h_pow_pred_lt : 4 ^ (triBvQ d - 1) < x := by
      apply Nat.pow_lt_of_lt_clog
      rw [h_triBvQ_eq]
      omega
    have hx_le_bvN : x ≤ bvN d := by
      rw [hx]
      apply (Nat.div_le_iff_le_mul hbvDpos).mpr
      have hineq : bvN d ≤ bvN d * bvD d := by
        calc
          bvN d = bvN d * 1 := by simp
          _ ≤ bvN d * bvD d := Nat.mul_le_mul_left _ hbvD_ge_one
      omega
    have h_four_pow_lt : 4 ^ triBvQ d < 4 * bvN d := by
      calc
        4 ^ triBvQ d = 4 * 4 ^ (triBvQ d - 1) := by
          rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ triBvQ d)]
        _ < 4 * x := Nat.mul_lt_mul_of_pos_left h_pow_pred_lt (by norm_num)
        _ ≤ 4 * bvN d := Nat.mul_le_mul_left _ hx_le_bvN
    have h_bvN_bound : bvN d ≤ 2 ^ 322 * d ^ 44 := by
      have hd2N := AdversarialBco.Bit.TriM.d2N_le hd
      have heloI := AdversarialBco.Bit.TriM.eloI_le hd
      have h_sq : (d + 1) ^ 2 ≤ 4 * d ^ 2 := by
        have hd1 : d + 1 ≤ 2 * d := by omega
        nlinarith
      have h_elo_sq : eloI d ^ 2 ≤ (2 ^ 112 * d ^ 14) ^ 2 :=
        Nat.pow_le_pow_left heloI 2
      calc
        bvN d = 64 * (d + 1) ^ 2 * d2N d * eloI d ^ 2 := rfl
        _ ≤ 64 * (4 * d ^ 2) * (2 ^ 90 * d ^ 14) * ((2 ^ 112 * d ^ 14) ^ 2) := by
          apply Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (le_refl _) h_sq) hd2N) h_elo_sq
        _ = 64 * 4 * d ^ 2 * 2 ^ 90 * d ^ 14 * (2 ^ 224 * d ^ 28) := by ring
        _ = 256 * 2 ^ 90 * 2 ^ 224 * d ^ (2 + 14 + 28) := by ring
        _ = 2 ^ 8 * 2 ^ 90 * 2 ^ 224 * d ^ 44 := by norm_num
        _ = 2 ^ 322 * d ^ 44 := by
          rw [← pow_add, ← pow_add]
    have h_four_mul_bvN_bound : 4 * bvN d ≤ 2 ^ 324 * d ^ 44 := by
      have h4 : 4 = 2 ^ 2 := by norm_num
      rw [h4]
      calc
        2 ^ 2 * bvN d ≤ 2 ^ 2 * (2 ^ 322 * d ^ 44) := Nat.mul_le_mul_left _ h_bvN_bound
        _ = (2 ^ 2 * 2 ^ 322) * d ^ 44 := by ring
        _ = 2 ^ 324 * d ^ 44 := by
          rw [← pow_add]
    have h_target_sq : 2 ^ 324 * d ^ 44 = (2 ^ 162 * d ^ 22) ^ 2 := by
      calc
        2 ^ 324 * d ^ 44 = (2 ^ 162) ^ 2 * (d ^ 22) ^ 2 := by
          rw [← pow_mul, show (162 : ℕ) * 2 = 324 by norm_num, ← pow_mul, show (22 : ℕ) * 2 = 44 by norm_num]
        _ = (2 ^ 162 * d ^ 22) ^ 2 := by ring
    rw [h_target_sq] at h_four_mul_bvN_bound
    have h_sq_lt : (2 ^ triBvQ d) ^ 2 < (2 ^ 162 * d ^ 22) ^ 2 := by
      calc
        (2 ^ triBvQ d) ^ 2 = (2 ^ 2) ^ triBvQ d := by
          rw [← pow_mul, mul_comm, pow_mul]
        _ = 4 ^ triBvQ d := by norm_num
        _ < 4 * bvN d := h_four_pow_lt
        _ ≤ (2 ^ 162 * d ^ 22) ^ 2 := h_four_mul_bvN_bound
    have h_final : 2 ^ triBvQ d ≤ 2 ^ 162 * d ^ 22 := by
      have h_nonneg : 0 ≤ 2 ^ 162 * d ^ 22 := by positivity
      have h_lt : 2 ^ triBvQ d < 2 ^ 162 * d ^ 22 :=
        lt_of_pow_lt_pow_left₀ 2 h_nonneg h_sq_lt
      omega
    exact h_final

theorem AdversarialBco.Bit.TriM.ceil_div_le_self {N D : ℕ} (hN : 1 ≤ N) (hD : 1 ≤ D) : (N + D - 1) / D ≤ N := by
  have key : N + D - 1 ≤ D * N := by
    obtain ⟨a', ha⟩ : ∃ a', D = a' + 1 := ⟨D - 1, by omega⟩
    obtain ⟨b', hb⟩ : ∃ b', N = b' + 1 := ⟨N - 1, by omega⟩
    subst ha hb
    rw [show b' + 1 + (a' + 1) - 1 = a' + b' + 1 by omega]
    nlinarith [Nat.zero_le (a' * b')]
  exact Nat.div_le_of_le_mul key

theorem AdversarialBco.Bit.TriM.pow_triJsQ_le {d : ℕ} (hd : 1 ≤ d) (ℓ : ℕ) :
    2 ^ triJsQ d ℓ ≤ 2 * gbN d * 2 ^ triNeQ d ℓ * 2 ^ triJaQ d := by
  set Js := triJsQ d ℓ with hJs_def
  set Ne := triNeQ d ℓ with hNe_def
  set Ja := triJaQ d with hJa_def
  by_cases hJs0 : Js = 0
  · -- Case Js = 0: LHS = 1, RHS ≥ 2
    rw [hJs0, pow_zero]
    have hgbN : 1 ≤ gbN d := by
      rw [gbN]
      omega
    have h2Ne : 1 ≤ 2 ^ Ne := Nat.one_le_two_pow (n := Ne)
    have h2Ja : 1 ≤ 2 ^ Ja := Nat.one_le_two_pow (n := Ja)
    have hpos : 1 ≤ 2 * gbN d * 2 ^ Ne * 2 ^ Ja := by
      have h1 : 1 ≤ 2 := by omega
      have h_mul : 1 * 1 * 1 ≤ 2 * gbN d * (2 ^ Ne * 2 ^ Ja) :=
        Nat.mul_le_mul (Nat.mul_le_mul h1 hgbN) (Nat.mul_le_mul h2Ne h2Ja)
      simpa [mul_assoc] using h_mul
    exact hpos
  · -- Case Js > 0
    have hJs_pos : 0 < Js := Nat.pos_of_ne_zero hJs0
    have hJs_eq : Js = Nat.clog 4 ((jsN d ℓ + jsD d - 1) / jsD d) := by
      rw [hJs_def]
      exact AdversarialBco.Bit.TriM.triJsQ_eq hd ℓ
    rw [hJs_eq]
    set x := (jsN d ℓ + jsD d - 1) / jsD d with hx_def
    have hx_pos : 0 < x := by
      rw [hx_def]
      have hjsN_pos : 0 < jsN d ℓ := by
        rw [jsN]
        have h1 : 0 < gbN d := by
          rw [gbN]
          omega
        have h2 : 0 < 2 ^ Ne := pow_pos (by norm_num) _
        have h3 : 0 < 4 ^ Ja := pow_pos (by norm_num) _
        positivity
      have hjsD_pos : 0 < jsD d := by
        rw [jsD]
        have h1 : 0 < 4 ^ triBvQ d := pow_pos (by norm_num) _
        have h2 : 0 < d2N d := by
          rw [d2N]
          have hdpos : 0 < d := by omega
          have hrIpos : 0 < rI d := by
            rw [rI]
            apply pow_pos (by norm_num : 0 < 2) _
          have h1 : 0 < 4 * d * rI d ^ 2 * 4 ^ triJaQ d := by
            positivity
          have h2' : 0 ≤ d * (bI d * 2 ^ triJaQ d - 1) ^ 2 := Nat.zero_le _
          have h3' : 0 ≤ 2 * d * (d - 1) * bI d ^ 2 * 4 ^ triJaQ d := Nat.zero_le _
          omega
        positivity
      have hnum : jsD d ≤ jsN d ℓ + jsD d - 1 := by omega
      exact Nat.div_pos hnum hjsD_pos
    have h_pow_lt : 4 ^ (Nat.clog 4 x - 1) < x := by
      apply Nat.pow_lt_of_lt_clog (b := 4)
      have h_clog_pos : 0 < Nat.clog 4 x := by
        have hx_gt_one : 1 < x := by
          by_contra! hxle
          have h_clog_zero : Nat.clog 4 x = 0 := by
            rcases Nat.eq_zero_or_pos x with (hx0 | hxpos)
            · rw [hx0]; simp
            · have hx1 : x = 1 := by omega
              rw [hx1]; simp
          rw [h_clog_zero] at hJs_eq
          omega
        exact Nat.clog_pos (by norm_num : 1 < 4) hx_gt_one
      omega
    have h_lt : 4 ^ (Nat.clog 4 x) < 4 * x := by
      calc
        4 ^ (Nat.clog 4 x) = 4 ^ ((Nat.clog 4 x - 1) + 1) := by rw [Nat.sub_add_cancel (by omega : 1 ≤ Nat.clog 4 x)]
        _ = 4 ^ (Nat.clog 4 x - 1) * 4 := by rw [pow_succ]
        _ = 4 * 4 ^ (Nat.clog 4 x - 1) := by ring
        _ < 4 * x := Nat.mul_lt_mul_of_pos_left h_pow_lt (by norm_num)
    have hx_le_jsN : x ≤ jsN d ℓ := by
      rw [hx_def]
      have hjsD_pos : 1 ≤ jsD d := by
        rw [jsD]
        have h1 : 1 ≤ 4 ^ triBvQ d := Nat.one_le_pow _ _ (by norm_num : 0 < 4)
        have h2 : 1 ≤ d2N d := by
          rw [d2N]
          have hdpos : 0 < d := by omega
          have hrIpos : 0 < rI d := by
            rw [rI]
            exact pow_pos (by norm_num : 0 < 2) _
          have hfirst : 0 < 4 * d * rI d ^ 2 * 4 ^ triJaQ d := by
            positivity
          have hsum : 0 < 4 * d * rI d ^ 2 * 4 ^ triJaQ d + d * (bI d * 2 ^ triJaQ d - 1) ^ 2 + 2 * d * (d - 1) * bI d ^ 2 * 4 ^ triJaQ d := by
            omega
          omega
        exact Nat.mul_le_mul h1 h2
      have hjsN_pos : 1 ≤ jsN d ℓ := by
        rw [jsN]
        have h1 : 1 ≤ gbN d ^ 2 := by
          have : 1 ≤ gbN d := by
            rw [gbN]
            omega
          have hgbN_pos : 0 < gbN d := by omega
          exact Nat.one_le_pow _ _ hgbN_pos
        have h2 : 1 ≤ 2 ^ Ne := Nat.one_le_two_pow (n := Ne)
        have h3 : 1 ≤ 4 ^ Ja := Nat.one_le_pow _ _ (by norm_num : 0 < 4)
        exact Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3
      exact AdversarialBco.Bit.TriM.ceil_div_le_self hjsN_pos hjsD_pos
    have h_lt_jsN : 4 ^ (Nat.clog 4 x) < 4 * jsN d ℓ := by
      apply lt_of_lt_of_le h_lt
      exact Nat.mul_le_mul_left 4 hx_le_jsN
    have h_final : 4 * jsN d ℓ ≤ (2 * gbN d * 2 ^ Ne * 2 ^ Ja) ^ 2 := by
      rw [jsN]
      have h_pow_le : 2 ^ Ne ≤ 4 ^ Ne := by
        rw [show (4 : ℕ) ^ Ne = (2 ^ 2) ^ Ne by norm_num, ← pow_mul]
        exact Nat.pow_le_pow_right (by norm_num) (by omega)
      have h_sq_2Ne : (2 ^ Ne) ^ 2 = 4 ^ Ne := by
        calc
          (2 ^ Ne) ^ 2 = 2 ^ (Ne * 2) := by rw [pow_mul]
          _ = 2 ^ (2 * Ne) := by rw [mul_comm]
          _ = (2 ^ 2) ^ Ne := by rw [← pow_mul]
          _ = 4 ^ Ne := by norm_num
      have h_sq_2Ja : (2 ^ Ja) ^ 2 = 4 ^ Ja := by
        calc
          (2 ^ Ja) ^ 2 = 2 ^ (Ja * 2) := by rw [pow_mul]
          _ = 2 ^ (2 * Ja) := by rw [mul_comm]
          _ = (2 ^ 2) ^ Ja := by rw [← pow_mul]
          _ = 4 ^ Ja := by norm_num
      have h_rhs : (2 * gbN d * 2 ^ Ne * 2 ^ Ja) ^ 2 = 4 * gbN d ^ 2 * 4 ^ Ne * 4 ^ Ja := by
        calc
          (2 * gbN d * 2 ^ Ne * 2 ^ Ja) ^ 2 = (2 * gbN d * 2 ^ Ne * 2 ^ Ja) * (2 * gbN d * 2 ^ Ne * 2 ^ Ja) := by ring
          _ = 4 * gbN d ^ 2 * (2 ^ Ne * 2 ^ Ne) * (2 ^ Ja * 2 ^ Ja) := by ring
          _ = 4 * gbN d ^ 2 * ((2 ^ Ne) ^ 2) * ((2 ^ Ja) ^ 2) := by ring
          _ = 4 * gbN d ^ 2 * (4 ^ Ne) * (4 ^ Ja) := by rw [h_sq_2Ne, h_sq_2Ja]
          _ = 4 * gbN d ^ 2 * 4 ^ Ne * 4 ^ Ja := by ring
      rw [h_rhs]
      calc
        4 * (gbN d ^ 2 * 2 ^ Ne * 4 ^ Ja) = 4 * gbN d ^ 2 * 2 ^ Ne * 4 ^ Ja := by ring
        _ ≤ 4 * gbN d ^ 2 * 4 ^ Ne * 4 ^ Ja :=
          Nat.mul_le_mul (Nat.mul_le_mul (le_refl _) h_pow_le) (le_refl _)
    have h_sq_lt : 4 ^ (Nat.clog 4 x) < (2 * gbN d * 2 ^ Ne * 2 ^ Ja) ^ 2 :=
      lt_of_lt_of_le h_lt_jsN h_final
    have h_result : 2 ^ (Nat.clog 4 x) < 2 * gbN d * 2 ^ Ne * 2 ^ Ja := by
      -- 4^k = (2^2)^k = 2^(2*k) = (2^k)^2
      have h_sq_eq : 4 ^ (Nat.clog 4 x) = (2 ^ (Nat.clog 4 x)) ^ 2 := by
        calc
          4 ^ (Nat.clog 4 x) = (2 ^ 2) ^ (Nat.clog 4 x) := by norm_num
          _ = 2 ^ (2 * Nat.clog 4 x) := by rw [pow_mul]
          _ = 2 ^ ((Nat.clog 4 x) * 2) := by rw [mul_comm]
          _ = (2 ^ (Nat.clog 4 x)) ^ 2 := by rw [pow_mul]
      rw [h_sq_eq] at h_sq_lt
      exact (Nat.pow_lt_pow_iff_left (by norm_num)).mp h_sq_lt
    exact le_of_lt h_result

