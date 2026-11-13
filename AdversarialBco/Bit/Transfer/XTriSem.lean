/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XTriEq

@[expose] public section

/-!
# TRI-M, the integer model against the rational one

The counts of the program (`mst_le`, `ellPos_le`, `2^{B_v}`, `2^{j_s}`), the denominators and the magnitudes of the
iterates and stages.
-/

open AdversarialBco.Bit AdversarialBco.Bit.RQ AdversarialBco.Bit.Transfer AdversarialBco.Bit.TriM Matrix

theorem AdversarialBco.Bit.TriM.mst_le (n : ℕ) (_hn : 1 ≤ n) : triMstQ (1 / 2) n ≤ n.size + 1 := by
  unfold triMstQ
  have hceil : ⌈(n : ℚ) / ((1 : ℚ) / 2)⌉₊ = 2 * n := by
    have h : (n : ℚ) / ((1 : ℚ) / 2) = (2 * n : ℚ) := by ring
    rw [h]
    simpa using Nat.ceil_natCast (2 * n)
  rw [hceil]
  rw [max_le_iff]
  constructor
  · omega
  · apply Nat.clog_le_of_le_pow
    have hn_lt : n < 2 ^ n.size := Nat.lt_size_self n
    have h_lt : 2 * n < 2 ^ (n.size + 1) := by
      calc
        2 * n < 2 * 2 ^ n.size := Nat.mul_lt_mul_of_pos_left hn_lt (by norm_num)
        _ = 2 ^ (n.size + 1) := by ring
    omega

theorem AdversarialBco.Bit.TriM.ellPos_le {d : ℕ} (n : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n) :
    ellPos d n ≤ 22 + 3 * d.size + 4 * n.size := by
  have h_mst : triMstQ (1 / 2) n ≤ n.size + 1 := by
    have h2pos : 1 < 2 := by norm_num
    unfold triMstQ
    have hceil : ⌈(n : ℚ) / ((1 : ℚ) / 2)⌉₊ = 2 * n := by
      have hdiv : (n : ℚ) / ((1 : ℚ) / 2) = ((2 * n : ℕ) : ℚ) := by
        push_cast
        field_simp
      rw [hdiv]
      exact Nat.ceil_natCast (2 * n)
    rw [hceil]
    have hclog : Nat.clog 2 (2 * n) ≤ n.size + 1 := by
      have hn_lt : n < 2 ^ n.size := Nat.lt_size_self n
      have h2n_lt : 2 * n < 2 ^ (n.size + 1) := by
        calc
          2 * n < 2 * 2 ^ n.size := Nat.mul_lt_mul_of_pos_left hn_lt (by norm_num)
          _ = 2 ^ (n.size + 1) := by ring
      have h2n_le : 2 * n ≤ 2 ^ (n.size + 1) := Nat.le_of_lt h2n_lt
      calc
        Nat.clog 2 (2 * n) ≤ Nat.clog 2 (2 ^ (n.size + 1)) := Nat.clog_mono_right 2 h2n_le
        _ = n.size + 1 := Nat.clog_pow 2 (n.size + 1) h2pos
    have h1le : (1 : ℕ) ≤ n.size + 1 := by omega
    exact max_le h1le hclog
  unfold ellPos
  rw [Nat.clog_le_iff_le_pow (by norm_num : 1 < 2)]
  -- Goal: 3 * 2 ^ 19 * (d * n) ^ 3 * triMstQ (1 / 2) n ≤ 2 ^ (22 + 3 * d.size + 4 * n.size)
  have h_nsize_le : n.size + 1 ≤ 2 ^ (n.size + 1) := by
    have h_lt : n.size + 1 < 2 ^ (n.size + 1) := Nat.lt_two_pow_self
    exact Nat.le_of_lt h_lt
  have h_triMst_le : triMstQ (1 / 2) n ≤ 2 ^ (n.size + 1) :=
    Nat.le_trans h_mst h_nsize_le
  have h_3pow_le : 3 * 2 ^ 19 ≤ 2 ^ 21 := by norm_num
  have hd_lt : d < 2 ^ d.size := Nat.lt_size_self d
  have hn_lt : n < 2 ^ n.size := Nat.lt_size_self n
  have hd_pos : 0 < d := by omega
  have h_pow_pos : 0 < 2 ^ n.size := pow_pos (by norm_num) n.size
  have h_dn_lt : d * n < 2 ^ d.size * 2 ^ n.size := by
    have h1 : d * n < d * 2 ^ n.size := Nat.mul_lt_mul_of_pos_left hn_lt hd_pos
    have h2 : d * 2 ^ n.size < 2 ^ d.size * 2 ^ n.size :=
      Nat.mul_lt_mul_of_pos_right hd_lt h_pow_pos
    exact lt_trans h1 h2
  have h_dn_le_pow : d * n ≤ 2 ^ (d.size + n.size) := by
    have h_pow_add : 2 ^ d.size * 2 ^ n.size = 2 ^ (d.size + n.size) := by rw [pow_add]
    rw [h_pow_add] at h_dn_lt
    exact Nat.le_of_lt h_dn_lt
  have h_dn_cube_le : (d * n) ^ 3 ≤ (2 ^ (d.size + n.size)) ^ 3 :=
    Nat.pow_le_pow_left h_dn_le_pow 3
  have h_pow3_eq : (2 ^ (d.size + n.size)) ^ 3 = 2 ^ (3 * (d.size + n.size)) := by
    rw [← pow_mul, mul_comm, pow_mul]
  have h_dn_cube_le' : (d * n) ^ 3 ≤ 2 ^ (3 * (d.size + n.size)) := by
    rw [h_pow3_eq] at h_dn_cube_le
    exact h_dn_cube_le
  have h_expand : 3 * (d.size + n.size) = 3 * d.size + 3 * n.size := by ring
  rw [h_expand] at h_dn_cube_le'
  have h_mul1 : 3 * 2 ^ 19 * (d * n) ^ 3 ≤ 2 ^ 21 * 2 ^ (3 * d.size + 3 * n.size) :=
    Nat.mul_le_mul h_3pow_le h_dn_cube_le'
  have h_mul2 : (3 * 2 ^ 19 * (d * n) ^ 3) * triMstQ (1 / 2) n ≤
      (2 ^ 21 * 2 ^ (3 * d.size + 3 * n.size)) * 2 ^ (n.size + 1) :=
    Nat.mul_le_mul h_mul1 h_triMst_le
  calc
    3 * 2 ^ 19 * (d * n) ^ 3 * triMstQ (1 / 2) n ≤ (2 ^ 21 * 2 ^ (3 * d.size + 3 * n.size)) * 2 ^ (n.size + 1) := h_mul2
    _ = 2 ^ (21 + (3 * d.size + 3 * n.size)) * 2 ^ (n.size + 1) := by rw [← pow_add]
    _ = 2 ^ ((21 + (3 * d.size + 3 * n.size)) + (n.size + 1)) := by rw [← pow_add]
    _ = 2 ^ (22 + 3 * d.size + 4 * n.size) := by ring

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

theorem AdversarialBco.Bit.TriM.tzStage_D {d m : ℕ} (n : ℕ) (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ)
    (Dc : ℤ) (ch : Fin d → ℤ) (ω : ℕ → ℕ → Bool) (j : ℕ) :
    (tzStage n A b Dc ch ω j).D = Dc * 2 ^ (1 + j * tzGc d (ellPos d n)) := by
  induction j with
  | zero =>
      simp [tzStage]
      ring
  | succ j ih =>
      rw [tzStage]
      dsimp [tzComp]
      rw [ih]
      ring

theorem AdversarialBco.Bit.TriM.tzIter_bound {d M : ℕ} (c : DC) (T : Matrix (Fin d) (Fin d) ℤ) (mu : Fin d → ℤ)
    (ra : ℕ → Fin d → ℤ) (rb : ℕ → ℤ) (Y : ℕ → Fin d → ℤ) (hR : 0 ≤ c.R) (hRB : c.R ≤ c.Bh) (hAl : 0 < c.Al)
    (hAB : c.Al ≤ c.Bh) (hPG : 0 ≤ c.PG) (hPGB : c.PG ≤ c.Bh) (t : ℕ) :
    (∀ i, |(tzIter c T mu ra rb M Y t).1 i| ≤ c.Bh) ∧ ∀ i l, |(tzIter c T mu ra rb M Y t).2 i l| ≤ c.Bh := by
  induction' t with t ih
  · -- t = 0
    have h0Bh : 0 ≤ c.Bh := le_trans hR hRB
    refine ⟨?_, ?_⟩
    · intro i
      rw [tzIter]
      simp [h0Bh]
    · intro i l
      rw [tzIter]
      dsimp
      simp [Matrix.one_apply]
      by_cases h : i = l
      · subst h; simp; rw [abs_of_nonneg hPG]; exact hPGB
      · simp [h, h0Bh]
  · -- t = t + 1
    rw [tzIter]
    have hbound := tzUpd_bound c (tzIter c T mu ra rb M Y t)
      (Tᵀ *ᵥ (tzKeep T mu ra rb M (tzZ (tzIter c T mu ra rb M Y t) (Y t) c.P2)).row)
      (Y t)
      (tzKeep T mu ra rb M (tzZ (tzIter c T mu ra rb M Y t) (Y t) c.P2)).bb
      hR hRB hAl hAB
    rcases hbound with ⟨h1, h2, _⟩
    exact ⟨h1, h2⟩

theorem AdversarialBco.Bit.TriM.tzSum_bound {d M : ℕ} (c : DC) (T : Matrix (Fin d) (Fin d) ℤ) (mu : Fin d → ℤ)
    (ra : ℕ → Fin d → ℤ) (rb : ℕ → ℤ) (Y : ℕ → Fin d → ℤ) (hR : 0 ≤ c.R) (hRB : c.R ≤ c.Bh) (hAl : 0 < c.Al)
    (hAB : c.Al ≤ c.Bh) (hPG : 0 ≤ c.PG) (hPGB : c.PG ≤ c.Bh) (N : ℕ) :
    (∀ i, |(tzSum c T mu ra rb M Y N).1 i| ≤ N * c.Bh) ∧ ∀ i l, |(tzSum c T mu ra rb M Y N).2 i l| ≤ N * c.Bh := by
  have h_iter_bound := tzIter_bound (M := M) c T mu ra rb Y hR hRB hAl hAB hPG hPGB
  constructor
  · intro i
    dsimp [tzSum]
    rw [Prod.fst_sum, Finset.sum_apply]
    calc
      |∑ t ∈ Finset.range N, (tzIter c T mu ra rb M Y t).1 i| ≤ ∑ t ∈ Finset.range N, |(tzIter c T mu ra rb M Y t).1 i| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ t ∈ Finset.range N, c.Bh := by
        apply Finset.sum_le_sum
        intro t ht
        exact (h_iter_bound t).1 i
      _ = (Finset.card (Finset.range N)) • c.Bh := by simp
      _ = N • c.Bh := by simp
      _ = N * c.Bh := by simp
  · intro i l
    dsimp [tzSum]
    rw [Prod.snd_sum]
    rw [Matrix.sum_apply]
    calc
      |∑ t ∈ Finset.range N, (tzIter c T mu ra rb M Y t).2 i l| ≤ ∑ t ∈ Finset.range N, |(tzIter c T mu ra rb M Y t).2 i l| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ t ∈ Finset.range N, c.Bh := by
        apply Finset.sum_le_sum
        intro t ht
        exact (h_iter_bound t).2 i l
      _ = (Finset.card (Finset.range N)) • c.Bh := by simp
      _ = N • c.Bh := by simp
      _ = N * c.Bh := by simp

theorem AdversarialBco.Bit.TriM.tzStage_bound {d m : ℕ} (n : ℕ) (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ)
    (Dc : ℤ) (ch : Fin d → ℤ) (ω : ℕ → ℕ → Bool) (H : ℤ) (hH : ∀ i, |ch i| ≤ H) (hDH : |Dc| ≤ H) (j : ℕ) :
    (∀ i, |(tzStage n A b Dc ch ω j).mu i| ≤ 2 * H * (2 ^ tzGc d (ellPos d n) +
        d * (2 ^ triNeQ d (ellPos d n) * (tzDC d (ellPos d n)).Bh)) ^ j) ∧
    ∀ i l, |(tzStage n A b Dc ch ω j).T i l| ≤ 2 * H * (2 ^ tzGc d (ellPos d n) +
        d * (2 ^ triNeQ d (ellPos d n) * (tzDC d (ellPos d n)).Bh)) ^ j := by
  have hH_nonneg : 0 ≤ H := by
    have h_abs_nonneg : 0 ≤ |Dc| := abs_nonneg _
    linarith
  set ℓ := ellPos d n with hℓ
  set Gc := tzGc d ℓ with hGc
  set E := (2 : ℤ) ^ Gc + (d : ℤ) * ((2 : ℤ) ^ triNeQ d ℓ * (tzDC d ℓ).Bh) with hE
  set K := fun (j : ℕ) => (2 : ℤ) * H * E ^ j with hK
  have hE_nonneg : 0 ≤ E := by
    rw [hE]
    have h1 : 0 ≤ (2 : ℤ) ^ Gc := pow_nonneg (by norm_num) _
    have h2 : 0 ≤ (d : ℤ) := by exact_mod_cast Nat.zero_le _
    have h3 : 0 ≤ (2 : ℤ) ^ triNeQ d ℓ := pow_nonneg (by norm_num) _
    have h4 : 0 ≤ (tzDC d ℓ).Bh := by
      unfold tzDC
      have hpos : 0 ≤ (2 : ℤ) ^ (triLa (triSQ d) - 10 + tzG d ℓ) := pow_nonneg (by norm_num) _
      nlinarith
    have hd : 0 ≤ (d : ℤ) * ((2 : ℤ) ^ triNeQ d ℓ * (tzDC d ℓ).Bh) := by
      have hpos' : 0 ≤ (2 : ℤ) ^ triNeQ d ℓ * (tzDC d ℓ).Bh := by
        nlinarith
      nlinarith
    nlinarith
  have hK_nonneg : ∀ j, 0 ≤ K j := by
    intro j
    rw [hK]
    have hEj : 0 ≤ E ^ j := pow_nonneg hE_nonneg _
    nlinarith
  have h_La_ge_10 : 10 ≤ triLa (triSQ d) := by
    unfold triLa
    have h_triSQ : 4 ≤ triSQ d := (triSQ_bounds d).1
    have h_sq : 16 ≤ (triSQ d) ^ 2 := Nat.pow_le_pow_left h_triSQ 2
    have h_mul : 70 ≤ 5 * (triSQ d) ^ 2 := by nlinarith
    have h_pos : 0 < 7 := by norm_num
    rw [Nat.le_div_iff_mul_le h_pos]
    nlinarith
  have h_dc_R_nonneg : 0 ≤ (tzDC d ℓ).R := by
    unfold tzDC; exact pow_nonneg (by norm_num) _
  have h_dc_R_le_Bh : (tzDC d ℓ).R ≤ (tzDC d ℓ).Bh := by
    unfold tzDC
    have h_expand : (2 : ℤ) ^ (triLa (triSQ d) - 3 + tzG d ℓ) =
        (128 : ℤ) * (2 : ℤ) ^ (triLa (triSQ d) - 10 + tzG d ℓ) := by
      have h_exp_eq : triLa (triSQ d) - 3 + tzG d ℓ = (triLa (triSQ d) - 10 + tzG d ℓ) + 7 := by
        have h10 : 10 ≤ triLa (triSQ d) := h_La_ge_10
        omega
      rw [h_exp_eq, pow_add]
      norm_num
      ring
    rw [h_expand]
    have h_nonneg : 0 ≤ (2 : ℤ) ^ (triLa (triSQ d) - 10 + tzG d ℓ) := pow_nonneg (by norm_num) _
    nlinarith
  have h_dc_Al_pos : 0 < (tzDC d ℓ).Al := by
    unfold tzDC; exact pow_pos (by norm_num) _
  have h_dc_Al_le_Bh : (tzDC d ℓ).Al ≤ (tzDC d ℓ).Bh := by
    unfold tzDC
    have h_le_G : (2 : ℤ) ^ (triBvQ d + triJsQ d ℓ) ≤ (2 : ℤ) ^ (tzG d ℓ) := by
      have hG_eq : tzG d ℓ = triBvQ d + triJsQ d ℓ + triJaQ d := rfl
      rw [hG_eq]
      have h_nat : (2 : ℕ) ^ (triBvQ d + triJsQ d ℓ) ≤ (2 : ℕ) ^ (triBvQ d + triJsQ d ℓ + triJaQ d) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      exact_mod_cast h_nat
    have h_G_le_Bh : (2 : ℤ) ^ (tzG d ℓ) ≤ (tzDC d ℓ).Bh := by
      unfold tzDC
      have h_pow : (2 : ℤ) ^ (tzG d ℓ) ≤ (2 : ℤ) ^ (triLa (triSQ d) - 10 + tzG d ℓ) := by
        have h_nat : (2 : ℕ) ^ (tzG d ℓ) ≤ (2 : ℕ) ^ (triLa (triSQ d) - 10 + tzG d ℓ) :=
          Nat.pow_le_pow_right (by norm_num) (by omega)
        exact_mod_cast h_nat
      have h_nonneg : 0 ≤ (2 : ℤ) ^ (triLa (triSQ d) - 10 + tzG d ℓ) := pow_nonneg (by norm_num) _
      nlinarith
    exact le_trans h_le_G h_G_le_Bh
  have h_dc_PG_nonneg : 0 ≤ (tzDC d ℓ).PG := by
    unfold tzDC; exact pow_nonneg (by norm_num) _
  have h_dc_PG_le_Bh : (tzDC d ℓ).PG ≤ (tzDC d ℓ).Bh := by
    unfold tzDC
    have h_pow : (2 : ℤ) ^ (tzG d ℓ) ≤ (2 : ℤ) ^ (triLa (triSQ d) - 10 + tzG d ℓ) := by
      have h_nat : (2 : ℕ) ^ (tzG d ℓ) ≤ (2 : ℕ) ^ (triLa (triSQ d) - 10 + tzG d ℓ) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      exact_mod_cast h_nat
    have h_nonneg : 0 ≤ (2 : ℤ) ^ (triLa (triSQ d) - 10 + tzG d ℓ) := pow_nonneg (by norm_num) _
    nlinarith
  induction' j with j ih
  · -- base case j = 0
    have h0 : tzStage n A b Dc ch ω 0 = ⟨2 * Dc, fun i => 2 * ch i, Dc • 1⟩ := rfl
    have h_pow0 : E ^ 0 = 1 := by rw [pow_zero]
    have h_mu_goal : ∀ i, |(2 * ch i)| ≤ 2 * H := by
      intro i
      calc
        |(2 : ℤ) * ch i| = |(2 : ℤ)| * |ch i| := abs_mul (2 : ℤ) (ch i)
        _ = (2 : ℤ) * |ch i| := by norm_num
        _ ≤ (2 : ℤ) * H := mul_le_mul_of_nonneg_left (hH i) (by norm_num)
    refine ⟨?_, ?_⟩
    · intro i
      simpa [h0, h_pow0] using h_mu_goal i
    · intro i l
      rw [h0, h_pow0, mul_one]
      simp [Matrix.one_apply]
      split_ifs with h_eq
      · nlinarith
      · simp; nlinarith
  · -- inductive step
    rcases ih with ⟨ih_mu, ih_T⟩
    set P := tzStage n A b Dc ch ω j with hP
    set S := tzSum (tzDC d ℓ) P.T P.mu (onN (tzRowA A b))
      (onN (tzRowB A b ch (1 + j * tzGc d ℓ) j P.D)) (m + (d + d))
      (tzY d (triBgQ d) (ω j)) (2 ^ triNeQ d ℓ) with hS
    set Q := (2 : ℤ) ^ triNeQ d ℓ * (tzDC d ℓ).Bh with hQ
    have h_tzSum := tzSum_bound (M := m + (d + d)) (tzDC d ℓ) P.T P.mu (onN (tzRowA A b))
      (onN (tzRowB A b ch (1 + j * tzGc d ℓ) j P.D)) (tzY d (triBgQ d) (ω j))
      h_dc_R_nonneg h_dc_R_le_Bh h_dc_Al_pos h_dc_Al_le_Bh h_dc_PG_nonneg h_dc_PG_le_Bh
      (2 ^ triNeQ d ℓ)
    rcases h_tzSum with ⟨hS1, hS2⟩
    have hS1' : ∀ i, |S.1 i| ≤ Q := by
      intro i
      have := hS1 i
      rw [hQ]
      simpa using this
    have hS2' : ∀ i l, |S.2 i l| ≤ Q := by
      intro i l
      have := hS2 i l
      rw [hQ]
      simpa using this
    have hQ_nonneg : 0 ≤ Q := by
      rw [hQ]
      have h1 : 0 ≤ (2 : ℤ) ^ triNeQ d ℓ := pow_nonneg (by norm_num) _
      have hBh : 0 ≤ (tzDC d ℓ).Bh := by
        unfold tzDC
        have hpos : 0 ≤ (2 : ℤ) ^ (triLa (triSQ d) - 10 + tzG d ℓ) := pow_nonneg (by norm_num) _
        nlinarith
      nlinarith
    have h_comp := comp_bound P S Gc (K j) Q (hK_nonneg j) hQ_nonneg ih_mu ih_T hS1' hS2'
    rcases h_comp with ⟨h_mu_comp, h_T_comp⟩
    have hEQ : E = 2 ^ Gc + (d : ℤ) * Q := by rw [hE, hQ]
    have h_target : K j * ((2 : ℤ) ^ Gc + (d : ℤ) * Q) = 2 * H * E ^ (j + 1) := by
      show 2 * H * E ^ j * ((2 : ℤ) ^ Gc + (d : ℤ) * Q) = _
      rw [pow_succ, ← hEQ]
      ring
    have h_tzStage_succ : tzStage n A b Dc ch ω (j + 1) = tzComp P S Gc := by
      rw [hP, hS, hGc]
      rfl
    refine ⟨?_, ?_⟩
    · intro i
      rw [h_tzStage_succ]
      exact (h_mu_comp i).trans_eq h_target
    · intro i l
      rw [h_tzStage_succ]
      exact (h_T_comp i l).trans_eq h_target
