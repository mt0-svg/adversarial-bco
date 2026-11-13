/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XTriAux

@[expose] public section

/-!
# TRI-M, the magnitudes

The bounds of a stage (`stageK_le`, `stage_D_le`, `stage_entries_le`) and linear bounds on the parameters of TRI-M
in `d` and `ℓ` (`triJaQ`, `triBvQ`, `triLh`, `tzP`, `gbN`, ...), for the work term of `TriRule`.
-/

open AdversarialBco.Bit AdversarialBco.Bit.RQ AdversarialBco.Bit.Transfer AdversarialBco.Bit.TriM Matrix

theorem AdversarialBco.Bit.TriM.stageK_le (d ℓ : ℕ) :
    (2 : ℤ) ^ tzGc d ℓ + d * (2 ^ triNeQ d ℓ * (tzDC d ℓ).Bh) ≤ 2 ^ (tzGc d ℓ + triLa (triSQ d) + d) := by
  set La := triLa (triSQ d) with hLa
  set G := tzG d ℓ with hG
  set Ne := triNeQ d ℓ with hNe
  have hGc_eq : tzGc d ℓ = G + Ne := rfl
  have hBh : (tzDC d ℓ).Bh = (161 : ℤ) * (2 : ℤ) ^ (La - 10 + G) := rfl
  rw [hGc_eq, hBh]
  -- First, prove La ≥ 10 (needed for subtraction to be proper)
  have hLa_ge_10 : 10 ≤ La := by
    have h4 : 4 ≤ triSQ d := (triSQ_bounds d).1
    have h_triLa4 : triLa 4 = 11 := by unfold triLa; norm_num
    have h_mono : triLa 4 ≤ triLa (triSQ d) := by
      unfold triLa
      have hsq : 4 ^ 2 ≤ (triSQ d) ^ 2 := Nat.pow_le_pow_left h4 2
      have hmul : 5 * 4 ^ 2 ≤ 5 * (triSQ d) ^ 2 := Nat.mul_le_mul_left 5 hsq
      exact Nat.div_le_div_right hmul
    omega
  -- Simplify LHS: 2^(G+Ne) + d * 2^Ne * 161 * 2^(La-10+G) = 2^(G+Ne) + d * 161 * 2^(G+Ne+La-10)
  have h_exp_eq : Ne + (La - 10 + G) = (G + Ne) + La - 10 := by omega
  have hLHS : (2 : ℤ) ^ (G + Ne) + (d : ℤ) * ((2 : ℤ) ^ Ne * ((161 : ℤ) * (2 : ℤ) ^ (La - 10 + G))) =
      (2 : ℤ) ^ (G + Ne) + (d : ℤ) * (161 : ℤ) * (2 : ℤ) ^ ((G + Ne) + La - 10) := by
    calc
      (2 : ℤ) ^ (G + Ne) + (d : ℤ) * ((2 : ℤ) ^ Ne * ((161 : ℤ) * (2 : ℤ) ^ (La - 10 + G)))
          = (2 : ℤ) ^ (G + Ne) + (d : ℤ) * (161 : ℤ) * ((2 : ℤ) ^ Ne * (2 : ℤ) ^ (La - 10 + G)) := by ring
      _ = (2 : ℤ) ^ (G + Ne) + (d : ℤ) * (161 : ℤ) * (2 : ℤ) ^ (Ne + (La - 10 + G)) := by rw [← pow_add]
      _ = (2 : ℤ) ^ (G + Ne) + (d : ℤ) * (161 : ℤ) * (2 : ℤ) ^ ((G + Ne) + La - 10) := by rw [h_exp_eq]
  rw [hLHS]
  -- Goal: 2^(G+Ne) + d * 161 * 2^(G+Ne+La-10) ≤ 2^((G+Ne) + La + d)
  -- Let A = G+Ne. Goal: 2^A + d*161*2^(A+La-10) ≤ 2^(A+La+d)
  set A := G + Ne with hA
  -- We'll prove: d*161*2^(A+La-10) ≤ 2^(A+La+d-2) and 2^A ≤ 2^(A+La+d-2)
  -- Then sum ≤ 2*2^(A+La+d-2) = 2^(A+La+d-1) ≤ 2^(A+La+d)
  -- Key inequality 1: d * 161 * 2^(A+La-10) ≤ 2^(A+La+d-2)
  have h_term1 : (d : ℤ) * (161 : ℤ) * (2 : ℤ) ^ (A + La - 10) ≤ (2 : ℤ) ^ (A + La + d - 2) := by
    have h_d_le : (d : ℤ) ≤ (2 : ℤ) ^ d := mod_cast (Nat.lt_two_pow_self (n := d)).le
    have h_161_le : (161 : ℤ) ≤ (2 : ℤ) ^ 8 := by norm_num
    have h_nonneg : 0 ≤ (2 : ℤ) ^ (A + La - 10) := pow_nonneg (by norm_num) _
    have h_prod : (d : ℤ) * (161 : ℤ) * (2 : ℤ) ^ (A + La - 10)
        ≤ (2 : ℤ) ^ d * (2 : ℤ) ^ 8 * (2 : ℤ) ^ (A + La - 10) := by
      nlinarith
    have h_pow_eq : (2 : ℤ) ^ d * (2 : ℤ) ^ 8 * (2 : ℤ) ^ (A + La - 10) = (2 : ℤ) ^ (A + La + d - 2) := by
      calc
        (2 : ℤ) ^ d * (2 : ℤ) ^ 8 * (2 : ℤ) ^ (A + La - 10)
          = ((2 : ℤ) ^ d * (2 : ℤ) ^ 8) * (2 : ℤ) ^ (A + La - 10) := by ring
        _ = (2 : ℤ) ^ (d + 8) * (2 : ℤ) ^ (A + La - 10) := by rw [pow_add]
        _ = (2 : ℤ) ^ ((d + 8) + (A + La - 10)) := by rw [← pow_add]
        _ = (2 : ℤ) ^ (A + La + d - 2) := by
          have h_exp : (d + 8) + (A + La - 10) = A + La + d - 2 := by omega
          rw [h_exp]
    calc
      (d : ℤ) * (161 : ℤ) * (2 : ℤ) ^ (A + La - 10) ≤ (2 : ℤ) ^ d * (2 : ℤ) ^ 8 * (2 : ℤ) ^ (A + La - 10) := h_prod
      _ = (2 : ℤ) ^ (A + La + d - 2) := h_pow_eq
  -- Key inequality 2: 2^A ≤ 2^(A+La+d-2)
  have h_term2 : (2 : ℤ) ^ A ≤ (2 : ℤ) ^ (A + La + d - 2) := by
    have h_exp_le : A ≤ A + La + d - 2 := by omega
    have h_nat : (2 : ℕ) ^ A ≤ (2 : ℕ) ^ (A + La + d - 2) :=
      Nat.pow_le_pow_right (by norm_num) h_exp_le
    exact_mod_cast h_nat
  -- Sum the two inequalities
  have h_sum : (2 : ℤ) ^ A + (d : ℤ) * (161 : ℤ) * (2 : ℤ) ^ (A + La - 10) ≤
      (2 : ℤ) ^ (A + La + d - 2) + (2 : ℤ) ^ (A + La + d - 2) := by
    nlinarith
  -- Now: 2^exp + 2^exp = 2 * 2^exp = 2^(exp+1)
  have h_double : (2 : ℤ) ^ (A + La + d - 2) + (2 : ℤ) ^ (A + La + d - 2) = (2 : ℤ) ^ (A + La + d - 1) := by
    have h : (2 : ℤ) ^ (A + La + d - 2) + (2 : ℤ) ^ (A + La + d - 2) = 2 * (2 : ℤ) ^ (A + La + d - 2) := by ring
    rw [h]
    -- 2 * 2^k = 2^1 * 2^k = 2^(1+k)
    calc
      2 * (2 : ℤ) ^ (A + La + d - 2) = (2 : ℤ) ^ 1 * (2 : ℤ) ^ (A + La + d - 2) := by norm_num
      _ = (2 : ℤ) ^ ((1 : ℕ) + (A + La + d - 2)) := by rw [pow_add]
      _ = (2 : ℤ) ^ (A + La + d - 1) := by
        have h_exp : (1 : ℕ) + (A + La + d - 2) = A + La + d - 1 := by omega
        rw [h_exp]
  -- Now: 2^(A+La+d-1) ≤ 2^(A+La+d)
  have h_final : (2 : ℤ) ^ (A + La + d - 1) ≤ (2 : ℤ) ^ (A + La + d) := by
    have h_exp_le : A + La + d - 1 ≤ A + La + d := by omega
    have h_nat : (2 : ℕ) ^ (A + La + d - 1) ≤ (2 : ℕ) ^ (A + La + d) :=
      Nat.pow_le_pow_right (by norm_num) h_exp_le
    exact_mod_cast h_nat
  -- Combine everything
  calc
    (2 : ℤ) ^ A + (d : ℤ) * (161 : ℤ) * (2 : ℤ) ^ (A + La - 10) ≤
        (2 : ℤ) ^ (A + La + d - 2) + (2 : ℤ) ^ (A + La + d - 2) := h_sum
    _ = (2 : ℤ) ^ (A + La + d - 1) := h_double
    _ ≤ (2 : ℤ) ^ (A + La + d) := h_final

theorem AdversarialBco.Bit.TriM.stage_D_le {d m : ℕ} (n : ℕ) (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ)
    (Dc : ℤ) (ch : Fin d → ℤ) (ω : ℕ → ℕ → Bool) (s : ℕ) (hD0 : 0 < Dc) (hD : Dc < 2 ^ s) (j : ℕ) :
    0 < (tzStage n A b Dc ch ω j).D ∧ (tzStage n A b Dc ch ω j).D < 2 ^ (s + 1 + j * tzGc d (ellPos d n)) := by
  have hD_eq : (tzStage n A b Dc ch ω j).D = Dc * (2 : ℤ) ^ (1 + j * tzGc d (ellPos d n)) := by
    induction' j with j ih
    · simp [tzStage]
      ring
    · simp [tzStage, tzComp, ih]
      ring
  rw [hD_eq]
  have hpos : 0 < (2 : ℤ) ^ (1 + j * tzGc d (ellPos d n)) := by
    positivity
  have hDpos : 0 < Dc * (2 : ℤ) ^ (1 + j * tzGc d (ellPos d n)) :=
    mul_pos hD0 hpos
  have hDlt : Dc * (2 : ℤ) ^ (1 + j * tzGc d (ellPos d n)) < (2 : ℤ) ^ s * (2 : ℤ) ^ (1 + j * tzGc d (ellPos d n)) :=
    mul_lt_mul_of_pos_right hD hpos
  have hsum : (2 : ℤ) ^ s * (2 : ℤ) ^ (1 + j * tzGc d (ellPos d n)) = (2 : ℤ) ^ (s + 1 + j * tzGc d (ellPos d n)) := by
    calc
      (2 : ℤ) ^ s * (2 : ℤ) ^ (1 + j * tzGc d (ellPos d n)) = (2 : ℤ) ^ (s + (1 + j * tzGc d (ellPos d n))) := by
        rw [← pow_add]
      _ = (2 : ℤ) ^ (s + 1 + j * tzGc d (ellPos d n)) := by ring
  exact And.intro hDpos (hDlt.trans_eq hsum)

theorem AdversarialBco.Bit.TriM.stage_entries_le {d m : ℕ} (n : ℕ) (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ)
    (Dc : ℤ) (ch : Fin d → ℤ) (ω : ℕ → ℕ → Bool) (s : ℕ) (hC : ∀ i, |ch i| ≤ 2 ^ s) (hD : |Dc| ≤ 2 ^ s) (j : ℕ) :
    (∀ i, |(tzStage n A b Dc ch ω j).mu i| ≤
        2 ^ (s + 1 + j * (tzGc d (ellPos d n) + triLa (triSQ d) + d))) ∧
    ∀ i l, |(tzStage n A b Dc ch ω j).T i l| ≤ 2 ^ (s + 1 + j * (tzGc d (ellPos d n) + triLa (triSQ d) + d)) := by
  set ℓ := ellPos d n with hℓ
  set K := (2 : ℤ) ^ tzGc d ℓ + d * ((2 : ℤ) ^ triNeQ d ℓ * (tzDC d ℓ).Bh) with hK
  have h_bound := tzStage_bound n A b Dc ch ω (2 ^ s) hC hD j
  rcases h_bound with ⟨h_mu, h_T⟩
  have hK_le : K ≤ (2 : ℤ) ^ (tzGc d ℓ + triLa (triSQ d) + d) := by
    simpa [hK, ℓ] using stageK_le d ℓ
  have hK_nonneg : 0 ≤ K := by
    rw [hK]
    have h2 : 0 ≤ (2 : ℤ) ^ tzGc d ℓ := pow_nonneg (by norm_num) _
    have hd : 0 ≤ (d : ℤ) := by exact Nat.cast_nonneg _
    have hrest : 0 ≤ (2 : ℤ) ^ triNeQ d ℓ * (tzDC d ℓ).Bh := by
      apply mul_nonneg (pow_nonneg (by norm_num) _) ?_
      -- (tzDC d ℓ).Bh = 161 * 2 ^ (triLa (triSQ d) - 10 + tzG d ℓ) which is nonnegative
      dsimp [tzDC]
      positivity
    nlinarith
  have hK_pow : K ^ j ≤ ((2 : ℤ) ^ (tzGc d ℓ + triLa (triSQ d) + d)) ^ j := by
    gcongr
  have h_pow_simp : ((2 : ℤ) ^ (tzGc d ℓ + triLa (triSQ d) + d)) ^ j
      = (2 : ℤ) ^ (j * (tzGc d ℓ + triLa (triSQ d) + d)) := by
    rw [← pow_mul, mul_comm]
  have h_pow_eq : (2 : ℤ) * (2 : ℤ) ^ s = (2 : ℤ) ^ (s + 1) := by
    rw [mul_comm, ← pow_succ 2 s]
  have h_final : 2 * (2 : ℤ) ^ s * K ^ j ≤ (2 : ℤ) ^ (s + 1 + j * (tzGc d ℓ + triLa (triSQ d) + d)) := by
    calc
      2 * (2 : ℤ) ^ s * K ^ j ≤ 2 * (2 : ℤ) ^ s * ((2 : ℤ) ^ (tzGc d ℓ + triLa (triSQ d) + d)) ^ j :=
        mul_le_mul_of_nonneg_left hK_pow (by norm_num)
      _ = 2 * (2 : ℤ) ^ s * ((2 : ℤ) ^ (j * (tzGc d ℓ + triLa (triSQ d) + d))) := by rw [h_pow_simp]
      _ = (2 * (2 : ℤ) ^ s) * (2 : ℤ) ^ (j * (tzGc d ℓ + triLa (triSQ d) + d)) := by ring
      _ = ((2 : ℤ) ^ (s + 1)) * (2 : ℤ) ^ (j * (tzGc d ℓ + triLa (triSQ d) + d)) := by rw [h_pow_eq]
      _ = (2 : ℤ) ^ ((s + 1) + j * (tzGc d ℓ + triLa (triSQ d) + d)) := by rw [← pow_add]
      _ = (2 : ℤ) ^ (s + 1 + j * (tzGc d ℓ + triLa (triSQ d) + d)) := by ring
  refine ⟨?_, ?_⟩
  · intro i
    apply le_trans (h_mu i) h_final
  · intro i l
    apply le_trans (h_T i l) h_final

theorem AdversarialBco.Bit.TriM.triJaQ_le_lin {d : ℕ} (hd : 1 ≤ d) : triJaQ d ≤ 12 + 2 * d := by
  have hpow := pow_triJaQ_le hd
  have hd_le : d ≤ 2 ^ d := (Nat.lt_two_pow_self (n := d)).le
  have hsq : d ^ 2 ≤ (2 ^ d) ^ 2 := Nat.pow_le_pow_left hd_le 2
  have h_pow_eq : (2 ^ d) ^ 2 = 2 ^ (2 * d) := by
    calc
      (2 ^ d) ^ 2 = 2 ^ (d * 2) := by rw [← pow_mul]
      _ = 2 ^ (2 * d) := by rw [mul_comm]
  have h_bound : 2 ^ 11 * d ^ 2 ≤ 2 ^ (11 + 2 * d) := by
    calc
      2 ^ 11 * d ^ 2 ≤ 2 ^ 11 * (2 ^ d) ^ 2 := Nat.mul_le_mul_left (2 ^ 11) hsq
      _ = 2 ^ 11 * 2 ^ (2 * d) := by rw [h_pow_eq]
      _ = 2 ^ (11 + 2 * d) := by rw [pow_add]
  have h_total : 2 ^ triJaQ d ≤ 2 ^ (11 + 2 * d) := le_trans hpow h_bound
  have h_le : triJaQ d ≤ 11 + 2 * d :=
    (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h_total
  omega

theorem AdversarialBco.Bit.TriM.triBvQ_le_lin {d : ℕ} (hd : 1 ≤ d) : triBvQ d ≤ 162 + 22 * d := by
  have h := pow_triBvQ_le hd
  have h2 : 2 ^ 162 * d ^ 22 ≤ 2 ^ (162 + 22 * d) := by
    calc
      2 ^ 162 * d ^ 22 ≤ 2 ^ 162 * (2 ^ d) ^ 22 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.le_of_lt (Nat.lt_two_pow_self)) 22)
      _ = 2 ^ 162 * 2 ^ (d * 22) := by rw [pow_mul]
      _ = 2 ^ (162 + d * 22) := by rw [pow_add]
      _ = 2 ^ (162 + 22 * d) := by rw [mul_comm d 22]
  have h3 : 2 ^ triBvQ d ≤ 2 ^ (162 + 22 * d) := le_trans h h2
  exact (Nat.pow_le_pow_iff_right Nat.one_lt_two).mp h3

theorem AdversarialBco.Bit.TriM.triLh_le_lin {d : ℕ} (hd : 1 ≤ d) : triLh (triSQ d) ≤ 42 + 6 * d := by
  have h_pow := pow_triLh_le hd
  have h_lt : d < 2 ^ d := Nat.lt_two_pow_self
  have h_pow6 : d ^ 6 ≤ (2 ^ d) ^ 6 := Nat.pow_le_pow_left (Nat.le_of_lt h_lt) 6
  have h_eq : 2 ^ 42 * (2 ^ d) ^ 6 = 2 ^ (42 + 6 * d) := by
    calc
      2 ^ 42 * (2 ^ d) ^ 6 = 2 ^ 42 * 2 ^ (d * 6) := by rw [pow_mul]
      _ = 2 ^ 42 * 2 ^ (6 * d) := by rw [mul_comm d 6]
      _ = 2 ^ (42 + 6 * d) := by rw [pow_add]
  have h_total : 2 ^ triLh (triSQ d) ≤ 2 ^ (42 + 6 * d) := by
    calc
      2 ^ triLh (triSQ d) ≤ 2 ^ 42 * d ^ 6 := h_pow
      _ ≤ 2 ^ 42 * (2 ^ d) ^ 6 := Nat.mul_le_mul_left _ h_pow6
      _ = 2 ^ (42 + 6 * d) := h_eq
  have h_two_gt_one : 1 < 2 := by norm_num
  exact ((Nat.pow_le_pow_iff_right h_two_gt_one).mp h_total)

theorem AdversarialBco.Bit.TriM.guN_le11 {d : ℕ} (hd : 1 ≤ d) : guN d ≤ 2 ^ 81 * d ^ 11 := by
  unfold guN
  have hKg := triKgQ_le hd
  have hpJa := pow_triJaQ_le hd
  have hdpos : 0 < d := by omega
  have hd11 : 1 ≤ d ^ 11 := by
    have h := Nat.pow_le_pow_left hd 11
    omega
  have h_sq : 8 * d * triKgQ d ≤ (2 ^ 79 * d ^ 11) ^ 2 := by
    calc
      8 * d * triKgQ d ≤ 8 * d * (2 ^ 154 * d ^ 21) := Nat.mul_le_mul_left (8 * d) hKg
      _ = 2 ^ 157 * d ^ 22 := by ring
      _ ≤ 2 ^ 158 * d ^ 22 := Nat.mul_le_mul_right (d ^ 22) (by norm_num : 2 ^ 157 ≤ 2 ^ 158)
      _ = (2 ^ 79 * d ^ 11) ^ 2 := by ring
  have h_sqrt : Nat.sqrt (8 * d * triKgQ d) ≤ 2 ^ 79 * d ^ 11 := by
    calc
      Nat.sqrt (8 * d * triKgQ d) ≤ Nat.sqrt ((2 ^ 79 * d ^ 11) ^ 2) := Nat.sqrt_le_sqrt h_sq
      _ = 2 ^ 79 * d ^ 11 := by rw [Nat.sqrt_eq']
  have h_ja : 2 ^ (triJaQ d - 3) ≤ 2 ^ 11 * d ^ 11 := by
    calc
      2 ^ (triJaQ d - 3) ≤ 2 ^ triJaQ d :=
        Nat.pow_le_pow_right (by norm_num) (Nat.sub_le (triJaQ d) 3)
      _ ≤ 2 ^ 11 * d ^ 2 := hpJa
      _ ≤ 2 ^ 11 * d ^ 11 := Nat.mul_le_mul_left (2 ^ 11) (Nat.pow_le_pow_right hdpos (by omega))
  have h_sum : Nat.sqrt (8 * d * triKgQ d) + 2 + 2 ^ (triJaQ d - 3) ≤ 2 ^ 81 * d ^ 11 := by
    have h_add : Nat.sqrt (8 * d * triKgQ d) + 2 + 2 ^ (triJaQ d - 3) ≤
        (2 ^ 79 * d ^ 11) + 2 + (2 ^ 11 * d ^ 11) := by
      omega
    have h_bound : (2 ^ 79 * d ^ 11) + 2 + (2 ^ 11 * d ^ 11) ≤ 2 ^ 81 * d ^ 11 := by
      have h1 : (2 ^ 79 * d ^ 11) + (2 ^ 11 * d ^ 11) ≤ 2 ^ 80 * d ^ 11 := by
        have : 2 ^ 79 + 2 ^ 11 ≤ 2 ^ 80 := by
          have h : 2 ^ 11 ≤ 2 ^ 79 := Nat.pow_le_pow_right (by norm_num) (by omega)
          omega
        calc
          (2 ^ 79 * d ^ 11) + (2 ^ 11 * d ^ 11) = (2 ^ 79 + 2 ^ 11) * d ^ 11 := by ring
          _ ≤ 2 ^ 80 * d ^ 11 := Nat.mul_le_mul_right (d ^ 11) this
      have h2 : 2 ≤ 2 * d ^ 11 := by
        have : 1 ≤ d ^ 11 := hd11
        omega
      omega
    omega
  exact h_sum

theorem AdversarialBco.Bit.TriM.gbN_le {d : ℕ} (hd : 1 ≤ d) : gbN d ≤ 2 ^ 244 * d ^ 33 := by
  have hguN_le : guN d ≤ 2 ^ 81 * d ^ 11 := guN_le11 hd
  have hpow_le : 2 ^ triBvQ d ≤ 2 ^ 162 * d ^ 22 := pow_triBvQ_le hd
  have hprod_le : guN d * 2 ^ triBvQ d ≤ (2 ^ 81 * d ^ 11) * (2 ^ 162 * d ^ 22) :=
    Nat.mul_le_mul hguN_le hpow_le
  have hprod_simp : (2 ^ 81 * d ^ 11) * (2 ^ 162 * d ^ 22) = 2 ^ 243 * d ^ 33 := by
    ring
  rw [hprod_simp] at hprod_le
  have h_two_d_le : 2 * d ≤ 2 ^ 243 * d ^ 33 := by
    calc
      2 * d = 2 ^ 1 * d ^ 1 := by simp
      _ ≤ 2 ^ 243 * d ^ 33 :=
        Nat.mul_le_mul (Nat.pow_le_pow_right (by omega) (by omega)) (Nat.pow_le_pow_right hd (by omega))
  have h_d_plus_one_le : d + 1 ≤ 2 ^ 243 * d ^ 33 := by
    calc
      d + 1 ≤ d + d := Nat.add_le_add_left hd d
      _ = 2 * d := by ring
      _ ≤ 2 ^ 243 * d ^ 33 := h_two_d_le
  unfold gbN
  calc
    guN d * 2 ^ triBvQ d + d + 1 = (guN d * 2 ^ triBvQ d) + (d + 1) := by ring
    _ ≤ (2 ^ 243 * d ^ 33) + (d + 1) := Nat.add_le_add_right hprod_le (d + 1)
    _ ≤ (2 ^ 243 * d ^ 33) + (2 ^ 243 * d ^ 33) := Nat.add_le_add_left h_d_plus_one_le _
    _ = 2 * (2 ^ 243 * d ^ 33) := by ring
    _ = 2 ^ 244 * d ^ 33 := by ring

theorem AdversarialBco.Bit.TriM.tzP_le {d : ℕ} (hd : 1 ≤ d) : tzP d ≤ 2 ^ 158 * d ^ 21 := by
  have hkg := AdversarialBco.Bit.TriM.triKgQ_le hd
  have htzP : tzP d = triBgQ d + 2 * Nat.size (triBgQ d) + 4 := rfl
  have hbg : triBgQ d = 4 * triKgQ d := rfl
  rw [htzP, hbg]
  have hsize : Nat.size (4 * triKgQ d) ≤ 4 * triKgQ d := by
    rw [Nat.size_le]
    exact Nat.lt_two_pow_self (n := 4 * triKgQ d)
  have hineq1 : 4 * triKgQ d + 2 * Nat.size (4 * triKgQ d) + 4 ≤ 12 * triKgQ d + 4 := by
    have : 2 * Nat.size (4 * triKgQ d) ≤ 2 * (4 * triKgQ d) := Nat.mul_le_mul_left _ hsize
    omega
  have hineq2 : 12 * triKgQ d + 4 ≤ 14 * triKgQ d := by
    have h2 : 2 ≤ triKgQ d := le_max_left _ _
    omega
  have hineq3 : 14 * triKgQ d ≤ 14 * (2 ^ 154 * d ^ 21) :=
    Nat.mul_le_mul_left _ hkg
  have hineq4 : 14 * (2 ^ 154 * d ^ 21) ≤ 2 ^ 158 * d ^ 21 := by
    calc
      14 * (2 ^ 154 * d ^ 21) = (14 * 2 ^ 154) * d ^ 21 := by ring
      _ ≤ (16 * 2 ^ 154) * d ^ 21 := Nat.mul_le_mul_right _ (by norm_num)
      _ = 2 ^ 4 * 2 ^ 154 * d ^ 21 := by norm_num
      _ = 2 ^ 158 * d ^ 21 := by ring
  exact le_trans hineq1 (le_trans hineq2 (le_trans hineq3 hineq4))

theorem AdversarialBco.Bit.TriM.triLa_le_lin {d : ℕ} (hd : 1 ≤ d) : triLa (triSQ d) ≤ 32 + 4 * d := by
  have h4 : d ^ 4 ≤ (2 ^ d) ^ 4 := Nat.pow_le_pow_left Nat.lt_two_pow_self.le 4
  have h : 2 ^ triLa (triSQ d) ≤ 2 ^ (32 + 4 * d) :=
    calc 2 ^ triLa (triSQ d) ≤ 2 ^ 32 * d ^ 4 := pow_triLa_le hd
      _ ≤ 2 ^ 32 * (2 ^ d) ^ 4 := Nat.mul_le_mul_left _ h4
      _ = 2 ^ (32 + 4 * d) := by rw [← pow_mul, ← pow_add, mul_comm d 4]
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h

set_option exponentiation.threshold 1000 in
theorem AdversarialBco.Bit.TriM.pow_triNeQ_le {d : ℕ} (hd : 1 ≤ d) (ℓ : ℕ) :
    2 ^ triNeQ d ℓ ≤ 2 ^ 1000 * d ^ 200 * (ℓ + 1) := by
  have h2pos : 1 < 2 := by norm_num
  have hneDpos : 0 < neD d := by
    unfold neD
    positivity
  rw [triNeQ_eq hd ℓ]
  set N := neN d ℓ with hN
  set D := neD d with hD
  have hD1 : 1 ≤ D := by
    rw [hD]
    unfold neD
    have hpos : 0 < 9 * 4 ^ (triBvQ d + triJaQ d) * 400000000 := by positivity
    omega
  have hx_le_N : (N + D - 1) / D ≤ N := by
    by_cases hN0 : N = 0
    · rw [hN0]
      have hdiv : (0 + D - 1) / D = 0 := Nat.div_eq_of_lt (by omega)
      rw [hdiv]
    · have hNpos : 1 ≤ N := Nat.one_le_of_lt (Nat.pos_of_ne_zero hN0)
      have h_mul : N ≤ N * D := by
        refine le_trans ?_ (Nat.mul_le_mul_left N hD1)
        simp
      have h_lt : N + D - 1 < (N + 1) * D := by
        have h_eq : (N + 1) * D = N * D + D := by ring
        rw [h_eq]
        have h1 : N + D - 1 < N + D := by omega
        have h2 : N + D ≤ N * D + D := Nat.add_le_add_right h_mul D
        omega
      have h_div_lt : (N + D - 1) / D < N + 1 :=
        (Nat.div_lt_iff_lt_mul hneDpos).mpr h_lt
      omega
  have h_pow_clog : 2 ^ Nat.clog 2 ((N + D - 1) / D) ≤ 2 * ((N + D - 1) / D) + 1 := by
    by_cases hx0 : (N + D - 1) / D = 0
    · rw [hx0]; norm_num
    · have hxpos : 1 ≤ (N + D - 1) / D := Nat.one_le_of_lt (Nat.pos_of_ne_zero hx0)
      by_cases hx1 : (N + D - 1) / D = 1
      · rw [hx1]; norm_num
      · have hx_gt1 : 1 < (N + D - 1) / D := by omega
        have h := Nat.pow_pred_clog_lt_self h2pos hx_gt1
        have hpos_clog : 0 < Nat.clog 2 ((N + D - 1) / D) := Nat.clog_pos h2pos hx_gt1
        have h' : 2 ^ Nat.clog 2 ((N + D - 1) / D) < 2 * ((N + D - 1) / D) := by
          calc
            2 ^ Nat.clog 2 ((N + D - 1) / D) =
                2 ^ ((Nat.clog 2 ((N + D - 1) / D)).pred.succ) := by
              rw [Nat.succ_pred_eq_of_pos hpos_clog]
            _ = 2 ^ (Nat.clog 2 ((N + D - 1) / D)).pred * 2 := by rw [Nat.pow_succ]
            _ = 2 * 2 ^ (Nat.clog 2 ((N + D - 1) / D)).pred := by ring
            _ < 2 * ((N + D - 1) / D) := Nat.mul_lt_mul_of_pos_left h (by norm_num)
        omega
  have h_neN_bound : N ≤ 2 ^ 809 * d ^ 108 * (ℓ + 1) := by
    rw [hN]
    unfold neN
    have h_d2N : d2N d ≤ 2 ^ 90 * d ^ 14 := d2N_le hd
    have h_eloI : eloI d ≤ 2 ^ 112 * d ^ 14 := eloI_le hd
    have h_gbN : gbN d ≤ 2 ^ 244 * d ^ 33 := gbN_le hd
    have h_guN : guN d ≤ 2 ^ 81 * d ^ 11 := guN_le11 hd
    have h_pow_triBvQ : 2 ^ triBvQ d ≤ 2 ^ 162 * d ^ 22 := pow_triBvQ_le hd
    -- 4 ^ triBvQ d ≤ 2 ^ 324 * d ^ 44
    have h_4powBvQ : 4 ^ triBvQ d ≤ 2 ^ 324 * d ^ 44 := by
      calc
        4 ^ triBvQ d = (2 ^ 2) ^ triBvQ d := by norm_num
        _ = (2 ^ triBvQ d) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]
        _ ≤ (2 ^ 162 * d ^ 22) ^ 2 := Nat.pow_le_pow_left h_pow_triBvQ 2
        _ = (2 ^ 162) ^ 2 * (d ^ 22) ^ 2 := by rw [mul_pow]
        _ = 2 ^ (162 * 2) * d ^ (22 * 2) := by rw [pow_mul, pow_mul]
        _ = 2 ^ 324 * d ^ 44 := by norm_num
    have h_sq_eloI : eloI d ^ 2 ≤ (2 ^ 112 * d ^ 14) ^ 2 := Nat.pow_le_pow_left h_eloI 2
    have h_sq_gbN : gbN d ^ 2 ≤ (2 ^ 244 * d ^ 33) ^ 2 := Nat.pow_le_pow_left h_gbN 2
    have h_sq_guN : guN d ^ 2 ≤ (2 ^ 81 * d ^ 11) ^ 2 := Nat.pow_le_pow_left h_guN 2
    -- 8 * d2N d * eloI d ^ 2 ≤ 2 ^ 317 * d ^ 42
    have h_term1 : 8 * d2N d * eloI d ^ 2 ≤ 2 ^ 317 * d ^ 42 := by
      calc
        8 * d2N d * eloI d ^ 2 ≤ 8 * (2 ^ 90 * d ^ 14) * (2 ^ 112 * d ^ 14) ^ 2 :=
          Nat.mul_le_mul (Nat.mul_le_mul_left 8 h_d2N) h_sq_eloI
        _ = 8 * (2 ^ 90 * d ^ 14) * ((2 ^ 112) ^ 2 * (d ^ 14) ^ 2) := by rw [mul_pow]
        _ = (8 * 2 ^ 90 * (2 ^ 112) ^ 2) * (d ^ 14 * (d ^ 14) ^ 2) := by ring
        _ = (2 ^ 3 * 2 ^ 90 * 2 ^ (112 * 2)) * d ^ (14 * 3) := by
          rw [pow_mul, pow_mul]; ring
        _ = (2 ^ (3 + 90 + 224)) * d ^ 42 := by norm_num
        _ = 2 ^ 317 * d ^ 42 := by norm_num
    -- 9 * gbN d ^ 2 ≤ 2 ^ 492 * d ^ 66
    have h_term2 : 9 * gbN d ^ 2 ≤ 2 ^ 492 * d ^ 66 := by
      calc
        9 * gbN d ^ 2 ≤ 9 * (2 ^ 244 * d ^ 33) ^ 2 := Nat.mul_le_mul_left 9 h_sq_gbN
        _ = 9 * ((2 ^ 244) ^ 2 * (d ^ 33) ^ 2) := by rw [mul_pow]
        _ = (9 * (2 ^ 244) ^ 2) * (d ^ 33) ^ 2 := by ring
        _ = (9 * 2 ^ (244 * 2)) * d ^ (33 * 2) := by rw [pow_mul, pow_mul]
        _ = (9 * 2 ^ 488) * d ^ 66 := by norm_num
        _ ≤ (2 ^ 4 * 2 ^ 488) * d ^ 66 := Nat.mul_le_mul (by norm_num) (by rfl)
        _ = 2 ^ (4 + 488) * d ^ 66 := by rw [pow_add]
        _ = 2 ^ 492 * d ^ 66 := by norm_num
    -- 8 * guN d ^ 2 * ℓ * 4 ^ triBvQ d ≤ 2 ^ 489 * d ^ 66 * ℓ
    have h_term3 : 8 * guN d ^ 2 * ℓ * 4 ^ triBvQ d ≤ 2 ^ 489 * d ^ 66 * ℓ := by
      calc
        8 * guN d ^ 2 * ℓ * 4 ^ triBvQ d ≤
            (8 * (2 ^ 81 * d ^ 11) ^ 2) * ℓ * (2 ^ 324 * d ^ 44) := by
          have h_left : 8 * guN d ^ 2 ≤ 8 * (2 ^ 81 * d ^ 11) ^ 2 :=
            Nat.mul_le_mul_left 8 h_sq_guN
          have h_mul : 8 * guN d ^ 2 * ℓ ≤ (8 * (2 ^ 81 * d ^ 11) ^ 2) * ℓ :=
            Nat.mul_le_mul h_left (by rfl)
          exact Nat.mul_le_mul h_mul h_4powBvQ
        _ = (8 * ((2 ^ 81) ^ 2 * (d ^ 11) ^ 2)) * ℓ * (2 ^ 324 * d ^ 44) := by rw [mul_pow]
        _ = (8 * 2 ^ (81 * 2) * d ^ (11 * 2)) * ℓ * (2 ^ 324 * d ^ 44) := by
          rw [pow_mul, pow_mul]; ring
        _ = (8 * 2 ^ 162 * d ^ 22) * ℓ * (2 ^ 324 * d ^ 44) := by norm_num
        _ = 8 * 2 ^ 162 * d ^ 22 * ℓ * 2 ^ 324 * d ^ 44 := by ring
        _ = 8 * (2 ^ 162 * 2 ^ 324) * (d ^ 22 * d ^ 44) * ℓ := by ring
        _ = 8 * 2 ^ (162 + 324) * d ^ (22 + 44) * ℓ := by rw [pow_add, pow_add]
        _ = 8 * 2 ^ 486 * d ^ 66 * ℓ := by norm_num
        _ = 2 ^ 3 * 2 ^ 486 * d ^ 66 * ℓ := by norm_num
        _ = 2 ^ (3 + 486) * d ^ 66 * ℓ := by rw [pow_add]
        _ = 2 ^ 489 * d ^ 66 * ℓ := by norm_num
    have h_sum : 9 * gbN d ^ 2 + 8 * guN d ^ 2 * ℓ * 4 ^ triBvQ d ≤ 2 ^ 492 * d ^ 66 * (ℓ + 1) := by
      have hsum : 9 * gbN d ^ 2 + 8 * guN d ^ 2 * ℓ * 4 ^ triBvQ d ≤
          2 ^ 492 * d ^ 66 + 2 ^ 489 * d ^ 66 * ℓ :=
        add_le_add h_term2 h_term3
      have hineq : 2 ^ 492 * d ^ 66 + 2 ^ 489 * d ^ 66 * ℓ ≤ 2 ^ 492 * d ^ 66 * (ℓ + 1) := by
        have h_eq : 2 ^ 492 = 8 * 2 ^ 489 := by
          calc
            2 ^ 492 = 2 ^ (489 + 3) := by ring
            _ = 2 ^ 489 * 2 ^ 3 := by rw [pow_add]
            _ = 2 ^ 489 * 8 := by norm_num
            _ = 8 * 2 ^ 489 := by ring
        rw [h_eq]
        have h_factor : 8 + ℓ ≤ 8 * ℓ + 8 := by omega
        calc
          8 * 2 ^ 489 * d ^ 66 + 2 ^ 489 * d ^ 66 * ℓ = (2 ^ 489 * d ^ 66) * 8 + (2 ^ 489 * d ^ 66) * ℓ := by ring
          _ = (2 ^ 489 * d ^ 66) * (8 + ℓ) := by rw [Nat.mul_add]
          _ ≤ (2 ^ 489 * d ^ 66) * (8 * ℓ + 8) := Nat.mul_le_mul_left _ h_factor
          _ = (2 ^ 489 * d ^ 66) * (8 * (ℓ + 1)) := by ring
          _ = 8 * 2 ^ 489 * d ^ 66 * (ℓ + 1) := by ring
      exact le_trans hsum hineq
    calc
      8 * d2N d * eloI d ^ 2 * (9 * gbN d ^ 2 + 8 * guN d ^ 2 * ℓ * 4 ^ triBvQ d) ≤
          (2 ^ 317 * d ^ 42) * (2 ^ 492 * d ^ 66 * (ℓ + 1)) :=
        Nat.mul_le_mul h_term1 h_sum
      _ = (2 ^ 317 * 2 ^ 492) * (d ^ 42 * d ^ 66) * (ℓ + 1) := by ring
      _ = 2 ^ (317 + 492) * d ^ (42 + 66) * (ℓ + 1) := by rw [pow_add, pow_add]
      _ = 2 ^ 809 * d ^ 108 * (ℓ + 1) := by norm_num
  have h_final : 2 * N + 1 ≤ 2 ^ 1000 * d ^ 200 * (ℓ + 1) := by
    have h_mul : 2 * N ≤ 2 * (2 ^ 809 * d ^ 108 * (ℓ + 1)) :=
      Nat.mul_le_mul_left 2 h_neN_bound
    have h_dpow : d ^ 108 ≤ d ^ 200 := Nat.pow_le_pow_right hd (by omega)
    have h_pow_eq : 2 * 2 ^ 809 = 2 ^ 810 := by
      calc
        2 * 2 ^ 809 = 2 ^ 809 * 2 := by ring
        _ = 2 ^ 810 := by rw [← pow_succ]
    have h_main : 2 * (2 ^ 809 * d ^ 108 * (ℓ + 1)) ≤ 2 ^ 810 * d ^ 200 * (ℓ + 1) := by
      calc
        2 * (2 ^ 809 * d ^ 108 * (ℓ + 1)) = (2 * 2 ^ 809) * d ^ 108 * (ℓ + 1) := by ring
        _ = 2 ^ 810 * d ^ 108 * (ℓ + 1) := by rw [h_pow_eq]
        _ ≤ 2 ^ 810 * d ^ 200 * (ℓ + 1) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ h_dpow) (by rfl)
    have h_one : 1 ≤ 2 ^ 1000 * d ^ 200 * (ℓ + 1) := by
      have hpos2 : 0 < 2 ^ 1000 := by positivity
      have hpos_d : 0 < d ^ 200 := pow_pos (Nat.pos_of_ne_zero (by omega)) 200
      have hpos_l : 0 < ℓ + 1 := Nat.succ_pos _
      have : 0 < 2 ^ 1000 * d ^ 200 * (ℓ + 1) := by positivity
      omega
    have h_ineq : 2 * N + 1 ≤ 2 ^ 810 * d ^ 200 * (ℓ + 1) + 1 := by
      have : 2 * N ≤ 2 ^ 810 * d ^ 200 * (ℓ + 1) := le_trans h_mul h_main
      omega
    have h_ineq2 : 2 ^ 810 * d ^ 200 * (ℓ + 1) + 1 ≤ 2 ^ 1000 * d ^ 200 * (ℓ + 1) := by
      have hM : 1 ≤ d ^ 200 * (ℓ + 1) := by
        have hd200 : 1 ≤ d ^ 200 := Nat.one_le_pow _ _ hd
        have h_l1 : 1 ≤ ℓ + 1 := Nat.succ_pos _
        exact calc
          1 = 1 * 1 := by simp
          _ ≤ d ^ 200 * (ℓ + 1) := Nat.mul_le_mul hd200 h_l1
      have h_pow_add : 2 ^ 810 + 1 ≤ 2 ^ 1000 := by
        have : 2 ^ 810 + 1 ≤ 2 ^ 810 + 2 ^ 810 := by
          have hpos : 0 < 2 ^ 810 := by positivity
          omega
        have hsum : 2 ^ 810 + 2 ^ 810 = 2 ^ 811 := by
          rw [← two_mul, ← pow_succ']
        rw [hsum] at this
        have : 2 ^ 811 ≤ 2 ^ 1000 := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      calc
        2 ^ 810 * d ^ 200 * (ℓ + 1) + 1 ≤
            2 ^ 810 * d ^ 200 * (ℓ + 1) + d ^ 200 * (ℓ + 1) := by omega
        _ = (2 ^ 810 + 1) * d ^ 200 * (ℓ + 1) := by ring
        _ ≤ 2 ^ 1000 * d ^ 200 * (ℓ + 1) := by
          have h := Nat.mul_le_mul_right (d ^ 200 * (ℓ + 1)) h_pow_add
          simpa [mul_assoc] using h
    omega
  calc
    2 ^ Nat.clog 2 ((N + D - 1) / D) ≤ 2 * ((N + D - 1) / D) + 1 := h_pow_clog
    _ ≤ 2 * N + 1 := by
      have : 2 * ((N + D - 1) / D) ≤ 2 * N := Nat.mul_le_mul_left 2 hx_le_N
      omega
    _ ≤ 2 ^ 1000 * d ^ 200 * (ℓ + 1) := h_final

set_option exponentiation.threshold 1100 in
theorem AdversarialBco.Bit.TriM.triNeQ_le_lin {d : ℕ} (hd : 1 ≤ d) (ℓ : ℕ) : triNeQ d ℓ ≤ 1000 + 200 * d + ℓ := by
  have h_pow := pow_triNeQ_le hd ℓ
  have hd_lt : d < 2 ^ d := Nat.lt_two_pow_self (n := d)
  have hd_pow : d ^ 200 ≤ 2 ^ (200 * d) := by
    calc
      d ^ 200 ≤ (2 ^ d) ^ 200 := Nat.pow_le_pow_left (Nat.le_of_lt hd_lt) 200
      _ = 2 ^ (d * 200) := by rw [← pow_mul]
      _ = 2 ^ (200 * d) := by rw [mul_comm]
  have hℓ_le : ℓ + 1 ≤ 2 ^ ℓ := by
    have hℓ_lt : ℓ < 2 ^ ℓ := Nat.lt_two_pow_self (n := ℓ)
    omega
  have h_rhs : 2 ^ 1000 * d ^ 200 * (ℓ + 1) ≤ 2 ^ (1000 + 200 * d + ℓ) := by
    calc
      2 ^ 1000 * d ^ 200 * (ℓ + 1) ≤ 2 ^ 1000 * (2 ^ (200 * d)) * (ℓ + 1) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ hd_pow) (le_refl _)
      _ = 2 ^ 1000 * 2 ^ (200 * d) * (ℓ + 1) := rfl
      _ ≤ 2 ^ 1000 * 2 ^ (200 * d) * 2 ^ ℓ :=
        Nat.mul_le_mul (le_refl _) hℓ_le
      _ = 2 ^ (1000 + 200 * d) * 2 ^ ℓ := by rw [← pow_add]
      _ = 2 ^ ((1000 + 200 * d) + ℓ) := by rw [← pow_add]
      _ = 2 ^ (1000 + 200 * d + ℓ) := by ring
  have h_total : 2 ^ triNeQ d ℓ ≤ 2 ^ (1000 + 200 * d + ℓ) :=
    le_trans h_pow h_rhs
  have h_two_gt_one : 1 < 2 := by norm_num
  exact (Nat.pow_le_pow_iff_right h_two_gt_one).mp h_total

theorem AdversarialBco.Bit.TriM.triJsQ_le_lin {d : ℕ} (hd : 1 ≤ d) (ℓ : ℕ) :
    triJsQ d ℓ ≤ 2000 + 300 * d + ℓ := by
  have h4 : 1 < 2 := by norm_num
  have h_pow := pow_triJsQ_le hd ℓ
  have h_gbN := gbN_le hd
  have h_jaQ := pow_triJaQ_le hd
  have h_neQ := triNeQ_le_lin hd ℓ
  have h_d_le : d ≤ 2 ^ d := Nat.le_of_lt Nat.lt_two_pow_self
  have h_d33_le : d ^ 33 ≤ 2 ^ (33 * d) := by
    calc
      d ^ 33 ≤ (2 ^ d) ^ 33 := Nat.pow_le_pow_left h_d_le 33
      _ = 2 ^ (d * 33) := by rw [Nat.pow_mul]
      _ = 2 ^ (33 * d) := by rw [mul_comm]
  have h_d2_le : d ^ 2 ≤ 2 ^ (2 * d) := by
    calc
      d ^ 2 ≤ (2 ^ d) ^ 2 := Nat.pow_le_pow_left h_d_le 2
      _ = 2 ^ (d * 2) := by rw [Nat.pow_mul]
      _ = 2 ^ (2 * d) := by rw [mul_comm]
  have h_bound1 : 2 * gbN d * 2 ^ triNeQ d ℓ * 2 ^ triJaQ d ≤ 2 ^ (256 + 35 * d + triNeQ d ℓ) := by
    calc
      2 * gbN d * 2 ^ triNeQ d ℓ * 2 ^ triJaQ d
          ≤ 2 * (2 ^ 244 * d ^ 33) * 2 ^ triNeQ d ℓ * (2 ^ 11 * d ^ 2) := by
        have h_gbN' : 2 * gbN d ≤ 2 * (2 ^ 244 * d ^ 33) := by omega
        have h_jaQ' : 2 ^ triJaQ d ≤ 2 ^ 11 * d ^ 2 := h_jaQ
        have h1 : (2 * gbN d) * 2 ^ triNeQ d ℓ ≤ (2 * (2 ^ 244 * d ^ 33)) * 2 ^ triNeQ d ℓ :=
          Nat.mul_le_mul h_gbN' (Nat.le_refl _)
        exact Nat.mul_le_mul h1 h_jaQ'
      _ = 2 ^ (1 + 244 + 11) * d ^ (33 + 2) * 2 ^ triNeQ d ℓ := by
        ring
      _ = 2 ^ 256 * d ^ 35 * 2 ^ triNeQ d ℓ := by norm_num
      _ = 2 ^ 256 * (d ^ 33 * d ^ 2) * 2 ^ triNeQ d ℓ := by rw [← pow_add]
      _ ≤ 2 ^ 256 * (2 ^ (33 * d) * 2 ^ (2 * d)) * 2 ^ triNeQ d ℓ := by
        have h_inner : d ^ 33 * d ^ 2 ≤ 2 ^ (33 * d) * 2 ^ (2 * d) :=
          Nat.mul_le_mul h_d33_le h_d2_le
        have h_mid : 2 ^ 256 * (d ^ 33 * d ^ 2) ≤ 2 ^ 256 * (2 ^ (33 * d) * 2 ^ (2 * d)) :=
          Nat.mul_le_mul (Nat.le_refl _) h_inner
        exact Nat.mul_le_mul h_mid (Nat.le_refl _)
      _ = 2 ^ 256 * 2 ^ (33 * d + 2 * d) * 2 ^ triNeQ d ℓ := by rw [pow_add]
      _ = 2 ^ 256 * 2 ^ (35 * d) * 2 ^ triNeQ d ℓ := by ring
      _ = 2 ^ (256 + 35 * d) * 2 ^ triNeQ d ℓ := by rw [← pow_add]
      _ = 2 ^ ((256 + 35 * d) + triNeQ d ℓ) := by rw [← pow_add]
      _ = 2 ^ (256 + 35 * d + triNeQ d ℓ) := by rw [add_assoc]
  have h_bound2 : 2 ^ (256 + 35 * d + triNeQ d ℓ) ≤ 2 ^ (2000 + 300 * d + ℓ) := by
    refine Nat.pow_le_pow_right (by norm_num) ?_
    have h_triNe : triNeQ d ℓ ≤ 1000 + 200 * d + ℓ := h_neQ
    omega
  have h_total : 2 ^ triJsQ d ℓ ≤ 2 ^ (2000 + 300 * d + ℓ) :=
    le_trans h_pow (le_trans h_bound1 h_bound2)
  exact ((Nat.pow_le_pow_iff_right h4).mp h_total)

theorem AdversarialBco.Bit.TriM.tzGc_le_lin {d : ℕ} (hd : 1 ≤ d) (ℓ : ℕ) :
    tzGc d ℓ ≤ 4000 + 600 * d + 2 * ℓ := by
  unfold tzGc tzG
  have h1 : triBvQ d ≤ 162 + 22 * d := triBvQ_le_lin hd
  have h2 : triJsQ d ℓ ≤ 2000 + 300 * d + ℓ := triJsQ_le_lin hd ℓ
  have h3 : triJaQ d ≤ 12 + 2 * d := triJaQ_le_lin hd
  have h4 : triNeQ d ℓ ≤ 1000 + 200 * d + ℓ := triNeQ_le_lin hd ℓ
  omega
