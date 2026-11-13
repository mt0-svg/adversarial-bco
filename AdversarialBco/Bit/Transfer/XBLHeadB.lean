/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XBLRt
public import AdversarialBco.Bit.Transfer.XBLR4

@[expose] public section

/-!
# Magnitudes of the head of BL's round

The numerators of R8 and R9 (`A'`, `B'`, `b'`, `k'`, `g`, `G'`, `ĝ·μ̂`, `l'`) at most a power of two from the
bounds `2^U` of their inputs, a grid numerator from the value, `(B Bᵀ) w`, `w_μ` from R13's test,
the units of R2 to R4.
-/

open AdversarialBco.Bit.Transfer.BLM Matrix

/-- R8: the numerator of `A'_ij`. -/
theorem AdversarialBco.Bit.Transfer.BLM.hb_Ap {d : ℕ} (a1 a2 Q G : ℤ) (Ah : Matrix (Fin d) (Fin d) ℤ)
    (Γ : Fin d → ℤ) (U E8 : ℕ) (h1 : |a1| ≤ 2 ^ E8) (h2 : |a2| ≤ 2 ^ E8) (hA : ∀ i j, |Ah i j| ≤ 2 ^ U)
    (hΓ : ∀ j, |Γ j| ≤ 2 ^ U) (hQ1 : 1 ≤ Q) (hQ : Q ≤ 2 ^ U) (hG1 : 1 ≤ G) (hG : G ≤ 2 ^ U) (hd : d ≤ 2 ^ U)
    (i j : Fin d) :
    |rndZ (a1 * Ah i j * (G * G) - a2 * (Ah *ᵥ Γ) i * Γ j) (Q * Q * (G * G)) Q| ≤ 2 ^ (E8 + 5 * U + 2) := by
  have hQ_nonneg : 0 ≤ Q := by linarith
  have hG_nonneg : 0 ≤ G := by linarith
  have hG_abs : |G| ≤ 2 ^ U := by
    rw [abs_of_nonneg hG_nonneg]
    exact hG
  have h_mulvec : |(Ah *ᵥ Γ) i| ≤ 2 ^ (U + U + U) := mulVec_abs_le hA hΓ hd i
  have h_term1 : |a1 * Ah i j * (G * G)| ≤ 2 ^ (E8 + U + U + U) := by
    have h_absG_sq : |G * G| ≤ (2 ^ U) * (2 ^ U) := by
      rw [abs_mul]
      have h_nonneg_G : 0 ≤ |G| := abs_nonneg _
      have h_nonneg_2U : 0 ≤ (2 : ℤ) ^ U := by positivity
      exact mul_le_mul hG_abs hG_abs h_nonneg_G h_nonneg_2U
    calc
      |a1 * Ah i j * (G * G)| = |a1| * (|Ah i j| * |G * G|) := by simp [abs_mul]; ring
      _ ≤ (2 ^ E8) * ((2 ^ U) * ((2 ^ U) * (2 ^ U))) := by
        apply mul_le_mul h1
        · apply mul_le_mul (hA i j) h_absG_sq
          · positivity
          · positivity
        · positivity
        · positivity
      _ = 2 ^ (E8 + U + U + U) := by ring
  have h_term2 : |a2 * (Ah *ᵥ Γ) i * Γ j| ≤ 2 ^ (E8 + (U + U + U) + U) := by
    calc
      |a2 * (Ah *ᵥ Γ) i * Γ j| = |a2| * (|(Ah *ᵥ Γ) i| * |Γ j|) := by simp [abs_mul]; ring
      _ ≤ (2 ^ E8) * ((2 ^ (U + U + U)) * (2 ^ U)) := by
        apply mul_le_mul h2
        · apply mul_le_mul h_mulvec (hΓ j)
          · positivity
          · positivity
        · positivity
        · positivity
      _ = 2 ^ (E8 + (U + U + U) + U) := by ring
  have h_term1_le : |a1 * Ah i j * (G * G)| ≤ 2 ^ (E8 + 4 * U) := by
    apply le_trans h_term1
    have h_exp : E8 + U + U + U ≤ E8 + 4 * U := by omega
    exact pow_le_pow_right₀ (by norm_num : 1 ≤ (2 : ℤ)) h_exp
  have h_term2_le : |a2 * (Ah *ᵥ Γ) i * Γ j| ≤ 2 ^ (E8 + 4 * U) := by
    apply le_trans h_term2
    have h_exp' : E8 + (U + U + U) + U ≤ E8 + 4 * U := by omega
    exact pow_le_pow_right₀ (by norm_num : 1 ≤ (2 : ℤ)) h_exp'
  have h_num : |a1 * Ah i j * (G * G) - a2 * (Ah *ᵥ Γ) i * Γ j| ≤ 2 ^ (E8 + 4 * U + 1) := by
    have h_abs_sub : |a1 * Ah i j * (G * G) - a2 * (Ah *ᵥ Γ) i * Γ j| ≤
        |a1 * Ah i j * (G * G)| + |a2 * (Ah *ᵥ Γ) i * Γ j| := abs_sub _ _
    have h_sum : |a1 * Ah i j * (G * G)| + |a2 * (Ah *ᵥ Γ) i * Γ j| ≤ 2 ^ (E8 + 4 * U) + 2 ^ (E8 + 4 * U) := by
      gcongr
    have h_pow_add : 2 ^ (E8 + 4 * U) + 2 ^ (E8 + 4 * U) = 2 ^ (E8 + 4 * U + 1) := by
      calc
        2 ^ (E8 + 4 * U) + 2 ^ (E8 + 4 * U) = 2 * 2 ^ (E8 + 4 * U) := by rw [two_mul]
        _ = 2 ^ (E8 + 4 * U) * 2 := by rw [mul_comm]
        _ = 2 ^ (E8 + 4 * U + 1) := by rw [pow_succ]
    linarith
  have h_denom_nonneg : 1 ≤ Q * Q * (G * G) := by
    have hQQ : 1 ≤ Q * Q := by
      nlinarith
    nlinarith
  have h_result := rndZ_abs_pow (a1 * Ah i j * (G * G) - a2 * (Ah *ᵥ Γ) i * Γ j) (Q * Q * (G * G)) Q
    (E8 + 4 * U + 1) U h_denom_nonneg hQ_nonneg h_num hQ
  have h_exp_eq : (E8 + 4 * U + 1) + U + 1 = E8 + 5 * U + 2 := by omega
  rw [h_exp_eq] at h_result
  exact h_result

/-- R8: the numerator of `B'_ij`. -/
theorem AdversarialBco.Bit.Transfer.BLM.hb_Bp {d : ℕ} (a3 a4 Q G : ℤ) (Bh : Matrix (Fin d) (Fin d) ℤ)
    (Γ : Fin d → ℤ) (U E8 : ℕ) (h3 : |a3| ≤ 2 ^ E8) (h4 : |a4| ≤ 2 ^ E8) (hB : ∀ i j, |Bh i j| ≤ 2 ^ U)
    (hΓ : ∀ j, |Γ j| ≤ 2 ^ U) (hQ1 : 1 ≤ Q) (hQ : Q ≤ 2 ^ U) (hG1 : 1 ≤ G) (hG : G ≤ 2 ^ U) (hd : d ≤ 2 ^ U)
    (i j : Fin d) :
    |rndZ (a3 * Bh i j * (G * G) + a4 * (Bh *ᵥ Γ) i * Γ j) (Q * Q * (G * G)) Q| ≤ 2 ^ (E8 + 5 * U + 2) := by
  have hQ_nonneg : 0 ≤ Q := by linarith
  have hG_nonneg : 0 ≤ G := by linarith
  have h_two_nonneg : 0 ≤ (2 : ℤ) := by norm_num
  have h_two_pos : (1 : ℤ) ≤ 2 := by norm_num
  have hQ_abs : |Q| ≤ (2 : ℤ) ^ U := by
    rw [abs_of_nonneg hQ_nonneg]
    exact hQ
  have hG_abs : |G| ≤ (2 : ℤ) ^ U := by
    rw [abs_of_nonneg hG_nonneg]
    exact hG
  have hG_sq : |G * G| ≤ (2 : ℤ) ^ (U + U) := by
    calc
      |G * G| = |G| * |G| := abs_mul G G
      _ ≤ ((2 : ℤ) ^ U) * ((2 : ℤ) ^ U) :=
        mul_le_mul hG_abs hG_abs (abs_nonneg _) (pow_nonneg h_two_nonneg U)
      _ = (2 : ℤ) ^ (U + U) := by rw [pow_add]
  have h_mulVec : |(Bh *ᵥ Γ) i| ≤ (2 : ℤ) ^ (U + U + U) :=
    mulVec_abs_le hB hΓ hd i
  have h_term1 : |a3 * Bh i j * (G * G)| ≤ (2 : ℤ) ^ (E8 + 3 * U) := by
    calc
      |a3 * Bh i j * (G * G)| = |a3| * |Bh i j| * |G * G| := by simp [abs_mul]
      _ = |a3| * |Bh i j| * (|G| * |G|) := by rw [abs_mul]
      _ ≤ ((2 : ℤ) ^ E8) * ((2 : ℤ) ^ U) * (((2 : ℤ) ^ U) * ((2 : ℤ) ^ U)) := by
        have h_prod1 : |a3| * |Bh i j| ≤ ((2 : ℤ) ^ E8) * ((2 : ℤ) ^ U) :=
          mul_le_mul h3 (hB i j) (abs_nonneg _) (pow_nonneg h_two_nonneg E8)
        have h_prod2 : |G| * |G| ≤ ((2 : ℤ) ^ U) * ((2 : ℤ) ^ U) :=
          mul_le_mul hG_abs hG_abs (abs_nonneg _) (pow_nonneg h_two_nonneg U)
        have h_nonneg1 : 0 ≤ |G| * |G| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
        have h_nonneg2 : 0 ≤ ((2 : ℤ) ^ E8) * ((2 : ℤ) ^ U) :=
          mul_nonneg (pow_nonneg h_two_nonneg E8) (pow_nonneg h_two_nonneg U)
        exact mul_le_mul h_prod1 h_prod2 h_nonneg1 h_nonneg2
      _ = (2 : ℤ) ^ (E8 + 3 * U) := by
        simp [pow_add]
        ring
  have h_term2 : |a4 * (Bh *ᵥ Γ) i * Γ j| ≤ (2 : ℤ) ^ (E8 + 4 * U) := by
    calc
      |a4 * (Bh *ᵥ Γ) i * Γ j| = |a4| * |(Bh *ᵥ Γ) i| * |Γ j| := by simp [abs_mul]
      _ ≤ ((2 : ℤ) ^ E8) * ((2 : ℤ) ^ (U + U + U)) * ((2 : ℤ) ^ U) := by
        have h_prod1 : |a4| * |(Bh *ᵥ Γ) i| ≤ ((2 : ℤ) ^ E8) * ((2 : ℤ) ^ (U + U + U)) :=
          mul_le_mul h4 h_mulVec (abs_nonneg _) (pow_nonneg h_two_nonneg E8)
        have h_prod2 : |Γ j| ≤ (2 : ℤ) ^ U := hΓ j
        have h_nonneg1 : 0 ≤ |Γ j| := abs_nonneg _
        have h_nonneg2 : 0 ≤ ((2 : ℤ) ^ E8) * ((2 : ℤ) ^ (U + U + U)) :=
          mul_nonneg (pow_nonneg h_two_nonneg E8) (pow_nonneg h_two_nonneg (U + U + U))
        exact mul_le_mul h_prod1 h_prod2 h_nonneg1 h_nonneg2
      _ = (2 : ℤ) ^ (E8 + 4 * U) := by
        rw [pow_add, pow_add]
        ring
  have h_sum : |a3 * Bh i j * (G * G) + a4 * (Bh *ᵥ Γ) i * Γ j| ≤ (2 : ℤ) ^ (E8 + 4 * U + 1) := by
    calc
      |a3 * Bh i j * (G * G) + a4 * (Bh *ᵥ Γ) i * Γ j| ≤
          |a3 * Bh i j * (G * G)| + |a4 * (Bh *ᵥ Γ) i * Γ j| := abs_add_le _ _
      _ ≤ (2 : ℤ) ^ (E8 + 3 * U) + (2 : ℤ) ^ (E8 + 4 * U) := add_le_add h_term1 h_term2
      _ ≤ (2 : ℤ) ^ (E8 + 4 * U) + (2 : ℤ) ^ (E8 + 4 * U) := by
        have h_exp_le : E8 + 3 * U ≤ E8 + 4 * U := by omega
        have h_pow_le : (2 : ℤ) ^ (E8 + 3 * U) ≤ (2 : ℤ) ^ (E8 + 4 * U) :=
          pow_le_pow_right₀ h_two_pos h_exp_le
        nlinarith
      _ = 2 * (2 : ℤ) ^ (E8 + 4 * U) := by ring
      _ = (2 : ℤ) ^ (E8 + 4 * U) * 2 := by rw [mul_comm]
      _ = (2 : ℤ) ^ ((E8 + 4 * U) + 1) := by rw [pow_succ]
      _ = (2 : ℤ) ^ (E8 + 4 * U + 1) := by ring
  have hden_pos : 1 ≤ Q * Q * (G * G) := by
    have hQQ : 1 ≤ Q * Q := by nlinarith
    have hGG : 1 ≤ G * G := by nlinarith
    nlinarith
  have h_exp_eq : (E8 + 4 * U + 1) + U + 1 = E8 + 5 * U + 2 := by omega
  have h_goal : |rndZ (a3 * Bh i j * (G * G) + a4 * (Bh *ᵥ Γ) i * Γ j) (Q * Q * (G * G)) Q| ≤
      (2 : ℤ) ^ ((E8 + 4 * U + 1) + U + 1) :=
    rndZ_abs_pow (a3 * Bh i j * (G * G) + a4 * (Bh *ᵥ Γ) i * Γ j) (Q * Q * (G * G)) Q
      (E8 + 4 * U + 1) U hden_pos hQ_nonneg h_sum hQ
  simpa [h_exp_eq] using h_goal

/-- R9: the numerator of `g_j`. -/
theorem AdversarialBco.Bit.Transfer.BLM.hb_g {d : ℕ} (F Q G yh nh : ℤ) (Bh : Matrix (Fin d) (Fin d) ℤ)
    (Γ : Fin d → ℤ) (U : ℕ) (hF1 : 1 ≤ F) (hQ1 : 1 ≤ Q) (hQ : Q ≤ 2 ^ U) (hG1 : 1 ≤ G)
    (hy : |yh| ≤ 2 ^ (5 * U + 7)) (hn : |nh| ≤ 2 ^ U) (hB : ∀ i j, |Bh i j| ≤ 2 ^ U) (hΓ : ∀ j, |Γ j| ≤ 2 ^ U)
    (hd : d ≤ 2 ^ U) (j : Fin d) :
    |rndZ (yh * nh * (Bh *ᵥ Γ) j) (F * Q * Q * G) Q| ≤ 2 ^ (10 * U + 8) := by
  have hBh : |(Bh *ᵥ Γ) j| ≤ 2 ^ (U + U + U) := mulVec_abs_le hB hΓ hd j
  have hdenom : 1 ≤ F * Q * Q * G := by
    have hFpos : 0 ≤ F := by linarith
    have hQpos : 0 ≤ Q := by linarith
    have hGpos : 0 ≤ G := by linarith
    have h_one_nonneg : (0 : ℤ) ≤ 1 := by norm_num
    have hFQ : 1 ≤ F * Q :=
      calc
        (1 : ℤ) = (1 : ℤ) * 1 := by ring
        _ ≤ F * Q := mul_le_mul hF1 hQ1 h_one_nonneg hFpos
    have hFQpos : 0 ≤ F * Q := by
      -- F ≥ 0, Q ≥ 0, so F*Q ≥ 0
      exact mul_nonneg hFpos hQpos
    have hFQQ : 1 ≤ F * Q * Q :=
      calc
        (1 : ℤ) = 1 * 1 := by ring
        _ ≤ (F * Q) * Q := mul_le_mul hFQ hQ1 h_one_nonneg hFQpos
    have hFQQpos : 0 ≤ F * Q * Q := by
      exact mul_nonneg hFQpos hQpos
    calc
      (1 : ℤ) = 1 * 1 := by ring
      _ ≤ (F * Q * Q) * G := mul_le_mul hFQQ hG1 h_one_nonneg hFQQpos
  have hQnonneg : 0 ≤ Q := by linarith
  have hnum : |yh * nh * (Bh *ᵥ Γ) j| ≤ 2 ^ (9 * U + 7) := by
    have hy_nonneg : 0 ≤ |yh| := abs_nonneg _
    have hn_nonneg : 0 ≤ |nh| := abs_nonneg _
    have hB_nonneg : 0 ≤ |(Bh *ᵥ Γ) j| := abs_nonneg _
    have h2a_nonneg : (0 : ℤ) ≤ (2 : ℤ) ^ (5 * U + 7) := pow_nonneg (by norm_num) _
    have h2b_nonneg : (0 : ℤ) ≤ (2 : ℤ) ^ U := pow_nonneg (by norm_num) _
    have h2c_nonneg : (0 : ℤ) ≤ (2 : ℤ) ^ (U + U + U) := pow_nonneg (by norm_num) _
    have hprod1 : |yh| * |nh| ≤ 2 ^ (5 * U + 7) * 2 ^ U :=
      mul_le_mul hy hn hn_nonneg h2a_nonneg
    have hprod2 : (|yh| * |nh|) * |(Bh *ᵥ Γ) j| ≤ (2 ^ (5 * U + 7) * 2 ^ U) * 2 ^ (U + U + U) :=
      mul_le_mul hprod1 hBh hB_nonneg (by positivity)
    calc
      |yh * nh * (Bh *ᵥ Γ) j| = |yh| * |nh| * |(Bh *ᵥ Γ) j| := by simp [abs_mul]
      _ ≤ (2 ^ (5 * U + 7) * 2 ^ U) * 2 ^ (U + U + U) := hprod2
      _ = 2 ^ ((5 * U + 7) + U) * 2 ^ (U + U + U) := by rw [← Int.pow_add]
      _ = 2 ^ (((5 * U + 7) + U) + (U + U + U)) := by rw [← Int.pow_add]
      _ = 2 ^ (9 * U + 7) := by ring
  simpa [show (9 * U + 7 + U + 1 : ℕ) = (10 * U + 8 : ℕ) by omega]
    using rndZ_abs_pow (yh * nh * (Bh *ᵥ Γ) j) (F * Q * Q * G) Q (9 * U + 7) U hdenom hQnonneg hnum hQ

/-- R9: the numerator of `l'`. -/
theorem AdversarialBco.Bit.Transfer.BLM.hb_lp {d : ℕ} (F Q G D yh nh lh : ℤ) (Bh : Matrix (Fin d) (Fin d) ℤ)
    (Γ mu : Fin d → ℤ) (U : ℕ) (hF1 : 1 ≤ F) (hQ1 : 1 ≤ Q) (hQ : Q ≤ 2 ^ U) (hG1 : 1 ≤ G) (hD1 : 1 ≤ D)
    (hy : |yh| ≤ 2 ^ (5 * U + 7)) (hn : |nh| ≤ 2 ^ U) (hl : |lh| ≤ 2 ^ U) (hB : ∀ i j, |Bh i j| ≤ 2 ^ U)
    (hΓ : ∀ j, |Γ j| ≤ 2 ^ U) (hmu : ∀ j, |mu j| ≤ 2 ^ U) (hd : d ≤ 2 ^ U) :
    |lh + rndZ ((fun j => rndZ (yh * nh * (Bh *ᵥ Γ) j) (F * Q * Q * G) Q) ⬝ᵥ mu) (Q * D) Q| ≤ 2 ^ (13 * U + 10) := by
  have hQpos : 0 ≤ Q := by linarith
  have hFQQG_pos : 1 ≤ F * Q * Q * G := by
    have hQQ : (1 : ℤ) ≤ Q * Q := by
      have := mul_le_mul hQ1 hQ1 (by linarith) (by linarith)
      simpa using this
    have hFQQ : (1 : ℤ) ≤ F * (Q * Q) := by
      have := mul_le_mul hF1 hQQ (by linarith) (by linarith)
      simpa using this
    have hFQQG : (1 : ℤ) ≤ (F * (Q * Q)) * G := by
      have := mul_le_mul hFQQ hG1 (by linarith) (by linarith)
      simpa using this
    simpa [mul_assoc, mul_comm, mul_left_comm] using hFQQG
  have hQD_pos : 1 ≤ Q * D := by
    calc
      (1 : ℤ) = 1 * 1 := by simp
      _ ≤ Q * 1 := mul_le_mul hQ1 (by rfl) (by linarith) (by linarith)
      _ ≤ Q * D := mul_le_mul (by rfl) hD1 (by linarith) (by linarith)
  set ĝ := fun j => rndZ (yh * nh * (Bh *ᵥ Γ) j) (F * Q * Q * G) Q with hĝ_def
  have hBhΓ_bound : ∀ j, |(Bh *ᵥ Γ) j| ≤ (2 : ℤ) ^ (U + U + U) := by
    intro j
    exact mulVec_abs_le hB hΓ hd j
  have hprod_bound : ∀ j, |yh * nh * (Bh *ᵥ Γ) j| ≤ (2 : ℤ) ^ (9 * U + 7) := by
    intro j
    have h_abs : |yh * nh * (Bh *ᵥ Γ) j| = |yh| * |nh| * |(Bh *ᵥ Γ) j| := by
      simp [abs_mul]
    rw [h_abs]
    have h_mul1 : |yh| * |nh| ≤ (2 : ℤ) ^ (5 * U + 7) * (2 : ℤ) ^ U := by
      refine mul_le_mul hy hn (abs_nonneg _) (pow_nonneg (by norm_num) _)
    have h_mul2 : (|yh| * |nh|) * |(Bh *ᵥ Γ) j| ≤
        ((2 : ℤ) ^ (5 * U + 7) * (2 : ℤ) ^ U) * (2 : ℤ) ^ (U + U + U) := by
      refine mul_le_mul h_mul1 (hBhΓ_bound j) (abs_nonneg _) ?_
      exact mul_nonneg (pow_nonneg (by norm_num) _) (pow_nonneg (by norm_num) _)
    calc
      |yh| * |nh| * |(Bh *ᵥ Γ) j| ≤ ((2 : ℤ) ^ (5 * U + 7) * (2 : ℤ) ^ U) * (2 : ℤ) ^ (U + U + U) := h_mul2
      _ = (2 : ℤ) ^ ((5 * U + 7) + U + (U + U + U)) := by
        simp [pow_add]
      _ = (2 : ℤ) ^ (9 * U + 7) := by
        congr 1
        omega
  have hĝ_bound : ∀ j, |ĝ j| ≤ (2 : ℤ) ^ (10 * U + 8) := by
    intro j
    rw [hĝ_def]
    have h := rndZ_abs_pow (yh * nh * (Bh *ᵥ Γ) j) (F * Q * Q * G) Q (9 * U + 7) U
      hFQQG_pos hQpos (hprod_bound j) hQ
    have h_exp : (9 * U + 7) + U + 1 = 10 * U + 8 := by omega
    simpa [h_exp] using h
  have h_dot_bound : |ĝ ⬝ᵥ mu| ≤ (2 : ℤ) ^ ((10 * U + 8) + U + U) :=
    dot_abs_le hĝ_bound hmu hd
  have h_dot_bound_simp : |ĝ ⬝ᵥ mu| ≤ (2 : ℤ) ^ (12 * U + 8) := by
    have h_exp : (10 * U + 8) + U + U = 12 * U + 8 := by omega
    simpa [h_exp] using h_dot_bound
  have h_outer_bound : |rndZ (ĝ ⬝ᵥ mu) (Q * D) Q| ≤ (2 : ℤ) ^ ((12 * U + 8) + U + 1) :=
    rndZ_abs_pow (ĝ ⬝ᵥ mu) (Q * D) Q (12 * U + 8) U hQD_pos hQpos h_dot_bound_simp hQ
  have h_outer_bound_simp : |rndZ (ĝ ⬝ᵥ mu) (Q * D) Q| ≤ (2 : ℤ) ^ (13 * U + 9) := by
    have h_exp : (12 * U + 8) + U + 1 = 13 * U + 9 := by omega
    simpa [h_exp] using h_outer_bound
  have h_pow_le : (2 : ℤ) ^ U ≤ (2 : ℤ) ^ (13 * U + 9) := by
    have h_le : U ≤ 13 * U + 9 := by omega
    have h_nat : (2 : ℕ) ^ U ≤ (2 : ℕ) ^ (13 * U + 9) :=
      Nat.pow_le_pow_right (by norm_num) h_le
    exact_mod_cast h_nat
  calc
    |lh + rndZ (ĝ ⬝ᵥ mu) (Q * D) Q| ≤ |lh| + |rndZ (ĝ ⬝ᵥ mu) (Q * D) Q| := abs_add_le _ _
    _ ≤ (2 : ℤ) ^ U + (2 : ℤ) ^ (13 * U + 9) := add_le_add hl h_outer_bound_simp
    _ ≤ (2 : ℤ) ^ (13 * U + 9) + (2 : ℤ) ^ (13 * U + 9) := by linarith
    _ = (2 : ℤ) ^ (13 * U + 10) := by
      calc
        (2 : ℤ) ^ (13 * U + 9) + (2 : ℤ) ^ (13 * U + 9) = 2 * (2 : ℤ) ^ (13 * U + 9) := by ring
        _ = (2 : ℤ) ^ (13 * U + 9) * 2 := mul_comm _ _
        _ = (2 : ℤ) ^ ((13 * U + 9) + 1) := by rw [← pow_succ]
        _ = (2 : ℤ) ^ (13 * U + 10) := by rw [show (13 * U + 9) + 1 = 13 * U + 10 by omega]

/-- A numerator over `2^e` whose value is at most `R ≤ 2^a` is at most `2^E` when `a + e ≤ E`. -/
theorem AdversarialBco.Bit.Transfer.BLM.hb_x (x : ℤ) (e a E : ℕ) (R : ℚ) (h : |(x : ℚ) / 2 ^ e| ≤ R)
    (hR : R ≤ 2 ^ a) (hE : a + e ≤ E) : |x| ≤ 2 ^ E := by
  have hpos : 0 < (2 : ℚ) ^ e := pow_pos (by norm_num) e
  have hx_abs_eq : |(x : ℚ)| = |(x : ℚ) / (2 : ℚ) ^ e| * (2 : ℚ) ^ e := by
    calc
      |(x : ℚ)| = |((x : ℚ) / (2 : ℚ) ^ e) * (2 : ℚ) ^ e| := by
        field_simp [hpos.ne']
      _ = |(x : ℚ) / (2 : ℚ) ^ e| * |(2 : ℚ) ^ e| := by rw [abs_mul]
      _ = |(x : ℚ) / (2 : ℚ) ^ e| * (2 : ℚ) ^ e := by rw [abs_of_pos hpos]
  have hx_abs_le : |(x : ℚ)| ≤ (2 : ℚ) ^ E := by
    calc
      |(x : ℚ)| = |(x : ℚ) / (2 : ℚ) ^ e| * (2 : ℚ) ^ e := hx_abs_eq
      _ ≤ R * (2 : ℚ) ^ e := mul_le_mul_of_nonneg_right h (by positivity)
      _ ≤ (2 : ℚ) ^ a * (2 : ℚ) ^ e := mul_le_mul_of_nonneg_right hR (by positivity)
      _ = (2 : ℚ) ^ (a + e) := by rw [pow_add]
      _ ≤ (2 : ℚ) ^ E := pow_le_pow_right₀ (by norm_num) hE
  exact_mod_cast hx_abs_le

/-- `(B Bᵀ) w` from bounds on the entries of `B` and of `w`. -/
theorem AdversarialBco.Bit.Transfer.BLM.hb_Pw {d : ℕ} (Bp : Matrix (Fin d) (Fin d) ℚ) (w : Fin d → ℚ) (T R : ℚ)
    (hT : 0 ≤ T) (hR : 0 ≤ R) (hB : ∀ i j, |Bp i j| ≤ T) (hw : ∀ j, |w j| ≤ R) (i : Fin d) :
    |((Bp * Bpᵀ) *ᵥ w) i| ≤ d * d * T * T * R := by
  -- Expand the matrix-vector product
  have h_expand : ((Bp * Bpᵀ) *ᵥ w) i = ∑ k : Fin d, (∑ j : Fin d, Bp i j * Bp k j) * w k := by
    calc
      ((Bp * Bpᵀ) *ᵥ w) i = ∑ k : Fin d, (Bp * Bpᵀ) i k * w k := rfl
      _ = ∑ k : Fin d, (∑ j : Fin d, Bp i j * (Bpᵀ) j k) * w k := by
        simp [Matrix.mul_apply]
      _ = ∑ k : Fin d, (∑ j : Fin d, Bp i j * Bp k j) * w k := by
        simp [Matrix.transpose_apply]
  rw [h_expand]
  -- Bound |∑ k, (∑ j, Bp i j * Bp k j) * w k|
  calc
    |∑ k : Fin d, (∑ j : Fin d, Bp i j * Bp k j) * w k| ≤
        ∑ k : Fin d, |(∑ j : Fin d, Bp i j * Bp k j) * w k| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k : Fin d, (|∑ j : Fin d, Bp i j * Bp k j| * |w k|) := by
      simp [abs_mul]
    _ ≤ ∑ k : Fin d, (|∑ j : Fin d, Bp i j * Bp k j| * R) := by
      refine Finset.sum_le_sum ?_
      intro k _
      refine mul_le_mul_of_nonneg_left (hw k) (abs_nonneg _)
    _ ≤ ∑ k : Fin d, ((∑ j : Fin d, |Bp i j * Bp k j|) * R) := by
      refine Finset.sum_le_sum ?_
      intro k _
      refine mul_le_mul_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) hR
    _ = (∑ k : Fin d, ∑ j : Fin d, |Bp i j * Bp k j|) * R := by
      simp [Finset.sum_mul]
    _ = (∑ k : Fin d, ∑ j : Fin d, |Bp i j| * |Bp k j|) * R := by
      simp [abs_mul]
    _ ≤ (∑ k : Fin d, ∑ j : Fin d, T * T) * R := by
      refine mul_le_mul_of_nonneg_right ?_ hR
      refine Finset.sum_le_sum ?_
      intro k _
      refine Finset.sum_le_sum ?_
      intro j _
      refine mul_le_mul (hB i j) (hB k j) (abs_nonneg _) hT
    _ = (d * d * (T * T)) * R := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      ring
    _ = d * d * T * T * R := by ring

/-- A vector with `w·w ≤ (2W)²` has every coordinate at most `2|W|`. -/
theorem AdversarialBco.Bit.Transfer.BLM.hb_wmu {d : ℕ} (w : Fin d → ℚ) (W : ℚ) (h : ¬ (2 * W) ^ 2 < w ⬝ᵥ w)
    (j : Fin d) : |w j| ≤ 2 * |W| := by
  have hle : w ⬝ᵥ w ≤ (2 * W) ^ 2 := by
    linarith
  have hsq_nonneg : ∀ i, 0 ≤ w i * w i := by
    intro i
    have : w i * w i = (w i) ^ 2 := by ring
    rw [this]
    exact pow_two_nonneg _
  have hsq_j : w j * w j ≤ w ⬝ᵥ w := by
    calc
      w j * w j ≤ ∑ i : Fin d, w i * w i :=
        Finset.single_le_sum (by
          intro i hi
          exact hsq_nonneg i) (Finset.mem_univ j)
      _ = w ⬝ᵥ w := rfl
  have hsq_bound : w j * w j ≤ (2 * W) ^ 2 := by
    linarith
  have hsq_abs : (2 * W) ^ 2 = (2 * |W|) ^ 2 := by
    calc
      (2 * W) ^ 2 = 4 * (W ^ 2) := by ring
      _ = 4 * (|W| ^ 2) := by simp [sq_abs]
      _ = (2 * |W|) ^ 2 := by ring
  have h_nonneg : 0 ≤ 2 * |W| := by
    have : 0 ≤ |W| := abs_nonneg _
    nlinarith
  have h_abs_sq : (w j) ^ 2 ≤ (2 * |W|) ^ 2 := by
    calc
      (w j) ^ 2 = w j * w j := by ring
      _ ≤ (2 * W) ^ 2 := hsq_bound
      _ = (2 * |W|) ^ 2 := hsq_abs
  exact abs_le_of_sq_le_sq h_abs_sq h_nonneg

/-- The units of R2 to R4 are quadratic. -/
theorem AdversarialBco.Bit.Transfer.BLM.units_r24 (d m : ℕ) : r24Units d m ≤ 200 * (d + m + 1) ^ 2 := by
  unfold r24Units r2xUnits r2gUnits r2pUnits
  ring_nf
  nlinarith

/-- R9: the numerator of `G'_j`. -/
theorem AdversarialBco.Bit.Transfer.BLM.hb_Gp {d : ℕ} (F Q G yh nh : ℤ) (Bh : Matrix (Fin d) (Fin d) ℤ)
    (Γ Gh : Fin d → ℤ) (U : ℕ) (hF1 : 1 ≤ F) (hQ1 : 1 ≤ Q) (hQ : Q ≤ 2 ^ U) (hG1 : 1 ≤ G)
    (hy : |yh| ≤ 2 ^ (5 * U + 7)) (hn : |nh| ≤ 2 ^ U) (hB : ∀ i j, |Bh i j| ≤ 2 ^ U) (hΓ : ∀ j, |Γ j| ≤ 2 ^ U)
    (hGh : ∀ j, |Gh j| ≤ 2 ^ U) (hd : d ≤ 2 ^ U) (j : Fin d) :
    |Gh j + rndZ (yh * nh * (Bh *ᵥ Γ) j) (F * Q * Q * G) Q| ≤ 2 ^ (10 * U + 9) := by
  have hg := hb_g F Q G yh nh Bh Γ U hF1 hQ1 hQ hG1 hy hn hB hΓ hd j
  have hU : (2 : ℤ) ^ U ≤ 2 ^ (10 * U + 8) := pow_le_pow_right₀ (by norm_num) (by omega)
  calc |Gh j + rndZ (yh * nh * (Bh *ᵥ Γ) j) (F * Q * Q * G) Q|
      ≤ |Gh j| + |rndZ (yh * nh * (Bh *ᵥ Γ) j) (F * Q * Q * G) Q| := abs_add_le _ _
    _ ≤ 2 ^ (10 * U + 8) + 2 ^ (10 * U + 8) := add_le_add ((hGh j).trans hU) hg
    _ = 2 ^ (10 * U + 9) := by ring

set_option maxHeartbeats 400000 in
/-- R9: the numerator of `b'_j`. -/
theorem AdversarialBco.Bit.Transfer.BLM.hb_bp {d : ℕ} (F Q G D kN yh : ℤ) (Bh : Matrix (Fin d) (Fin d) ℤ)
    (Γ mu bh : Fin d → ℤ) (U : ℕ) (hF1 : 1 ≤ F) (hF : F ≤ 2 ^ U) (hQ1 : 1 ≤ Q) (hQ : Q ≤ 2 ^ U) (hG1 : 1 ≤ G)
    (hG : G ≤ 2 ^ U) (hD1 : 1 ≤ D) (hD : D ≤ 2 ^ U) (hk : |kN| ≤ 2 ^ U) (hy : |yh| ≤ 2 ^ (5 * U + 7))
    (hB : ∀ i j, |Bh i j| ≤ 2 ^ U) (hΓ : ∀ j, |Γ j| ≤ 2 ^ U) (hmu : ∀ j, |mu j| ≤ 2 ^ U) (hb : ∀ j, |bh j| ≤ 2 ^ U)
    (hd : d ≤ 2 ^ U) (j : Fin d) :
    |bh j + rndZ (kN * yh * (((Bh *ᵥ Γ) ⬝ᵥ mu) * (Bh *ᵥ Γ) j - G * G * (Bh *ᵥ (Bhᵀ *ᵥ mu)) j))
      (F * Q * Q * Q * (G * G) * D) Q| ≤ 2 ^ (15 * U + 10) := by
  set u := Bh *ᵥ Γ with hu_def
  have hu_abs : ∀ j', |u j'| ≤ (2 : ℤ) ^ (U + U + U) := by
    intro j'
    simpa [hu_def] using mulVec_abs_le hB hΓ hd j'
  have h_dot_abs : |u ⬝ᵥ mu| ≤ (2 : ℤ) ^ (U + U + U + U + U) := by
    have h := dot_abs_le (fun k => hu_abs k) hmu hd
    simpa [add_comm, add_left_comm, add_assoc] using h
  have h_BhT_mu_abs : ∀ j', |(Bhᵀ *ᵥ mu) j'| ≤ (2 : ℤ) ^ (U + U + U) := by
    intro j'
    have h_BhT : ∀ i k, |Bhᵀ i k| ≤ (2 : ℤ) ^ U := by
      intro i k
      simpa [Matrix.transpose_apply] using hB k i
    simpa using mulVec_abs_le h_BhT hmu hd j'
  have h_Bh_BhT_abs : ∀ j', |(Bh *ᵥ (Bhᵀ *ᵥ mu)) j'| ≤ (2 : ℤ) ^ (U + U + U + U + U) := by
    intro j'
    have h := mulVec_abs_le hB h_BhT_mu_abs hd j'
    simpa [add_comm, add_left_comm, add_assoc] using h
  have hG_nonneg : 0 ≤ G := by linarith
  have hG_abs : |G| ≤ (2 : ℤ) ^ U := by
    rw [abs_of_nonneg hG_nonneg]
    exact hG
  -- |a * b| ≤ 2^(ka + kb)
  have h_mul_bound {a b : ℤ} {ka kb : ℕ} (ha : |a| ≤ (2 : ℤ) ^ ka) (hb : |b| ≤ (2 : ℤ) ^ kb) :
      |a * b| ≤ (2 : ℤ) ^ (ka + kb) := by
    rw [abs_mul]
    have h := mul_le_mul ha hb (by positivity) (by positivity)
    simpa [pow_add] using h
  -- bound on (u ⬝ᵥ mu) * u j
  have h_prod1_abs : |(u ⬝ᵥ mu) * u j| ≤ (2 : ℤ) ^ ((U + U + U + U + U) + (U + U + U)) :=
    h_mul_bound h_dot_abs (hu_abs j)
  -- bound on G * G * (Bh *ᵥ (Bhᵀ *ᵥ mu)) j
  have h_prod2_abs : |G * G * (Bh *ᵥ (Bhᵀ *ᵥ mu)) j| ≤ (2 : ℤ) ^ ((U + U) + (U + U + U + U + U)) := by
    rw [abs_mul, abs_mul]
    -- goal: |G| * |G| * |(Bh *ᵥ (Bhᵀ *ᵥ mu)) j| ≤ 2^((U+U)+(U+U+U+U+U))
    -- multiplication is left-assoc, so this is (|G| * |G|) * |w j|
    have h_GG : |G| * |G| ≤ (2 : ℤ) ^ U * (2 : ℤ) ^ U :=
      mul_le_mul hG_abs hG_abs (by positivity) (by positivity)
    have h_GG_w : (|G| * |G|) * |(Bh *ᵥ (Bhᵀ *ᵥ mu)) j| ≤
        ((2 : ℤ) ^ U * (2 : ℤ) ^ U) * (2 : ℤ) ^ (U + U + U + U + U) :=
      mul_le_mul h_GG (h_Bh_BhT_abs j) (by positivity) (by positivity)
    simpa [pow_add, mul_assoc] using h_GG_w
  -- the difference: diff = (u ⬝ᵥ mu) * u j - G * G * (Bh *ᵥ (Bhᵀ *ᵥ mu)) j
  set diff := ((u ⬝ᵥ mu) * u j - G * G * (Bh *ᵥ (Bhᵀ *ᵥ mu)) j) with hdiff_def
  have h_diff_abs : |diff| ≤ (2 : ℤ) ^ ((U + U + U + U + U + U + U + U) + 1) := by
    rw [hdiff_def]
    -- |A - B| ≤ |A| + |B|
    have h_triangle : |((u ⬝ᵥ mu) * u j) - G * G * (Bh *ᵥ (Bhᵀ *ᵥ mu)) j| ≤
        |(u ⬝ᵥ mu) * u j| + |G * G * (Bh *ᵥ (Bhᵀ *ᵥ mu)) j| :=
      abs_sub _ _
    apply le_trans h_triangle
    -- Now need: |A| + |B| ≤ 2^(8U+1)
    apply le_trans (add_le_add h_prod1_abs h_prod2_abs)
    -- Now need: 2^(8U) + 2^(7U) ≤ 2^(8U+1)
    -- Since 2^(7U) ≤ 2^(8U), we have 2^(8U) + 2^(7U) ≤ 2^(8U) + 2^(8U) = 2^(8U+1)
    have h_pow_le : (2 : ℤ) ^ ((U + U) + (U + U + U + U + U)) ≤
        (2 : ℤ) ^ ((U + U + U + U + U) + (U + U + U)) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have h_sum : (2 : ℤ) ^ ((U + U + U + U + U) + (U + U + U)) + (2 : ℤ) ^ ((U + U) + (U + U + U + U + U)) ≤
        (2 : ℤ) ^ ((U + U + U + U + U) + (U + U + U)) + (2 : ℤ) ^ ((U + U + U + U + U) + (U + U + U)) := by
      have h := add_le_add_right h_pow_le ((2 : ℤ) ^ ((U + U + U + U + U) + (U + U + U)))
      -- h: 2^(7U) + 2^(8U) ≤ 2^(8U) + 2^(8U)
      -- we need 2^(8U) + 2^(7U) ≤ 2^(8U) + 2^(8U)
      simpa [add_comm] using h
    apply le_trans h_sum
    -- goal: 2^(8U) + 2^(8U) ≤ 2^(8U+1)
    -- we show equality then use le_of_eq
    have h_eq : (2 : ℤ) ^ ((U + U + U + U + U) + (U + U + U)) + (2 : ℤ) ^ ((U + U + U + U + U) + (U + U + U)) =
        (2 : ℤ) ^ ((U + U + U + U + U + U + U + U) + 1) := by
      calc
        (2 : ℤ) ^ ((U + U + U + U + U) + (U + U + U)) + (2 : ℤ) ^ ((U + U + U + U + U) + (U + U + U)) =
            2 * (2 : ℤ) ^ ((U + U + U + U + U) + (U + U + U)) := by ring
        _ = (2 : ℤ) ^ (U + U + U + U + U + (U + U + U)) * 2 := by ring
        _ = (2 : ℤ) ^ ((U + U + U + U + U + (U + U + U)) + 1) := by rw [pow_succ]
        _ = (2 : ℤ) ^ ((U + U + U + U + U + U + U + U) + 1) := by
          rw [show (U + U + U + U + U + (U + U + U)) + 1 = (U + U + U + U + U + U + U + U) + 1 by omega]
    rw [h_eq]
  -- numerator: num = kN * yh * diff
  set num := kN * yh * diff with hnum_def
  have h_num_abs : |num| ≤ (2 : ℤ) ^ (U + (5 * U + 7) + ((U + U + U + U + U + U + U + U) + 1)) := by
    rw [hnum_def]
    have h_eq : |kN * yh * diff| = |kN| * |yh| * |diff| := by
      simp [abs_mul, mul_assoc]
    rw [h_eq]
    have h1 : |kN| ≤ (2 : ℤ) ^ U := by simpa using hk
    have h2 : |yh| ≤ (2 : ℤ) ^ (5 * U + 7) := by simpa using hy
    have h3 : |diff| ≤ (2 : ℤ) ^ ((U + U + U + U + U + U + U + U) + 1) := h_diff_abs
    have h12 : |kN| * |yh| ≤ (2 : ℤ) ^ U * (2 : ℤ) ^ (5 * U + 7) :=
      mul_le_mul h1 h2 (by positivity) (by positivity)
    have h123 : (|kN| * |yh|) * |diff| ≤
        ((2 : ℤ) ^ U * (2 : ℤ) ^ (5 * U + 7)) * (2 : ℤ) ^ ((U + U + U + U + U + U + U + U) + 1) :=
      mul_le_mul h12 h3 (by positivity) (by positivity)
    simpa [pow_add, mul_assoc] using h123
  -- denominator: den = F * Q * Q * Q * (G * G) * D
  set den := F * Q * Q * Q * (G * G) * D with hden_def
  have h_den_pos : 1 ≤ den := by
    rw [hden_def]
    have hQQ : 1 ≤ Q * Q := by nlinarith
    have hQQQ : 1 ≤ Q * Q * Q := by nlinarith
    have hGG : 1 ≤ G * G := by nlinarith
    have h1 : 1 ≤ F * Q := one_le_mul_of_one_le_of_one_le hF1 hQ1
    have h2 : 1 ≤ (F * Q) * Q := one_le_mul_of_one_le_of_one_le h1 hQ1
    have h3 : 1 ≤ ((F * Q) * Q) * Q := one_le_mul_of_one_le_of_one_le h2 hQ1
    have h4 : 1 ≤ (((F * Q) * Q) * Q) * (G * G) := one_le_mul_of_one_le_of_one_le h3 hGG
    have h5 : 1 ≤ ((((F * Q) * Q) * Q) * (G * G)) * D := one_le_mul_of_one_le_of_one_le h4 hD1
    simpa [mul_assoc] using h5
  have hQ_nonneg : 0 ≤ Q := by linarith
  -- simplify the exponent: U + (5U+7) + (8U+1) = 14U + 8
  have h_exp_simp : U + (5 * U + 7) + ((U + U + U + U + U + U + U + U) + 1) = 14 * U + 8 := by omega
  have h_num_bound : |num| ≤ (2 : ℤ) ^ (14 * U + 8) := by
    have := h_num_abs
    rw [h_exp_simp] at this
    exact this
  have h_rndZ_abs : |rndZ num den Q| ≤ (2 : ℤ) ^ ((14 * U + 8) + U + 1) :=
    rndZ_abs_pow num den Q (14 * U + 8) U h_den_pos hQ_nonneg h_num_bound hQ
  -- simplify: (14U+8) + U + 1 = 15U + 9
  have h_rndZ_exp : (14 * U + 8) + U + 1 = 15 * U + 9 := by omega
  rw [h_rndZ_exp] at h_rndZ_abs
  -- final step: |bh j + rndZ ...| ≤ |bh j| + |rndZ ...| ≤ 2^U + 2^(15U+9) ≤ 2^(15U+10)
  have h_bh_abs : |bh j| ≤ (2 : ℤ) ^ U := by simpa using hb j
  have h_sum_abs : |bh j + rndZ num den Q| ≤ |bh j| + |rndZ num den Q| :=
    abs_add_le _ _
  have h_final : |bh j| + |rndZ num den Q| ≤ (2 : ℤ) ^ (15 * U + 10) := by
    have h_pow_le : (2 : ℤ) ^ U ≤ (2 : ℤ) ^ (15 * U + 9) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have h_add := add_le_add h_bh_abs h_rndZ_abs
    -- h_add: |bh j| + |rndZ| ≤ 2^U + 2^(15U+9)
    -- We need: 2^U + 2^(15U+9) ≤ 2^(15U+10)
    -- 2^U ≤ 2^(15U+9), so 2^U + 2^(15U+9) ≤ 2^(15U+9) + 2^(15U+9) = 2^(15U+10)
    apply le_trans h_add
    have h1 : (2 : ℤ) ^ U + (2 : ℤ) ^ (15 * U + 9) ≤ (2 : ℤ) ^ (15 * U + 9) + (2 : ℤ) ^ (15 * U + 9) := by
      simpa [add_comm] using add_le_add_right h_pow_le ((2 : ℤ) ^ (15 * U + 9))
    have h2 : (2 : ℤ) ^ (15 * U + 9) + (2 : ℤ) ^ (15 * U + 9) = (2 : ℤ) ^ (15 * U + 10) := by
      calc
        (2 : ℤ) ^ (15 * U + 9) + (2 : ℤ) ^ (15 * U + 9) = 2 * (2 : ℤ) ^ (15 * U + 9) := by
          rw [two_mul]
        _ = (2 : ℤ) ^ (15 * U + 9) * 2 := by rw [mul_comm]
        _ = (2 : ℤ) ^ ((15 * U + 9) + 1) := by rw [← pow_succ 2 (15*U+9)]
        _ = (2 : ℤ) ^ (15 * U + 10) := by rw [show ((15 * U + 9) + 1) = 15 * U + 10 by omega]
    exact h1.trans h2.le
  exact le_trans h_sum_abs h_final

/-- R9: the numerator of `k'`. -/
theorem AdversarialBco.Bit.Transfer.BLM.hb_kp {d : ℕ} (F Q G D kN yh kh : ℤ) (Bh : Matrix (Fin d) (Fin d) ℤ)
    (Γ mu : Fin d → ℤ) (U : ℕ) (hF1 : 1 ≤ F) (_hF : F ≤ 2 ^ U) (hQ1 : 1 ≤ Q) (hQ : Q ≤ 2 ^ U) (hG1 : 1 ≤ G)
    (hG : G ≤ 2 ^ U) (hD1 : 1 ≤ D) (_hD : D ≤ 2 ^ U) (hk : |kN| ≤ 2 ^ U) (hy : |yh| ≤ 2 ^ (5 * U + 7))
    (hkh : |kh| ≤ 2 ^ U) (hB : ∀ i j, |Bh i j| ≤ 2 ^ U) (hΓ : ∀ j, |Γ j| ≤ 2 ^ U) (hmu : ∀ j, |mu j| ≤ 2 ^ U)
    (hd : d ≤ 2 ^ U) :
    |kh + rndZ (kN * yh * (((Bh *ᵥ Γ) ⬝ᵥ mu) * ((Bh *ᵥ Γ) ⬝ᵥ mu) - G * G * ((Bhᵀ *ᵥ mu) ⬝ᵥ (Bhᵀ *ᵥ mu))))
      (2 * (F * Q * Q * Q * (G * G) * D * D)) Q| ≤ 2 ^ (17 * U + 10) := by
  have pw : ∀ {x : ℤ} {a b : ℕ}, |x| ≤ 2 ^ a → a ≤ b → |x| ≤ 2 ^ b := fun h hab =>
    h.trans (pow_le_pow_right₀ (by norm_num) hab)
  have mulb : ∀ {x y : ℤ} {a b : ℕ}, |x| ≤ 2 ^ a → |y| ≤ 2 ^ b → |x * y| ≤ 2 ^ (a + b) := fun hx hy => by
    rw [abs_mul, pow_add]; exact mul_le_mul hx hy (abs_nonneg _) (by positivity)
  have hBt : ∀ i k, |Bhᵀ i k| ≤ (2 : ℤ) ^ U := fun i k => hB k i
  have hu := fun j => mulVec_abs_le hB hΓ hd j
  have hw := fun j => mulVec_abs_le hBt hmu hd j
  have h1 := dot_abs_le hu hmu hd
  have h2 := dot_abs_le hw hw hd
  have hGa : |G| ≤ 2 ^ U := by rw [abs_of_pos (by omega)]; exact hG
  have e1 := mulb h1 h1
  have e2 := mulb (mulb hGa hGa) h2
  have e3 : |((Bh *ᵥ Γ) ⬝ᵥ mu) * ((Bh *ᵥ Γ) ⬝ᵥ mu) - G * G * ((Bhᵀ *ᵥ mu) ⬝ᵥ (Bhᵀ *ᵥ mu))| ≤
      2 ^ (10 * U + 1) := by
    refine (abs_sub _ _).trans ?_
    rw [pow_succ, mul_two]
    exact add_le_add (pw e1 (by omega)) (pw e2 (by omega))
  have e4 := mulb (mulb hk hy) e3
  have hden : 1 ≤ 2 * (F * Q * Q * Q * (G * G) * D * D) := by
    have : 0 < F * Q * Q * Q * (G * G) * D * D := by positivity
    omega
  have e5 := rndZ_abs_pow _ _ Q _ U hden (by omega) e4 hQ
  refine (abs_add_le _ _).trans ?_
  have h2p : (2 : ℤ) ^ (17 * U + 10) = 2 ^ (17 * U + 9) + 2 ^ (17 * U + 9) := by
    rw [show 17 * U + 10 = 17 * U + 9 + 1 by omega, pow_succ]; ring
  rw [h2p]
  exact add_le_add (pw hkh (by omega)) (pw e5 (by omega))
