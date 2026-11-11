/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.MachDf2B
public import AdversarialBco.Poly.MachPGParts
public import AdversarialBco.Poly.MachPGBound
public import AdversarialBco.Poly.Df2ParBounds

@[expose] public section

/-!
# The cost of DF2-O in VL, and `Df2OMachine` from its inputs

Polynomial bounds on the step counts of `df2Prog` (`kDf2A_le`, `kDf2B_le`, `kMode0_le`, `df2B0_le`), and
`df2oMachine_of`: the machine layer `Df2OMachine` from the rules of PG (`PG.PgLeaves`), the rules of the two calls of
AP in each round (`ApRules`, within caps `K1`, `K2` depending on `d, n, δ`), the bound on `j`, and the bounds on the
steps of PG and on the caps of AP.
-/

namespace AdversarialBco.Poly.Mach.VL

open AdversarialBco AdversarialBco.RealRAM AdversarialBco.Poly

/-- The steps of part A of a round. -/
theorem kDf2A_le (d j : ℕ) (hd : 1 ≤ d) : kDf2A d j ≤ 241 * d ^ 2 * (j + 1) := by
  have e : kDf2A d j = 30 * d ^ 2 + 121 * d + 90 + j * (10 * d ^ 2 + 44 * d + 33) := by
    unfold kDf2A kARun kMemKp; ring
  have h1 : d ≤ d ^ 2 := by nlinarith
  have h2 : 1 ≤ d ^ 2 := by nlinarith
  rw [e]; nlinarith [Nat.mul_le_mul_left j h1, Nat.mul_le_mul_left j h2]

/-- The steps of part B of a round, with caps `K1`, `K2` on the calls of AP. -/
theorem kDf2B_le (d K1 K2 : ℕ) (hd : 1 ≤ d) : kDf2B d K1 K2 ≤ 761 * d ^ 2 + K1 + K2 := by
  have e : kDf2B d K1 K2 = 145 * d ^ 2 + 311 * d + 305 + K1 + K2 := by
    unfold kDf2B kNext kC1 kC2 kC3 kC4 kC5 kC6 kCommit kInit; ring
  have h1 : d ≤ d ^ 2 := by nlinarith
  have h2 : 1 ≤ d ^ 2 := by nlinarith
  rw [e]; nlinarith

/-- The steps of the code of the first mode. -/
theorem kMode0_le (d : ℕ) (hd : 1 ≤ d) : kMode0 d ≤ 124 * d ^ 2 := by
  have e : kMode0 d = 20 * d ^ 2 + 46 * d + 58 := by unfold kMode0; ring
  have h1 : d ≤ d ^ 2 := by nlinarith
  have h2 : 1 ≤ d ^ 2 := by nlinarith
  rw [e]; nlinarith

/-- The steps before the first play: the setup, the preparation (with PG) and part A of round `0`. -/
theorem df2B0_le (d n : ℕ) (hd : 1 ≤ d) (r0 R0 δ : ℝ) :
    df2L.NS + 2 * df2L.NA + 4 * d + 7 + kPre d n r0 R0 δ + kDf2A d (df2oPar d n δ).j + 3 ≤
      PG.kPG d r0 R0 (df2oPar d n δ).δ1 + 1006 * d ^ 2 * ((df2oPar d n δ).j + 1) := by
  have hA := kDf2A_le d (df2oPar d n δ).j hd
  have hM := kMode0_le d hd
  have h1 : d ≤ d ^ 2 := by nlinarith
  have h2 : 1 ≤ d ^ 2 := by nlinarith
  have h3 := Nat.mul_le_mul_left (df2oPar d n δ).j h2
  unfold kPre
  simp only [df2L]
  nlinarith

/-- `log (2 d n / δ) ≥ 1 / 2`. -/
theorem df2_log_ge (d n : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    1 / 2 ≤ Real.log (2 * d * n / δ) := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h2 : (2 : ℝ) ≤ 2 * d * n / δ := by
    rw [le_div_iff₀ hδ]; nlinarith
  have := Real.log_two_gt_d9
  have := Real.log_le_log (by norm_num) h2
  linarith

/-- `d² (j + 1) ≤ 71 (2 d n L)²` when `j ≤ 70 L` and `L ≥ 1 / 2`. -/
theorem df2_poly_le (d n : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n) (L j : ℝ) (hL : 1 / 2 ≤ L) (hj : j ≤ 70 * L) :
    (d : ℝ) ^ 2 * (j + 1) ≤ 71 * (2 * (d * n * L)) ^ 2 := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hD : (0 : ℝ) ≤ (d : ℝ) ^ 2 := sq_nonneg _
  have hq : j + 1 ≤ 284 * (n * L) ^ 2 := by
    have h1 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
    have h2 : 70 * L + 1 ≤ 284 * L ^ 2 := by nlinarith
    have h3 : L ^ 2 ≤ (n * L) ^ 2 := by rw [mul_pow]; nlinarith [sq_nonneg L]
    linarith
  calc (d : ℝ) ^ 2 * (j + 1) ≤ (d : ℝ) ^ 2 * (284 * (n * L) ^ 2) := mul_le_mul_of_nonneg_left hq hD
    _ = 71 * (2 * (d * n * L)) ^ 2 := by ring

/-- `Df2OMachine` from the rules of PG and of the calls of AP, the bound on `j`, and the bounds on the steps of PG and
of the calls of AP. -/
theorem df2oMachine_of (hL : PG.PgLeaves)
    (hj : ∀ d n : ℕ, 1 ≤ d → 1 ≤ n → ∀ δ : ℝ, 0 < δ → δ < 1 →
      ((df2oPar d n δ).j : ℝ) ≤ 70 * Real.log (2 * d * n / δ))
    (hPG : ∃ C : ℝ, ∃ k : ℕ, ∀ d n : ℕ, 1 ≤ d → 1 ≤ n → ∀ r0 R0 δ : ℝ, 0 < r0 → r0 ≤ R0 → 0 < δ → δ < 1 →
      (PG.kPG d r0 R0 (df2oPar d n δ).δ1 : ℝ) ≤
        C * ((d : ℝ) * n * Real.log (2 * d * n / δ) * (2 + Real.log (R0 / r0))) ^ k)
    (K1 K2 : ℕ → ℕ → ℝ → ℕ)
    (hK : ∃ C : ℝ, ∃ k : ℕ, ∀ d n : ℕ, 1 ≤ d → 1 ≤ n → ∀ δ : ℝ, 0 < δ → δ < 1 →
      ((K1 d n δ + K2 d n δ : ℕ) : ℝ) ≤ C * ((d : ℝ) * n * Real.log (2 * d * n / δ)) ^ k)
    (hAP : ∀ d : ℕ, 1 ≤ d → ∀ n : ℕ, 1 ≤ n → ∀ r0 R0 δ : ℝ, 0 < r0 → r0 ≤ R0 → 0 < δ → δ < 1 →
      ∀ K : Set (E d), IsCompact K → Convex ℝ K → Metric.closedBall 0 r0 ⊆ K → K ⊆ Metric.closedBall 0 R0 →
      ∀ f ∈ Advs K n, ∀ gs noise : ℕ → ℝ, ∀ t < n, ∀ st,
        df2oMode d n r0 R0 δ ⟨K, f, noise, gs⟩ t = .run st →
        ApRules ⟨K, f, noise, gs⟩ (df2oPar d n δ) n ((df2oPos d n r0 R0 δ ⟨K, f, noise, gs⟩).getD 0) st
          (df2oXi (df2oN0 d r0 R0 (df2oPar d n δ).δ1) gs t)
          (df2Y (df2oPar d n δ) K ((df2oPos d n r0 R0 δ ⟨K, f, noise, gs⟩).getD 0) (f t) (noise t) st
            (df2oXi (df2oN0 d r0 R0 (df2oPar d n δ).δ1) gs t)
            (df2oZeta d (df2oN0 d r0 R0 (df2oPar d n δ).δ1) gs t)) (K1 d n δ) (K2 d n δ)) :
    Df2OMachine := by
  obtain ⟨CP, kP, hP⟩ := hPG
  obtain ⟨CK, kK, hKb⟩ := hK
  set k := max 2 (max kP kK) with hk
  refine ⟨df2Prog.compile 0, (71 * 1006 + max CP 0 + max CK 0) * 2 ^ k, k,
    fun d hd n hn r0 R0 δ hr0 hrR hδ hδ1 K hKc hKv hball hsub f hf gs noise => ?_⟩
  obtain ⟨hC, hpl⟩ := df2Prog_spec hL d n hd hn r0 R0 δ ⟨K, f, noise, gs⟩ (K1 d n δ) (K2 d n δ)
    (hAP d hd n hn r0 R0 δ hr0 hrR hδ hδ1 K hKc hKv hball hsub f hf gs noise)
  set j := (df2oPar d n δ).j with hjdef
  set L := Real.log (2 * d * n / δ) with hLdef
  have hL2 : 1 / 2 ≤ L := df2_log_ge d n hd hn δ hδ hδ1
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hX : (1 : ℝ) ≤ 2 * (d * n * L) := by
    have : (1 : ℝ) ≤ d * n := by nlinarith
    nlinarith
  have hpoly := df2_poly_le d n hd hn L j hL2 (hj d n hd hn δ hδ hδ1)
  have hk2 : 2 ≤ k := le_max_left _ _
  have hkP : kP ≤ k := le_trans (le_max_left _ _) (le_max_right _ _)
  have hkK : kK ≤ k := le_trans (le_max_right _ _) (le_max_right _ _)
  have h2k : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  have hmP : 0 ≤ max CP 0 := le_max_right _ _
  have hmK : 0 ≤ max CK 0 := le_max_right _ _
  refine ⟨CostOK.mono hC ?_ ?_, hpl⟩
  · have hG : 2 ≤ 2 + Real.log (R0 / r0) := by
      have : 1 ≤ R0 / r0 := by rw [le_div_iff₀ hr0]; linarith
      linarith [Real.log_nonneg this]
    set Y := (d : ℝ) * n * L * (2 + Real.log (R0 / r0)) with hY
    have hZY : 2 * (d * n * L) ≤ Y := by
      rw [hY]; have : 0 ≤ (d : ℝ) * n * L := by nlinarith
      nlinarith
    have hY1 : 1 ≤ Y := le_trans hX hZY
    have hB0 : ((df2L.NS + 2 * df2L.NA + 4 * d + 7 + kPre d n r0 R0 δ + kDf2A d j + 3 : ℕ) : ℝ) ≤
        (PG.kPG d r0 R0 (df2oPar d n δ).δ1 : ℝ) + 1006 * ((d : ℝ) ^ 2 * (j + 1)) := by
      have := df2B0_le d n hd r0 R0 δ
      have h' : ((df2L.NS + 2 * df2L.NA + 4 * d + 7 + kPre d n r0 R0 δ + kDf2A d j + 3 : ℕ) : ℝ) ≤
          ((PG.kPG d r0 R0 (df2oPar d n δ).δ1 + 1006 * d ^ 2 * (j + 1) : ℕ) : ℝ) := by exact_mod_cast this
      refine h'.trans (le_of_eq ?_); push_cast; ring
    have hPk := hP d n hd hn r0 R0 δ hr0 hrR hδ hδ1
    have e1 : Y ^ kP ≤ Y ^ k := pow_le_pow_right₀ hY1 hkP
    have e2 : (2 * (d * n * L)) ^ 2 ≤ Y ^ k :=
      le_trans (pow_le_pow_left₀ (by linarith) hZY 2) (pow_le_pow_right₀ hY1 hk2)
    have e3 : CP * Y ^ kP ≤ max CP 0 * Y ^ k :=
      le_trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg (by linarith) _))
        (mul_le_mul_of_nonneg_left e1 hmP)
    have hYk : 0 ≤ Y ^ k := pow_nonneg (by linarith) _
    calc _ ≤ (PG.kPG d r0 R0 (df2oPar d n δ).δ1 : ℝ) + 1006 * ((d : ℝ) ^ 2 * (j + 1)) := hB0
      _ ≤ max CP 0 * Y ^ k + 1006 * (71 * Y ^ k) := by
        have hPk' : (PG.kPG d r0 R0 (df2oPar d n δ).δ1 : ℝ) ≤ CP * Y ^ kP := hPk
        exact add_le_add (hPk'.trans e3) (by linarith [hpoly, e2])
      _ = (71 * 1006 + max CP 0) * Y ^ k := by ring
      _ ≤ (71 * 1006 + max CP 0 + max CK 0) * Y ^ k := by nlinarith [mul_nonneg hmK hYk]
      _ ≤ (71 * 1006 + max CP 0 + max CK 0) * 2 ^ k * Y ^ k := by
        have hS : 0 ≤ (71 * 1006 + max CP 0 + max CK 0) * Y ^ k := mul_nonneg (by linarith) hYk
        nlinarith [mul_le_mul_of_nonneg_left h2k hS]
  · have hB : ((kDf2A d j + kDf2B d (K1 d n δ) (K2 d n δ) + 4 : ℕ) : ℝ) ≤
        1006 * ((d : ℝ) ^ 2 * (j + 1)) + ((K1 d n δ + K2 d n δ : ℕ) : ℝ) := by
      have hA := kDf2A_le d j hd
      have hBB := kDf2B_le d (K1 d n δ) (K2 d n δ) hd
      have h2 : 1 ≤ d ^ 2 := by nlinarith
      have hN : kDf2A d j + kDf2B d (K1 d n δ) (K2 d n δ) + 4 ≤ 1006 * d ^ 2 * (j + 1) + (K1 d n δ + K2 d n δ) := by
        nlinarith
      have h' : ((kDf2A d j + kDf2B d (K1 d n δ) (K2 d n δ) + 4 : ℕ) : ℝ) ≤
          ((1006 * d ^ 2 * (j + 1) + (K1 d n δ + K2 d n δ) : ℕ) : ℝ) := by exact_mod_cast hN
      refine h'.trans (le_of_eq ?_); push_cast; ring
    have hKk := hKb d n hd hn δ hδ hδ1
    set X := (d : ℝ) * n * L with hXd
    have hX0 : 0 ≤ X := by linarith
    have e1 : X ^ kK ≤ (2 * X) ^ k :=
      le_trans (pow_le_pow_left₀ hX0 (by linarith) kK) (pow_le_pow_right₀ hX hkK)
    have e2 : (2 * X) ^ 2 ≤ (2 * X) ^ k := pow_le_pow_right₀ hX hk2
    have e3 : CK * X ^ kK ≤ max CK 0 * (2 * X) ^ k :=
      le_trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hX0 _))
        (mul_le_mul_of_nonneg_left e1 hmK)
    have e4 : (2 * X) ^ k = 2 ^ k * X ^ k := mul_pow 2 X k
    have hXk : 0 ≤ X ^ k := pow_nonneg hX0 _
    have hKk' : ((K1 d n δ + K2 d n δ : ℕ) : ℝ) ≤ CK * X ^ kK := hKk
    have hpoly' : (d : ℝ) ^ 2 * (j + 1) ≤ 71 * (2 * X) ^ 2 := hpoly
    calc _ ≤ 1006 * ((d : ℝ) ^ 2 * (j + 1)) + ((K1 d n δ + K2 d n δ : ℕ) : ℝ) := hB
      _ ≤ 1006 * (71 * (2 * X) ^ k) + max CK 0 * (2 * X) ^ k := by linarith [hKk'.trans e3]
      _ = (71 * 1006 + max CK 0) * (2 ^ k * X ^ k) := by rw [e4]; ring
      _ ≤ (71 * 1006 + max CP 0 + max CK 0) * 2 ^ k * X ^ k := by
        have := mul_nonneg hmP (mul_nonneg (le_trans zero_le_one h2k) hXk)
        nlinarith

/-- `Df2OMachine` from the rules of the calls of AP and the bound on their caps: the rules of PG (`PG.pgLeaves`), the
bound on `j` (`df2oPar_j_le`) and the bound on the steps of PG (`PG.kPG_bound`) are proved. -/
theorem df2oMachine_of_ap (K1 K2 : ℕ → ℕ → ℝ → ℕ)
    (hK : ∃ C : ℝ, ∃ k : ℕ, ∀ d n : ℕ, 1 ≤ d → 1 ≤ n → ∀ δ : ℝ, 0 < δ → δ < 1 →
      ((K1 d n δ + K2 d n δ : ℕ) : ℝ) ≤ C * ((d : ℝ) * n * Real.log (2 * d * n / δ)) ^ k)
    (hAP : ∀ d : ℕ, 1 ≤ d → ∀ n : ℕ, 1 ≤ n → ∀ r0 R0 δ : ℝ, 0 < r0 → r0 ≤ R0 → 0 < δ → δ < 1 →
      ∀ K : Set (E d), IsCompact K → Convex ℝ K → Metric.closedBall 0 r0 ⊆ K → K ⊆ Metric.closedBall 0 R0 →
      ∀ f ∈ Advs K n, ∀ gs noise : ℕ → ℝ, ∀ t < n, ∀ st,
        df2oMode d n r0 R0 δ ⟨K, f, noise, gs⟩ t = .run st →
        ApRules ⟨K, f, noise, gs⟩ (df2oPar d n δ) n ((df2oPos d n r0 R0 δ ⟨K, f, noise, gs⟩).getD 0) st
          (df2oXi (df2oN0 d r0 R0 (df2oPar d n δ).δ1) gs t)
          (df2Y (df2oPar d n δ) K ((df2oPos d n r0 R0 δ ⟨K, f, noise, gs⟩).getD 0) (f t) (noise t) st
            (df2oXi (df2oN0 d r0 R0 (df2oPar d n δ).δ1) gs t)
            (df2oZeta d (df2oN0 d r0 R0 (df2oPar d n δ).δ1) gs t)) (K1 d n δ) (K2 d n δ)) :
    Df2OMachine :=
  df2oMachine_of PG.pgLeaves (fun d n hd hn δ hδ hδ1 => df2oPar_j_le d n hd hn δ hδ hδ1) PG.kPG_bound K1 K2 hK hAP

end AdversarialBco.Poly.Mach.VL
