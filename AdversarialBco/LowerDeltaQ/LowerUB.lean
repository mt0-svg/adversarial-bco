/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.LowerDeltaQ.Statement

@[expose] public section

/-!
# Clause (b) of Theorem LU from Theorem LU-DQ

Clause (b) of `TheoremLowerU` and of `TheoremLowerUProg` (StatementUnifiedLower.lean): for `d ≥ 4·10^6` and
`n ≥ d^10`, a strategy of `StratsLowU K n r0` against which the regret is at least `2.8·10^-9 d^{3/2} √n / log d` with
probability at least `1/2`. It is clause (a) of `TheoremLowerUDQ` (resp. `TheoremLowerUDProgQ`) at the failure
`δ = 1/2`: its range holds for every `d ≥ 4·10^6` (`range_half`, LowerDeltaQ/Main.lean), its probability is
`1 - 1/2 = 1/2`, and its threshold `2.1·10^-8 (1/2)^{3/2} d^{3/2} √n / log d ≥ 7.42·10^-9 d^{3/2} √n / log d` is above
`2.8·10^-9 d^{3/2} √n / log d`.
-/

open MeasureTheory

namespace AdversarialBco.LowerDeltaQ

open BitRAM BitRAMO Unified UnifiedLower Minimax
open RealRAM (Strategy)
open Lower (Learner IsLearnerAd regretAd)

/-- `ENNReal.ofReal (1 - 1/2) = 1/2`. -/
theorem ofReal_one_sub_half : ENNReal.ofReal (1 - 1 / 2 : ℝ) = 1 / 2 := by
  rw [show (1 - 1 / 2 : ℝ) = 1 / 2 by norm_num, ENNReal.ofReal_div_of_pos two_pos, ENNReal.ofReal_one,
    ENNReal.ofReal_ofNat]

/-- The range of clause (a) of `TheoremLowerUDQ` at `δ = 1/2`, in the form of the statement. -/
theorem range_half_lub {d : ℕ} (hd : 4000000 ≤ d) :
    1024 * (120 * Real.log d + 68) ≤ min (1 / 2 : ℝ) (1 / 2) * d ∧
      10 * (120 * Real.log d + 68) ≤ min (1 / 2 : ℝ) (1 / 2) ^ (3 / 2 : ℝ) * d := by
  obtain ⟨-, h2, h3⟩ := sqrt_facts (show (0 : ℝ) < 1 / 2 by norm_num)
  obtain ⟨hD1, hD3⟩ := range_half hd
  rw [h2] at hD1
  rw [h3] at hD3
  rw [min_self]
  exact ⟨hD1, hD3⟩

/-- `2.8·10^-9 ≤ 2.1·10^-8 min(1/2, 1/2)^{3/2}`. -/
theorem c28_le_half : (28 / 10 ^ 10 : ℝ) ≤ 21 / 10 ^ 9 * min (1 / 2 : ℝ) (1 / 2) ^ (3 / 2 : ℝ) := by
  obtain ⟨-, -, h3⟩ := sqrt_facts (show (0 : ℝ) < 1 / 2 by norm_num)
  rw [min_self, ← h3]
  have := sqrt_half_cube_ge
  linarith

/-- The threshold of clause (b) of `TheoremLowerU` is at most that of clause (a) of `TheoremLowerUDQ` at `δ = 1/2`. -/
theorem thr28_le {d : ℕ} (n : ℕ) (hd : 4000000 ≤ d) :
    28 / 10 ^ 10 * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n / Real.log d ≤
      21 / 10 ^ 9 * min (1 / 2 : ℝ) (1 / 2) ^ (3 / 2 : ℝ) * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n / Real.log d := by
  have hD : 0 ≤ (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n / Real.log d := by positivity
  have e1 : 28 / 10 ^ 10 * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n / Real.log d =
      28 / 10 ^ 10 * ((d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n / Real.log d) := by ring
  have e2 : 21 / 10 ^ 9 * min (1 / 2 : ℝ) (1 / 2) ^ (3 / 2 : ℝ) * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n / Real.log d =
      21 / 10 ^ 9 * min (1 / 2 : ℝ) (1 / 2) ^ (3 / 2 : ℝ) * ((d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n / Real.log d) := by
    ring
  rw [e1, e2]
  exact mul_le_mul_of_nonneg_right c28_le_half hD

/-- **Clause (b) of `TheoremLowerU` from `TheoremLowerUDQ`**: at `δ = 1/2`, clause (a). -/
theorem lowerU_b_of_UDQ (h : TheoremLowerUDQ) :
    ∀ d : ℕ, 1 ≤ d → ∀ n : ℕ, 1 ≤ n → ∀ (a : E d) (r0 R0 : ℝ) (K : Set (E d)), BodyU K a r0 R0 →
    ∀ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω), IsProbabilityMeasure μ →
    ∀ pol : Learner Ω d, IsLearnerAd K n pol → 4000000 ≤ d → d ^ 10 ≤ n →
      LowerProb K n r0 μ pol (28 / 10 ^ 10 * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n / Real.log d) (1 / 2) := by
  intro d hd n hn a r0 R0 K hb Ω mΩ μ hμ pol hpol h4 h10
  obtain ⟨hD1, hD3⟩ := range_half_lub h4
  obtain ⟨σ, hσ, hm, -, hp⟩ :=
    (h d hd n hn a r0 R0 K hb Ω mΩ μ hμ pol hpol).1 (1 / 2) (by norm_num) (by norm_num) h4 h10 hD1 hD3
  rw [ofReal_one_sub_half] at hp
  exact ⟨σ, hσ, hm, hp.trans (measure_mono fun ω hω => le_trans (thr28_le n h4) hω)⟩

/-- **Clause (b) of `TheoremLowerUProg` from `TheoremLowerUDProgQ`**: at the failure `δ' = 1/2`, clause (a). -/
theorem lowerUProg_b_of_UDProgQ (h : TheoremLowerUDProgQ) :
    ∀ (P : List InstrO) (d : ℕ), 1 ≤ d → ∀ n : ℕ, 1 ≤ n → ∀ δ r0 R0 : ℚ, 0 < δ → δ < 1 → 0 < r0 → r0 ≤ R0 →
    ∀ (a : Fin d → ℚ) (K : Set (E d)), IsCompact K → Convex ℝ K →
      Metric.closedBall (toE a) (r0 : ℝ) ⊆ K → K ⊆ Metric.closedBall (toE a) (R0 : ℝ) →
    ∀ orc : (Fin d → ℚ) → ℕ → Bool, WeakMemOracle K orc →
    ∀ (B : ℝ) (D D' : ℕ → ℕ), MachineOK P K orc (initU d n δ r0 R0 a) n B D D' →
      4000000 ≤ d → d ^ 10 ≤ n →
        ProgProb P K orc (initU d n δ r0 R0 a) n r0 D D'
          (28 / 10 ^ 10 * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n / Real.log d) (1 / 2) := by
  intro P d hd n hn δ r0 R0 h0 h1 hr0 hr a K hKc hKv hb1 hb2 orc horc B D D' hM h4 h10
  obtain ⟨hD1, hD3⟩ := range_half_lub h4
  obtain ⟨σ, loss, hσ, hcl, hN, hm, -, hp⟩ :=
    (h P d hd n hn δ r0 R0 h0 h1 hr0 hr a K hKc hKv hb1 hb2 orc horc B D D' hM).1 (1 / 2) (by norm_num)
      (by norm_num) h4 h10 hD1 hD3
  rw [ofReal_one_sub_half] at hp
  exact ⟨σ, loss, hσ, hcl, hN, hm, hp.trans (measure_mono fun cs hcs => le_trans (thr28_le n h4) hcs)⟩

end AdversarialBco.LowerDeltaQ
