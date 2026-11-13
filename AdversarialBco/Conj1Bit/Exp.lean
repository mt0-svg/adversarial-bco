/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Assembly

@[expose] public section

/-!
# The expected regret of the bit learner

`theoremConj1UpperBit_exp`: from `TheoremConj1UpperBit` (StatementConj1Bit.lean), the same program `P` runs within the
same cost and space and plays in the polytope, and its regret, as a function of the adversary's seed and the coins, is
integrable for `ρ ⊗ coinStream` with expectation at most `C d^{3/2} √n log(2dn)^5`.

The regret is measurable for every program (`regMeasOK`, Bit/Assembly.lean) and lies in `[-n, n]`
(`regretPts_le_of_mem`, `neg_le_regretPts_of_mem`, Conj1Exp/Bound.lean): the losses are admissible on the rational
points played (`playedBit_eq`, `RandAdv`) and the points lie in the polytope. So it is integrable, at most the
majorant `R` of the statement, whose integral is at most `ENNReal.ofReal (C X)`, `X = d^{3/2} √n log(2dn)^5 ≥ 0`;
the constant `max C 0` absorbs a negative `C`.
-/

namespace AdversarialBco

open MeasureTheory ProbabilityTheory
open BitRAM
open RealRAM (Strategy lossAd regretPts polytope HeightLE)
open scoped NNReal ENNReal

/-- **The expected regret of the bit learner**, from `TheoremConj1UpperBit`: one program `P` and constants `C, C', k`
such that, on every input of the statement and against every randomized admissible adversary `σ` with seed law `ρ`,
on every seed and coin sequence `P` plays `n` rounds within cost and space `C' (d m log(2dn) log(2M))^k` at points of
the polytope, and the regret is integrable for `ρ ⊗ coinStream` with expectation at most
`C d^{3/2} √n log(2dn)^5`. -/
theorem theoremConj1UpperBit_exp (h : TheoremConj1UpperBit) :
    ∃ (P : List Instr) (C C' : ℝ) (k : ℕ),
      ∀ d : ℕ, 1 ≤ d → ∀ n : ℕ, 1 ≤ n → ∀ m M : ℕ,
      ∀ (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ), HeightLE A b M →
        (∃ c : E d, Metric.closedBall c 1 ⊆ polytope A b) →
        (∀ x ∈ polytope A b, ∀ y ∈ polytope A b, dist x y ≤ n) →
      ∀ (Θ : Type) [MeasurableSpace Θ] (ρ : Measure Θ), IsProbabilityMeasure ρ →
      ∀ σ : Θ → Strategy d, RandAdv (polytope A b) n σ →
        (∀ (θ : Θ) (cs : ℕ → Bool),
          CostOKBit P ⟨σ θ, cs⟩ (initBit d n m A b) n
              (C' * ((d : ℝ) * m * Real.log (2 * d * n) * Real.log (2 * M)) ^ k) ∧
            SpaceOKBit P ⟨σ θ, cs⟩ (initBit d n m A b) n
              (C' * ((d : ℝ) * m * Real.log (2 * d * n) * Real.log (2 * M)) ^ k) ∧
            ∀ t < n, playedBit P ⟨σ θ, cs⟩ (initBit d n m A b) t ∈ polytope A b) ∧
        Integrable (fun ω : Θ × (ℕ → Bool) =>
            regretPts (polytope A b) (lossAd (σ ω.1) 0 (playedBit P ⟨σ ω.1, ω.2⟩ (initBit d n m A b)))
              (playedBit P ⟨σ ω.1, ω.2⟩ (initBit d n m A b)) n) (ρ.prod coinStream) ∧
        ∫ ω, regretPts (polytope A b) (lossAd (σ ω.1) 0 (playedBit P ⟨σ ω.1, ω.2⟩ (initBit d n m A b)))
              (playedBit P ⟨σ ω.1, ω.2⟩ (initBit d n m A b)) n ∂(ρ.prod coinStream) ≤
          C * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n * Real.log (2 * d * n) ^ 5 := by
  obtain ⟨P, C, C', k, hP⟩ := h
  refine ⟨P, max C 0, C', k, ?_⟩
  intro d hd n hn m M A b hH hball hdiam Θ _ ρ hρ σ hσ
  obtain ⟨hrun, R, hRm, hRle, hRint⟩ := hP d hd n hn m M A b hH hball hdiam Θ ρ hρ σ hσ
  refine ⟨hrun, ?_⟩
  have hI : Bit.Asm.InputOK d n m M A b := ⟨hd, hn, hH, hball, hdiam⟩
  have hmeas : Measurable fun ω : Θ × (ℕ → Bool) => Bit.Asm.regBit P d n m A b (σ ω.1) ω.2 :=
    Bit.Asm.regMeasOK P d n m M A b hI Θ σ hσ fun θ cs => (hrun θ cs).2.2
  -- the regret lies in `[-n, n]`
  have hbnd : ∀ ω : Θ × (ℕ → Bool), ‖Bit.Asm.regBit P d n m A b (σ ω.1) ω.2‖ ≤ n := by
    intro ω
    have hf : ∀ t < n, AdmLoss (polytope A b)
        (lossAd (σ ω.1) 0 (playedBit P ⟨σ ω.1, ω.2⟩ (initBit d n m A b)) t) := by
      intro t ht
      rw [Bit.Asm.playedBit_eq]
      exact (hσ t ht (Bit.Asm.ptsBit P ⟨σ ω.1, ω.2⟩ (initBit d n m A b))).1 ω.1
    have hx := (hrun ω.1 ω.2).2.2
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨RealRAM.neg_le_regretPts_of_mem hf hx, RealRAM.regretPts_le_of_mem hf hx⟩
  have : IsProbabilityMeasure (ρ.prod coinStream) := inferInstance
  have hi : Integrable (fun ω : Θ × (ℕ → Bool) => Bit.Asm.regBit P d n m A b (σ ω.1) ω.2) (ρ.prod coinStream) :=
    Integrable.of_bound hmeas.aestronglyMeasurable (n : ℝ) (Filter.Eventually.of_forall hbnd)
  refine ⟨hi, ?_⟩
  -- the expectation
  have hfin : ∫⁻ ω, (R ω : ℝ≥0∞) ∂(ρ.prod coinStream) ≠ ⊤ := (hRint.trans_lt ENNReal.ofReal_lt_top).ne
  have hRi : Integrable (fun ω => (R ω : ℝ)) (ρ.prod coinStream) := by
    have := integrable_toReal_of_lintegral_ne_top (measurable_coe_nnreal_ennreal.comp hRm).aemeasurable hfin
    simpa using this
  have hX : 0 ≤ (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n * Real.log (2 * d * n) ^ 5 := by
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hl : 0 ≤ Real.log (2 * d * n) := Real.log_nonneg (by nlinarith)
    positivity
  calc _ ≤ ∫ ω, (R ω : ℝ) ∂(ρ.prod coinStream) := integral_mono hi hRi hRle
    _ = (∫⁻ ω, (R ω : ℝ≥0∞) ∂(ρ.prod coinStream)).toReal := by
        have h := integral_toReal (μ := ρ.prod coinStream) (f := fun ω => (R ω : ℝ≥0∞))
          (measurable_coe_nnreal_ennreal.comp hRm).aemeasurable
          (Filter.Eventually.of_forall fun ω => ENNReal.coe_lt_top)
        simpa using h
    _ ≤ (ENNReal.ofReal (C * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n * Real.log (2 * d * n) ^ 5)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hRint
    _ = max (C * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n * Real.log (2 * d * n) ^ 5) 0 := ENNReal.toReal_ofReal'
    _ ≤ max C 0 * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n * Real.log (2 * d * n) ^ 5 := by
        have e1 : C * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n * Real.log (2 * d * n) ^ 5 =
            C * ((d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n * Real.log (2 * d * n) ^ 5) := by ring
        have e2 : max C 0 * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n * Real.log (2 * d * n) ^ 5 =
            max C 0 * ((d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n * Real.log (2 * d * n) ^ 5) := by ring
        rw [e1, e2]
        exact max_le (mul_le_mul_of_nonneg_right (le_max_left _ _) hX) (mul_nonneg (le_max_right _ _) hX)

end AdversarialBco
