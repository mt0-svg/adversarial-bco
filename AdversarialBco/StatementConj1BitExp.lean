/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.StatementConj1Bit

@[expose] public section

/-!
# Statement: Conjecture 1 of Bubeck, Eldan and Lee, first sentence, in the bit-cost model, in expectation

`TheoremConj1UpperBitExp` is `TheoremConj1UpperBit` (StatementConj1Bit.lean) with the regret bounded in expectation:
the same program `P` of the logarithmic-cost RAM of StatementBitRAM.lean, the same input `initBit d n m A b`, the same
hypotheses on the polytope `K = {x : A x ≤ b}` and on the randomised adaptive adversary `σ` with seed law `ρ`, the same
cost, space and play clauses on every run, and in place of a measurable majorant `R` of the regret with
`∫ R d(ρ ⊗ coinStream) ≤ C d^{3/2} n^{1/2} L^5`, `L = log (2 d n)`:

* the regret on `K` against the losses that the adversary chose on the run, as a function of the seed and the coins,
  is integrable for `ρ ⊗ coinStream`;
* its expectation is at most `C d^{3/2} n^{1/2} L^5`.

Everything it uses is defined in StatementConj1Bit.lean, StatementBitRAM.lean and the statement files they import,
unchanged. Integrability is asserted, so the Bochner integral is not the junk value `0` of a non-integrable function;
the regret may be negative, and the bound is on its mean, not on the mean of its positive part. `L ≥ log 2 > 0` for
`d, n ≥ 1`. The constant `C` is existential and uniform over every input and every adversary.
-/

open MeasureTheory ProbabilityTheory

namespace AdversarialBco

open BitRAM in
open RealRAM (Strategy lossAd regretPts polytope HeightLE) in
/-- **Conjecture 1 of Bubeck, Eldan and Lee, first sentence, in the bit-cost model, in expectation.** One program `P`
of the logarithmic-cost RAM and constants `C, C', k` such that, on every input of `TheoremConj1UpperBit` and against
every randomised adaptive adversary `σ` with seed law `ρ`, on every seed and coin sequence `P` plays `n` rounds within
cost and space `C' (d m log(2dn) log(2M))^k` at points of the polytope, and the regret is integrable for
`ρ ⊗ coinStream` with expectation at most `C d^{3/2} √n log(2dn)^5`. -/
def TheoremConj1UpperBitExp : Prop :=
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
        C * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n * Real.log (2 * d * n) ^ 5

end AdversarialBco
