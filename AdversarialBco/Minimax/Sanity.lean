/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Minimax.Value
public import AdversarialBco.UnifiedLower.Sanity

@[expose] public section

/-!
# Sanity checks of StatementMinimax.lean (`TheoremLowerUD`, `TheoremLowerUDProg`, `TheoremMinimax`)

The witnesses of the payoffs, which go with `lowerU_hyps_satisfiable` and `progU_hyps_satisfiable` of
UnifiedLower/Sanity.lean (the structural hypotheses):

* `payoffs_bounded`: the payoffs of every learner of `Learners` form nonempty sets inside `[0, n]` (mean) and `[-n, n]`
  (quantile at a level `δ' < 1`), so no `sSup` of the values is a junk value.
* `meanPosOf_tail_eq_integral`: the mean payoff of an almost everywhere strongly measurable function is the integral of
  its positive part (the layer cake formula).
* `log_lt_of_lt_pow`: `log x < m` when `x < 2.7182818283^m`, used by LowerDeltaQ/Sanity.lean for the range hypotheses.
-/

open MeasureTheory

namespace AdversarialBco.Minimax.MinimaxSanity

open BitRAM BitRAMO

/-- `log x < m` when `x < 2.7182818283^m`. -/
theorem log_lt_of_lt_pow (x : ℝ) (hx : 0 < x) (m : ℕ) (hm : m ≠ 0) (h : x < (2.7182818283 : ℝ) ^ m) :
    Real.log x < m := by
  rw [Real.log_lt_iff_lt_exp hx, ← Real.exp_one_pow]
  exact h.trans (pow_lt_pow_left₀ Real.exp_one_gt_d9 (by norm_num) hm)

/-- The payoffs of every learner of `Learners` on a convex nonempty `K` form nonempty sets inside `[0, n]` for the mean
and inside `[-n, n]` for the quantile at every level `δ' < 1`. -/
theorem payoffs_bounded {d : ℕ} (K : Set (E d)) (orc : (Fin d → ℚ) → ℕ → Bool) (s0 : State d) (n : ℕ)
    (ℓ : ProgWin) (hK : Convex ℝ K) (hne : K.Nonempty) (hℓ : ℓ ∈ Learners K orc s0 n) :
    (payoffs K n s0 orc meanPosOf ℓ).Nonempty ∧ payoffs K n s0 orc meanPosOf ℓ ⊆ Set.Icc 0 (n : ℝ) ∧
      ∀ δ' : ℝ, δ' < 1 → (payoffs K n s0 orc (quantileOf δ') ℓ).Nonempty ∧
        payoffs K n s0 orc (quantileOf δ') ℓ ⊆ Set.Icc (-(n : ℝ)) n :=
  ⟨payoffs_nonempty hK _ ℓ, payoffs_subset meanPosOf_range hℓ hne, fun _ hδ =>
    ⟨payoffs_nonempty hK _ ℓ, payoffs_subset (quantileOf_range hδ) hℓ hne⟩⟩

/-- The mean of the positive part read from the tail of an almost everywhere strongly measurable `X` is
`∫ max(X, 0) dμ`. -/
theorem meanPosOf_tail_eq_integral {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ℝ)
    (hX : AEStronglyMeasurable X μ) : meanPosOf (fun u => μ {ω | u < X ω}) = ∫ ω, max (X ω) 0 ∂μ :=
  meanPosOf_tail_eq_ae μ hX

end AdversarialBco.Minimax.MinimaxSanity
