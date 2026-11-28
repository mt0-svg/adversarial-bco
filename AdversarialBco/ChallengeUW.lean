/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
-- Comparator challenge of config-uw.json: AdversarialBco/StatementUW.lean verbatim over the seventh module, its theorem,
-- Theorem U from it and the five non-vacuity witnesses of the hypotheses, each proved by `sorry`
-- (code/formal-proof/challenges.sh). Nothing imports this module; the warnings `declaration uses sorry` are expected.
module

public import AdversarialBco.ChallengeBase.StatementUnified

@[expose] public section

/-!
# Statement: Theorem UW, the upper bound with `log (1/δ)` entering once (release v2.4)

`TheoremUW` is Theorem UW, over StatementUnified.lean (the statement of v2.3, imported
unchanged). The program of its proof is the learner BL-OW: the learner of `TheoremUnified` on the
table T4U, with the floors at a level that does not depend on `δ`, the confidence entering through a scale `u`, and
the observation weighted and clipped. Its bound in probability separates the two roles of `δ`:

  `P(Reg_n > C (d^{3/2} n^{1/2} log^5 (2 d n) + d (n log (2/δ))^{1/2} log^{9/2} (2 d n))) ≤ δ`.

The first term does not depend on `δ`; `log (1/δ)` enters the second once, under a square root. This is the power of
`log (1/δ)` that the lower bound of `TheoremGrowG` (StatementMatched.lean) has.

## The claim (`TheoremUW`)

`TheoremUW` is `TheoremUnified` word for word, with two changes in the regret clauses (ii):

* the probability clause reads `μ (Reg_n > C (d^{3/2} √n log^5 (2 d n) + d √(n log (2/δ)) log^{9/2} (2 d n))) ≤ δ`
  in place of `μ (Reg_n > C d^{3/2} √n log^5 (2 d n / δ)) ≤ δ`;
* the mean clause reads `∫ max (Reg_n, 0) dμ ≤ C (d^{3/2} √n log^5 (2 d n) + d √(n log (2/δ)) log^{9/2} (2 d n)) + n δ`.

Everything else is that of `TheoremUnified` and keeps its docstring: one program `P` of the oracle machine, constants
`C`, `C'`, an exponent `k` and two coin schedules `D`, `D'` (functions of the input), chosen before the input; the input
`d, n, δ, r0, R0, a` (`initU`), with the confidence `δ` read by the program; every compact convex `K` with
`B̄(a, r0) ⊆ K ⊆ B̄(a, R0)` and every weak membership oracle of `K`; the machine clauses (i) on every world, with the
cost and space bound `B = C' (d log (2 d n / δ) S)^k`, the plays in `K` and the coin windows; and the class of
environments (`NoisyAdv`, BJLR26's adversary and noise with the windows `D`, `D'`), with the regret measurable and
integrable. The sections "The input", "The machine clauses", "The environment", "Against BJLR26 Section 3, line by
line" and "The regret, the probability and the expectation" of StatementUnified.lean apply unchanged.

## The confidence

The program still reads `δ`: BL-OW computes its scale `u = 1 + k_δ log 2 / (7 d Λ_0)` from the input `δ`, rounded up
and not capped (AdversarialBco/UW/ProgPure.lean), so the same program meets the two regret clauses for every `δ`, as in
`TheoremUnified`. The cost bound keeps `log (2 d n / δ)`: clause (i) is unchanged. Of the two terms of the bound, the
first does not depend on `δ` and the second grows as `(log (2/δ))^{1/2}`.

## Non-vacuity (AdversarialBco/Unified/Sanity.lean)

The hypotheses are those of `TheoremUnified`, word for word, and its witnesses apply unchanged: `hyps_satisfiable`
(the hypotheses hold together at `d = n = 1`, `δ = 1/2`, the unit ball with its exact membership oracle, the zero
losses and noise), `noisyAdv_signNoise` (members with nonzero noise in every round), `histσ_le` (the conditional
expectations are given a sub-σ-algebra), `nil_not_costOKO` (the empty program fails the cost clause).

## What is not claimed

The polylogarithmic factors `log^5 (2 d n)` and `log^{9/2} (2 d n)` are not claimed optimal. As in `TheoremUnified`:
an oracle whose ambiguous answers change from run to run, plays in the interior of `K`, a body without a known centre
and radii, a noise that reads the coins drawn after the play of its round or a loss that reads the coins of the
current draw, a real `δ`, and the lower bound (StatementMinimaxQ.lean, StatementMatched.lean).

## Junk values

`log (2 d n) ≥ log 2 > 0` for `d, n ≥ 1`, so `log (2 d n) ^ (9/2 : ℝ)` is `Real.rpow` at a positive base, the usual
power. `log (2/δ) > log 2 > 0` for `0 < δ < 1`, so the square root is that of a positive number. `d ^ (3/2 : ℝ)` is
`Real.rpow` at `d ≥ 1`. The other junk values are those of StatementUnified.lean.
-/

open MeasureTheory ProbabilityTheory

namespace AdversarialBco

open BitRAM BitRAMO Unified in
/-- **Theorem UW.** One program `P` of the bit RAM with a weak membership oracle, constants `C, C', k` and coin
schedules `D, D'` such that, for every `d, n ≥ 1`, every rational `δ ∈ (0, 1)`, every rational centre `a` and radii
`0 < r0 ≤ R0`, every compact convex `K` with `B̄(a, r0) ⊆ K ⊆ B̄(a, R0)` and every weak membership oracle of `K`:
on every world (admissible losses, any noise, any coins) `P` plays `n` rounds, each within cost
`C' (d log(2dn/δ) S)^k` with its cells in use within the same bound, at points of `K`, reading exactly `D' t` coins
before the play of round `t` and at most `D t` before the play of round `t - 1`; and for every noisy adversary with
these windows (BJLR26's adversary and noise) the regret is measurable and integrable, exceeds
`C (d^{3/2} √n log^5(2dn) + d √(n log(2/δ)) log^{9/2}(2dn))` with probability at most `δ`, and its positive part has
mean at most that plus `n δ`. -/
def TheoremUW : Prop :=
  ∃ (P : List InstrO) (C C' : ℝ) (k : ℕ) (D D' : (d n : ℕ) → ℚ → ℚ → ℚ → (Fin d → ℚ) → ℕ → ℕ),
    ∀ d : ℕ, 1 ≤ d → ∀ n : ℕ, 1 ≤ n → ∀ δ r0 R0 : ℚ, 0 < δ → δ < 1 → 0 < r0 → r0 ≤ R0 →
    ∀ (a : Fin d → ℚ) (K : Set (E d)), IsCompact K → Convex ℝ K →
      Metric.closedBall (toE a) (r0 : ℝ) ⊆ K → K ⊆ Metric.closedBall (toE a) (R0 : ℝ) →
    ∀ orc : (Fin d → ℚ) → ℕ → Bool, WeakMemOracle K orc →
      (∀ (f : ℕ → E d → ℝ) (noise : ℕ → ℝ) (cs : ℕ → Bool), (∀ t < n, AdmLoss K (f t)) →
        CostOKO P ⟨f, noise, cs, orc⟩ (initU d n δ r0 R0 a) n
            (C' * ((d : ℝ) * Real.log (2 * d * n / (δ : ℝ)) * sizeU δ r0 R0 a) ^ k) ∧
          SpaceOKO P ⟨f, noise, cs, orc⟩ (initU d n δ r0 R0 a) n
            (C' * ((d : ℝ) * Real.log (2 * d * n / (δ : ℝ)) * sizeU δ r0 R0 a) ^ k) ∧
          (∀ t < n, playedO P ⟨f, noise, cs, orc⟩ (initU d n δ r0 R0 a) t ∈ K) ∧
          CoinWindowsOK P ⟨f, noise, cs, orc⟩ (initU d n δ r0 R0 a) n (D d n δ r0 R0 a) (D' d n δ r0 R0 a)) ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) (coin : Ω → ℕ → Bool) (loss : ℕ → Ω → E d → ℝ)
        (noise : ℕ → Ω → ℝ), NoisyAdv K n (D d n δ r0 R0 a) (D' d n δ r0 R0 a) μ coin loss noise →
        Measurable (fun ω => regretU P K n (initU d n δ r0 R0 a) (envWorld orc coin loss noise ω)) ∧
        Integrable (fun ω => regretU P K n (initU d n δ r0 R0 a) (envWorld orc coin loss noise ω)) μ ∧
        μ {ω | C * ((d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n * Real.log (2 * d * n) ^ 5 +
              d * Real.sqrt (n * Real.log (2 / (δ : ℝ))) * Real.log (2 * d * n) ^ (9 / 2 : ℝ)) <
            regretU P K n (initU d n δ r0 R0 a) (envWorld orc coin loss noise ω)} ≤ ENNReal.ofReal (δ : ℝ) ∧
        ∫ ω, max (regretU P K n (initU d n δ r0 R0 a) (envWorld orc coin loss noise ω)) 0 ∂μ ≤
          C * ((d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n * Real.log (2 * d * n) ^ 5 +
              d * Real.sqrt (n * Real.log (2 / (δ : ℝ))) * Real.log (2 * d * n) ^ (9 / 2 : ℝ)) + n * (δ : ℝ)

namespace UW

/-- **Theorem UW** (`TheoremUW`): the theorem that a solution module proves. -/
theorem theoremUW : TheoremUW := by
  sorry

/-- **Theorem U from Theorem UW**, at the constant `2 max(C, 0)` with UW's program, cost constants and windows. -/
theorem theoremUnified_of_UW (h : TheoremUW) : TheoremUnified := by
  sorry

end UW

namespace Unified.UnifiedSanity

open BitRAM BitRAMO

/-- The exact membership answer is a weak membership oracle for `K` at every precision. -/
theorem weakMemOracle_exact {d : ℕ} (K : Set (E d)) [DecidablePred (· ∈ K)] :
    WeakMemOracle K (fun y _ => decide (toE y ∈ K)) := by
  sorry

/-- Under `NoisyAdv`, the σ-algebra generated by the losses of the rounds below `L ≤ n`, the noises of the rounds below
`M ≤ n` and the coins below any index, and that of the coins from any index on, are sub-σ-algebras of the σ-algebra
of `Ω`. -/
theorem histσ_le {d n : ℕ} {K : Set (E d)} {D D' : ℕ → ℕ} {Ω : Type} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
    {coin : Ω → ℕ → Bool} {loss : ℕ → Ω → E d → ℝ} {noise : ℕ → Ω → ℝ}
    (h : NoisyAdv K n D D' μ coin loss noise) {L M : ℕ} (hL : L ≤ n) (hM : M ≤ n) (N : ℕ) :
    histσ K loss noise coin L M N ≤ mΩ ∧ coinsFrom coin N ≤ mΩ := by
  sorry

/-- The hypotheses of `TheoremUnified` hold together: `d = n = 1`, `δ = 1/2`, the centre `0`, `r0 = R0 = 1`, the closed
unit ball with its exact membership oracle, and the zero losses with zero noise on the coin space, for all windows. -/
theorem hyps_satisfiable (D D' : ℕ → ℕ) :
    (0 : ℚ) < 1 / 2 ∧ (1 / 2 : ℚ) < 1 ∧ (0 : ℚ) < 1 ∧ (1 : ℚ) ≤ 1 ∧
      IsCompact (Metric.closedBall (toE (0 : Fin 1 → ℚ)) 1) ∧
      Convex ℝ (Metric.closedBall (toE (0 : Fin 1 → ℚ)) 1) ∧
      Metric.closedBall (toE (0 : Fin 1 → ℚ)) ((1 : ℚ) : ℝ) ⊆ Metric.closedBall (toE (0 : Fin 1 → ℚ)) 1 ∧
      Metric.closedBall (toE (0 : Fin 1 → ℚ)) 1 ⊆ Metric.closedBall (toE (0 : Fin 1 → ℚ)) ((1 : ℚ) : ℝ) ∧
      (∃ orc : (Fin 1 → ℚ) → ℕ → Bool, WeakMemOracle (Metric.closedBall (toE (0 : Fin 1 → ℚ)) 1) orc ∧
        ∀ y k, orc y k = true ↔ toE y ∈ Metric.closedBall (toE (0 : Fin 1 → ℚ)) 1) ∧
      NoisyAdv (Metric.closedBall (toE (0 : Fin 1 → ℚ)) 1) 1 D D' coinStream (fun ω => ω)
        (fun _ _ _ => 0) (fun _ _ => 0) := by
  sorry

/-- The class has members with a nonzero noise in every round: on the fair coins indexed by `ℕ ⊕ ℕ`, the program's
coins at the indices `inl j`, the noise of round `t` equal to `1/2` or `-1/2` according to the coin at `inr t`, and the
zero losses, for every convex `K`, every `n` and all windows. -/
theorem noisyAdv_signNoise {d : ℕ} (K : Set (E d)) (hK : Convex ℝ K) (n : ℕ) (D D' : ℕ → ℕ) :
    NoisyAdv K n D D' (Measure.infinitePi fun _ : ℕ ⊕ ℕ => coinLaw) (fun ω j => ω (Sum.inl j))
        (fun _ _ _ => 0) (fun t ω => if ω (Sum.inr t) then 1 / 2 else -1 / 2) ∧
      ∀ (t : ℕ) (ω : ℕ ⊕ ℕ → Bool), (if ω (Sum.inr t) then (1 / 2 : ℝ) else -1 / 2) ≠ 0 := by
  sorry

/-- The empty program never plays, so it fails the cost clause on every input with `n ≥ 1`. -/
theorem nil_not_costOKO {d : ℕ} (w : WorldO d) (s0 : State d) (n : ℕ) (B : ℝ) (h0 : s0.rounds < n) :
    ¬ CostOKO [] w s0 n B := by
  sorry

end Unified.UnifiedSanity

end AdversarialBco
