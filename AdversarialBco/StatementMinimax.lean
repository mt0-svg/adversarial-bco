/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.StatementUnifiedLower

@[expose] public section

/-!
# Statement: the lower bound with `δ` and the minimax theorem in the game of Theorem U (release v2.4)

Three claims over the statements of v2.3 (StatementUnified.lean, StatementUnifiedLower.lean, imported unchanged), with
the constants of the lower bound with `δ` (Theorem LU-D and its corollaries):

* `TheoremLowerUD`: the lower bound of `TheoremLowerU` with a failure probability `δ`, for every learner;
* `TheoremLowerUDProg`: the same for the programs of the oracle machine, in the objects of `TheoremUnified`, as
  `TheoremLowerUProg` is for `TheoremLowerU`;
* `TheoremMinimax`: the minimax values of the game of Theorem U, in expectation and in quantile, bounded from above
  and from below.

`TheoremMinimax` bounds the minimax values from both sides: each value is an infimum over the learners of a supremum
over the environments, and the theorem places it between two explicit functions of `d`, `n` and `δ`. It is not an
identity `inf sup = sup inf` between the minimax and the maximin values, which is not claimed.

## The lower bound with `δ` (`TheoremLowerUD`, `TheoremLowerUDProg`)

With `Λ = d^{3/2} n^{1/2} / log d`, on every body of `BodyU` and for every measurable randomised learner:

* (a) for `0 < δ < 1`, `d ≥ 4·10^6`, `n ≥ d^10` and `d^3 min(δ, 1/2)^5 ≥ 5.2·10^14 (log d)^3`, a strategy of
  `StratsLowU K n r0` against which the regret is measurable, nonnegative at every seed, and at least
  `1.12·10^-8 min(δ, 1/2)^2 Λ` with probability at least `1 - δ` (`LowerProbNN`);
* (b) for `d ≥ 4·10^6` and `n ≥ d^10`, a strategy of the class against which the regret is integrable with mean at
  least `1.4·10^-9 Λ` (`LowerMean`);
* (c) clause (c) of `TheoremLowerU`, unchanged.

The threshold of (a) at `δ = 1/2` is `2.8·10^-9 Λ`, that of clause (b) of `TheoremLowerU`. The constant `1.4·10^-9` of
every mean bound here is the one derived from the probability form (`1/2` times `2.8·10^-9`). `TheoremLowerUDProg` asks
the same of every
program that meets `MachineOK` on an input of `TheoremUnified`'s class, with `ProgProbNN` and `ProgMean`: a strategy in
closed loop with the program, zero noise, on the program's coin space, an environment of `TheoremUnified` with the
program's windows. Its failure probability `δ'` is a real parameter apart from the confidence `δ` that the program
reads; at `δ' = δ` it is the form "with probability `1 - δ`" of `TheoremUnified`.

## The game (`ProgWin`, `Learners`, `LearnersB`, `payoffs`)

The game `G` is the input `(d, n, δ, r0, R0, a)` of `TheoremUnified` with a body `K` and a weak membership oracle `orc`
of `K`.

* A learner is a program `P` of the oracle machine with two coin windows `D`, `D'` (`ProgWin`) that meets, on the input
  `initU d n δ r0 R0 a`, three of the machine clauses of `TheoremUnified` (`MachineOK` of StatementUnifiedLower.lean,
  the hypothesis of `TheoremLowerUProg`): on every world whose losses are admissible on `K` in the rounds `t < n`, every
  round within some cost `B`, the plays of the rounds `t < n` in `K`, and the coin windows `D`, `D'`. These are the
  learners of `Learners`. `LearnersB B` asks clause (i) of `TheoremUnified` with the bound `B`: cost `B` per round,
  space `B`, plays in `K`, the windows; so `LearnersB B ⊆ Learners`.
* An adversary of the learner `(P, D, D')` is an environment of clause (ii) of `TheoremUnified` with its windows: a
  probability space `(Ω, μ)`, any `Ω : Type`, with the program's coins, the losses and the noises, a `NoisyAdv` with
  the windows `D`, `D'`. The learner's choice of windows is part of its move: `D'` is pinned by the coin clause (the
  number of coins read when round `t` is played), and `D t` is at least the number read when round `t - 1` is played;
  a larger `D t` only enlarges the class of adversaries.
* The payoff is a function of the tail of the regret (`tailU`): `u ↦ μ {Reg_n > u}`, with `Reg_n = regretU`, the
  regret of `TheoremUnified`. Two payoffs: the `(1 - δ')`-quantile `quantileOf δ' T = inf {u | T u ≤ δ'}` and the mean
  of the positive part `meanPosOf T = ∫_0^∞ T u du`.

The quantile value is the minimax `(1 - δ)`th quantile of Ma, Verchand and Samworth (High-probability minimax lower
bounds, arXiv 2406.13447), the infimum of the `r ∈ [0, ∞)` with `P{L ≤ r} ≥ 1 - δ`, the same set as `P(L > r) ≤ δ`;
Bongole, Zamani, Oechtering and Skoglund (Minimax quantile lower bounds for interactive statistical decision making with
privacy, arXiv 2606.23096) call it the strict minimax quantile, with `r ∈ [0, ∞]`. In both the infimum over the
learners is outside the supremum over the environments, and a learner may depend on the level. Their losses are
nonnegative; the regret here can be negative, and `u` ranges over the reals. The value is the same as with `u ≥ 0`:
every learner has the environment with the constant loss `0` and the noise `0`, where its regret and its quantile are
`0`.

## The values (`value`, `valMean`, `valQuant`, `valMeanB`, `valQuantB`)

`value L pay = inf_{ℓ ∈ L} sup_{environments of ℓ} pay (tail)`, with `sInf` and `sSup` on sets of reals.

* `valMean G = V⁺(G)`: the infimum over the learners of the supremum over their environments of `E max(Reg_n, 0)`.
* `valQuant G δ' = V_{δ'}(G)`: the same with the `(1 - δ')`-quantile of `Reg_n`. In the theorem `δ' = δ`, the
  confidence that the program reads; the definition keeps them apart.
* `valMeanB G B`, `valQuantB G B δ'`: the infimum over `LearnersB B` only, the learners within cost and space `B`.

## The minimax claim (`TheoremMinimax`)

There are constants `C`, `C'` and `k` such that for every input of `TheoremUnified`'s class (`d, n ≥ 1`, rationals
`0 < δ < 1`, `0 < r0 ≤ R0`, a rational centre `a`, a compact convex `K` with `B̄(a, r0) ⊆ K ⊆ B̄(a, R0)`, a weak
membership oracle `orc` of `K`), with `U = C d^{3/2} n^{1/2} log^5 (2 d n / δ)`, `B = C' (d log (2 d n / δ) S)^k` and
`Λ = d^{3/2} n^{1/2} / log d`:

* (attained) some learner within cost and space `B` (in `LearnersB B`) has every mean payoff at most `U + n δ` and
  every quantile payoff at most `U`, against every environment with its windows;
* (upper) `V⁺(G) ≤ V⁺_B(G) ≤ U + n δ` and `V_δ(G) ≤ V_{δ,B}(G) ≤ U`;
* (lower, every `d` and `n`) `n^{1/2} / (4 √3) ≤ V⁺(G)`;
* (lower, `d ≥ 4·10^6` and `n ≥ d^10`) `1.4·10^-9 Λ ≤ V⁺(G)`; `2.8·10^-9 Λ ≤ V_δ(G)` if `δ < 1/2`; and
  `2.8·10^-9 (1 - δ)^2 Λ ≤ V_δ(G)` if `δ ≥ 1/2` and `d^3 ((1 - δ)/2)^5 ≥ 5.2·10^14 (log d)^3`.

So for `d ≥ 4·10^6`, `n ≥ d^10` and `δ < 1/2` the two values are `d^{3/2} n^{1/2}` up to the factor
`log d · log^5 (2 d n / δ)` (and the additive `n δ` for the mean), and a learner within cost and space `B` per round
reaches them up to that factor. The lower bounds on the quantile value come from a probability strictly above `δ`:
`P(Reg_n ≥ L) ≥ 1/2 > δ` (clause (b) of `TheoremLowerUProg`), and `P(Reg_n ≥ L) ≥ (1 + δ)/2 > δ` (clause (a) of
`TheoremLowerUDProg` at the failure `(1 - δ)/2`); the strict inequality is what the strict tail asks. The lower bound
`1.4·10^-9 Λ` on the mean value is the probability `1/2` of the same clause (b) read through the tail; the bound
`n^{1/2} / (4 √3)` is clause (c) of `TheoremLowerUProg` with `E max(Reg_n, 0) ≥ E Reg_n`.

## Why tails, and the outer measure

Both payoffs are read from the tail `u ↦ μ {Reg_n > u}`, the probability form, and the mean is its integral, the
layer cake formula `E max(X, 0) = ∫_0^∞ P(X > u) du`. When `Reg_n` is measurable, `meanPosOf` of its tail is
`∫ max(Reg_n, 0) dμ` (the layer cake formula; sanity module, `meanPosOf_tail_eq_integral`) and `quantileOf δ'` is
`inf {u | P(Reg_n ≤ u) ≥ 1 - δ'}`, the left-continuous `(1 - δ')`-quantile of `Reg_n`. Off the measurable sets `μ` is
Mathlib's outer measure, so both payoffs are defined for every learner. The theorem does not depend on that reading:
the upper bounds read only the program of `TheoremUnified`, whose regret `TheoremUnified` asserts measurable on every
environment of its class, and each lower bound reads, for each learner, one environment in which its regret is
measurable or integrable (`ProgProb`, `ProgMean`, `ProgProbNN`), a lower bound on the supremum. So both bounds hold for
every reading of `E max(Reg_n, 0)` and of the quantile that agrees with the usual one on measurable regrets. No
integral here has a junk value: `∫⁻` is defined for every function.

## What is not claimed

* An identity between the minimax value and the maximin value (`inf sup = sup inf`): the theorem bounds the minimax
  values from both sides.
* A match in `δ`: the lower bounds do not grow with `log (1/δ)` (that of (a) decreases as `min(δ, 1/2)^2`), while the
  upper bound carries `log^5 (2 d n / δ)`. The item "A lower bound that depends on `δ`" of the frozen
  StatementUnifiedLower.lean is now covered by (a), in the range of (a).
* Failure probabilities below the range of (a): (a) needs `d^3 min(δ, 1/2)^5 ≥ 5.2·10^14 (log d)^3`, that is
  `δ ≥ δ_U(d) = (5.2·10^14 (log d)^3 / d^3)^{1/5}` (and `δ_U(d) ≤ 1/2`).
* The rate `d^{3/2} n^{1/2} / log d` for `d < 4·10^6` or `n < d^10`, as in StatementUnifiedLower.lean; for every `d`
  and `n` the mean value is bounded below at the rate `n^{1/2}` only.
* The noisy game: the lower bounds use the noise `0`, which `TheoremUnified`'s class contains.

## Non-vacuity (AdversarialBco/Minimax/Sanity.lean)

The structural hypotheses are those of the v2.3 theorems, satisfiable by `lowerU_hyps_satisfiable` and
`progU_hyps_satisfiable` (UnifiedLower/Sanity.lean). The two arithmetic hypotheses added here have content:

* (a) of `TheoremLowerUD` and `TheoremLowerUDProg` needs `δ ≥ δ_U(d)`; `δ_U(4·10^6) = 0.4910`, so at `d = 4·10^6` it
  holds for `δ ≥ 0.4910` only, and `δ_U(d)` decreases to `0` as `d` grows (`δ_U(10^8) = 0.0799`); it holds at
  `d = 10^7`, `n = d^10`, `δ = 1/2`.
* The last clause of `TheoremMinimax` (`δ ≥ 1/2`) needs `(1 - δ)/2 ≤ 1/4` and so `d^3 / 1024 ≥ 5.2·10^14 (log d)^3`,
  which holds exactly from `d = 13 295 001` on; at `d = 10^8` it holds for `δ ∈ [1/2, 0.8402]`; it holds at
  `d = 10^8`, `n = d^10`, `δ = 1/2`, with the unit ball about the rational centre `0` and its exact membership oracle.

The witnesses of the corresponding hypotheses of `TheoremLowerUDQ` and `TheoremMinimaxQ` (StatementMinimaxQ.lean) are
proved in Lean from `e > 2.7182818283` and exact rational arithmetic. Also certified: the payoffs of every learner form
nonempty sets inside `[0, n]` (mean) and `[-n, n]` (quantile, `δ' < 1`) (`payoffs_bounded`), and `meanPosOf` of the tail
of an almost everywhere strongly measurable function is the integral of its positive part
(`meanPosOf_tail_eq_integral`). The Comparator configuration config-minimax-q.json certifies them next to the theorems.

## Junk values

`sSup` and `sInf` on `ℝ` are `0` on a set that is empty or unbounded. Every learner of `Learners` has environments with
any windows (the constant loss with zero noise), and its regret lies in `[-n, n]` on every run (losses in `[0, 1]` on
`K`, plays in `K`), so its payoffs form a nonempty set in `[-n, n]` (in `[0, n]` for the mean; for the quantile the
level is `δ' < 1`, since at `δ' ≥ 1` every `u` qualifies). The claim asserts a learner of `LearnersB B`, which lies in
`Learners`, so every `sSup` and `sInf` in the claim is that of a nonempty bounded set; the attained clause bounds every
payoff of that learner, with no `sSup`; and the claim asserts `V⁺(G) ≥ n^{1/2} / (4 √3) > 0`, which no junk `0` meets.
`meanPosOf` takes `toReal` of an integral at most `n`. `log (2 d n / δ) > 0`; `log d > 0` for `d ≥ 4·10^6`. A negative
`C` lowers `U` and makes the upper bounds harder. `min δ (1/2)` is the minimum of two reals; `ENNReal.ofReal (1 - δ)` is
`1 - δ` for `δ < 1`. In `LowerProbNN` and `ProgProbNN` the measure of `{c ≤ Reg}` is asserted only next to the
measurability of the regret.
-/

open MeasureTheory

namespace AdversarialBco

namespace Minimax

open BitRAM BitRAMO Unified UnifiedLower

/-- A learner of the game: a program of the oracle machine and the coin windows it declares. -/
structure ProgWin where
  /-- The program. -/
  prog : List InstrO
  /-- The window of the losses: the coins of index at least `D t` are independent of the history of `fresh_loss` (the
  losses of the rounds `≤ t`, the noises of the rounds `< t`, the coins of index below `D t`). -/
  D : ℕ → ℕ
  /-- The window of the noises: the coins of index at least `D' t` are independent of the history of `fresh_noise`
  (the losses and the noises of the rounds `≤ t`, the coins of index below `D' t`). -/
  D' : ℕ → ℕ

/-- The tail of the regret of `P` run from `s0` with the oracle `orc` for `n` rounds on `K`, in the environment
`(Ω, μ, coin, loss, noise)`: `u ↦ μ {Reg_n > u}` (the measure of a set of `Ω`; off the measurable sets, Mathlib's
outer measure). -/
noncomputable def tailU {d : ℕ} (P : List InstrO) (K : Set (E d)) (n : ℕ) (s0 : State d)
    (orc : (Fin d → ℚ) → ℕ → Bool) {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (coin : Ω → ℕ → Bool)
    (loss : ℕ → Ω → E d → ℝ) (noise : ℕ → Ω → ℝ) (u : ℝ) : ENNReal :=
  μ {ω | u < regretU P K n s0 (envWorld orc coin loss noise ω)}

/-- The `(1 - δ')`-quantile read from a tail `T`: the infimum of the `u` with `T u ≤ δ'`. -/
noncomputable def quantileOf (δ' : ℝ) (T : ℝ → ENNReal) : ℝ :=
  sInf {u : ℝ | T u ≤ ENNReal.ofReal δ'}

/-- The mean of the positive part read from a tail `T`: `∫_0^∞ T u du`, as a real number. -/
noncomputable def meanPosOf (T : ℝ → ENNReal) : ℝ :=
  (∫⁻ u in Set.Ioi (0 : ℝ), T u).toReal

/-- The payoffs of the learner `ℓ`: the values `pay` of the tail of its regret, over every environment of
`TheoremUnified` (a `NoisyAdv` on `K` for `n` rounds) with the windows of `ℓ`. -/
def payoffs {d : ℕ} (K : Set (E d)) (n : ℕ) (s0 : State d) (orc : (Fin d → ℚ) → ℕ → Bool)
    (pay : (ℝ → ENNReal) → ℝ) (ℓ : ProgWin) : Set ℝ :=
  {v | ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (coin : Ω → ℕ → Bool) (loss : ℕ → Ω → E d → ℝ)
    (noise : ℕ → Ω → ℝ), NoisyAdv K n ℓ.D ℓ.D' μ coin loss noise ∧
      v = pay (tailU ℓ.prog K n s0 orc μ coin loss noise)}

/-- The value of the game over the learners of `L`: the infimum over `L` of the supremum of the payoffs. -/
noncomputable def value {d : ℕ} (L : Set ProgWin) (K : Set (E d)) (n : ℕ) (s0 : State d)
    (orc : (Fin d → ℚ) → ℕ → Bool) (pay : (ℝ → ENNReal) → ℝ) : ℝ :=
  sInf ((fun ℓ => sSup (payoffs K n s0 orc pay ℓ)) '' L)

/-- The learners: the programs with windows that meet `MachineOK` (every round within some cost, the plays in `K`,
the coin windows), the hypothesis of `TheoremLowerUProg`. -/
def Learners {d : ℕ} (K : Set (E d)) (orc : (Fin d → ℚ) → ℕ → Bool) (s0 : State d) (n : ℕ) : Set ProgWin :=
  {ℓ | ∃ B : ℝ, MachineOK ℓ.prog K orc s0 n B ℓ.D ℓ.D'}

/-- The learners within cost and space `B`: clause (i) of `TheoremUnified` with the bound `B`. -/
def LearnersB {d : ℕ} (K : Set (E d)) (orc : (Fin d → ℚ) → ℕ → Bool) (s0 : State d) (n : ℕ) (B : ℝ) :
    Set ProgWin :=
  {ℓ | ∀ (f : ℕ → E d → ℝ) (noise : ℕ → ℝ) (cs : ℕ → Bool), (∀ t < n, AdmLoss K (f t)) →
    CostOKO ℓ.prog ⟨f, noise, cs, orc⟩ s0 n B ∧ SpaceOKO ℓ.prog ⟨f, noise, cs, orc⟩ s0 n B ∧
      (∀ t < n, playedO ℓ.prog ⟨f, noise, cs, orc⟩ s0 t ∈ K) ∧
      CoinWindowsOK ℓ.prog ⟨f, noise, cs, orc⟩ s0 n ℓ.D ℓ.D'}

/-- `V⁺(G)`: the minimax value in expectation of the game on the input `(d, n, δ, r0, R0, a)`, the body `K` and the
oracle `orc`: the infimum over the learners of the supremum over their environments of `E max(Reg_n, 0)`. -/
noncomputable def valMean (d n : ℕ) (δ r0 R0 : ℚ) (a : Fin d → ℚ) (K : Set (E d))
    (orc : (Fin d → ℚ) → ℕ → Bool) : ℝ :=
  value (Learners K orc (initU d n δ r0 R0 a) n) K n (initU d n δ r0 R0 a) orc meanPosOf

/-- `V_{δ'}(G)`: the minimax value of the `(1 - δ')`-quantile of `Reg_n` in the same game. -/
noncomputable def valQuant (d n : ℕ) (δ r0 R0 : ℚ) (a : Fin d → ℚ) (K : Set (E d))
    (orc : (Fin d → ℚ) → ℕ → Bool) (δ' : ℝ) : ℝ :=
  value (Learners K orc (initU d n δ r0 R0 a) n) K n (initU d n δ r0 R0 a) orc (quantileOf δ')

/-- `V⁺_B(G)`: as `valMean`, the infimum over the learners within cost and space `B` only. -/
noncomputable def valMeanB (d n : ℕ) (δ r0 R0 : ℚ) (a : Fin d → ℚ) (K : Set (E d))
    (orc : (Fin d → ℚ) → ℕ → Bool) (B : ℝ) : ℝ :=
  value (LearnersB K orc (initU d n δ r0 R0 a) n B) K n (initU d n δ r0 R0 a) orc meanPosOf

/-- `V_{δ',B}(G)`: as `valQuant`, the infimum over the learners within cost and space `B` only. -/
noncomputable def valQuantB (d n : ℕ) (δ r0 R0 : ℚ) (a : Fin d → ℚ) (K : Set (E d))
    (orc : (Fin d → ℚ) → ℕ → Bool) (B δ' : ℝ) : ℝ :=
  value (LearnersB K orc (initU d n δ r0 R0 a) n B) K n (initU d n δ r0 R0 a) orc (quantileOf δ')


open Lower (Learner IsLearnerAd regretAd) in
open RealRAM (Strategy) in
/-- A strategy of `StratsLowU K n r0` against which the regret of the learner `(μ, pol)` in the noiseless game is
measurable, nonnegative at every seed, and at least `c` with probability at least `p`. -/
def LowerProbNN {d : ℕ} {Ω : Type} [MeasurableSpace Ω] (K : Set (E d)) (n : ℕ) (r0 : ℝ) (μ : Measure Ω)
    (pol : Learner Ω d) (c : ℝ) (p : ENNReal) : Prop :=
  ∃ σ ∈ StratsLowU K n r0, Measurable (fun ω => regretAd K σ (fun t => pol t ω) n) ∧
    (∀ ω, 0 ≤ regretAd K σ (fun t => pol t ω) n) ∧ p ≤ μ {ω | c ≤ regretAd K σ (fun t => pol t ω) n}

open RealRAM (Strategy) in
/-- A strategy of `StratsLowU K n r0` in closed loop with `P`, with the noise `0`, on the program's coin space, which is
an environment of `TheoremUnified` with the windows `D`, `D'` and against which the regret `regretU` of `P` is
measurable, nonnegative on every coin sequence, and at least `c` with probability at least `p`. -/
def ProgProbNN {d : ℕ} (P : List InstrO) (K : Set (E d)) (orc : (Fin d → ℚ) → ℕ → Bool) (s0 : State d) (n : ℕ)
    (r0 : ℝ) (D D' : ℕ → ℕ) (c : ℝ) (p : ENNReal) : Prop :=
  ∃ (σ : Strategy d) (loss : ℕ → (ℕ → Bool) → E d → ℝ), σ ∈ StratsLowU K n r0 ∧ ClosedLoop P s0 orc n σ loss ∧
    NoisyAdv K n D D' coinStream id loss (fun _ _ => 0) ∧
    Measurable (fun cs => regretU P K n s0 (envWorld orc id loss (fun _ _ => 0) cs)) ∧
    (∀ cs, 0 ≤ regretU P K n s0 (envWorld orc id loss (fun _ _ => 0) cs)) ∧
    p ≤ coinStream {cs | c ≤ regretU P K n s0 (envWorld orc id loss (fun _ _ => 0) cs)}

end Minimax

open Lower UnifiedLower Minimax in
/-- **Theorem LU-D.** For every `d, n ≥ 1`, every compact convex `K` with `B̄(a, r0) ⊆ K ⊆ B̄(a, R0)`, `0 < r0 ≤ R0`,
and every measurable randomised learner on `K`, with `Λ = d^{3/2} n^{1/2} / log d`: (a) for `0 < δ < 1`, `d ≥ 4·10^6`,
`n ≥ d^10` and `d^3 min(δ, 1/2)^5 ≥ 5.2·10^14 (log d)^3`, a strategy of `StratsLowU K n r0` against which the regret is
measurable, nonnegative, and at least `1.12·10^-8 min(δ, 1/2)^2 Λ` with probability at least `1 - δ`; (b) for
`d ≥ 4·10^6` and `n ≥ d^10`, a strategy of the class with integrable regret of mean at least `1.4·10^-9 Λ`; (c) a
strategy of the class with mean regret at least `n^{1/2} / (4 √3)`, and one with regret at least `n^{1/2} / (8 √3)`
with probability at least `1/48`. -/
def TheoremLowerUD : Prop :=
  ∀ d : ℕ, 1 ≤ d → ∀ n : ℕ, 1 ≤ n → ∀ (a : E d) (r0 R0 : ℝ) (K : Set (E d)), BodyU K a r0 R0 →
    ∀ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω), IsProbabilityMeasure μ →
    ∀ pol : Learner Ω d, IsLearnerAd K n pol →
      (∀ δ : ℝ, 0 < δ → δ < 1 → 4000000 ≤ d → d ^ 10 ≤ n →
        52 * 10 ^ 13 * Real.log d ^ 3 ≤ (d : ℝ) ^ 3 * min δ (1 / 2) ^ 5 →
        LowerProbNN K n r0 μ pol
          (112 / 10 ^ 10 * min δ (1 / 2) ^ 2 * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n / Real.log d)
          (ENNReal.ofReal (1 - δ))) ∧
      (4000000 ≤ d → d ^ 10 ≤ n →
        LowerMean K n r0 μ pol (14 / 10 ^ 10 * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n / Real.log d)) ∧
      LowerMean K n r0 μ pol (Real.sqrt n / (4 * Real.sqrt 3)) ∧
      LowerProb K n r0 μ pol (Real.sqrt n / (8 * Real.sqrt 3)) (1 / 48)

open BitRAM BitRAMO Unified UnifiedLower Minimax in
/-- **Theorem LU-D for the programs of the oracle machine, in the objects of `TheoremUnified`.** For every program `P`,
every input of `TheoremUnified`'s class and every weak membership oracle of `K`, if `P` meets `MachineOK` with some
bound `B` and windows `D`, `D'`, then, for each of the clauses (a), (b), (c) of `TheoremLowerUD`, a strategy of
`StratsLowU K n r0` in closed loop with `P` with the noise `0`, an environment of `TheoremUnified` with the windows
`D`, `D'` on the program's coin space, against which the regret `regretU` of `P` satisfies that clause; the failure
probability `δ'` of (a) is a real parameter, apart from the confidence `δ` that the program reads. -/
def TheoremLowerUDProg : Prop :=
  ∀ (P : List InstrO) (d : ℕ), 1 ≤ d → ∀ n : ℕ, 1 ≤ n → ∀ δ r0 R0 : ℚ, 0 < δ → δ < 1 → 0 < r0 → r0 ≤ R0 →
  ∀ (a : Fin d → ℚ) (K : Set (E d)), IsCompact K → Convex ℝ K →
    Metric.closedBall (toE a) (r0 : ℝ) ⊆ K → K ⊆ Metric.closedBall (toE a) (R0 : ℝ) →
  ∀ orc : (Fin d → ℚ) → ℕ → Bool, WeakMemOracle K orc →
  ∀ (B : ℝ) (D D' : ℕ → ℕ), MachineOK P K orc (initU d n δ r0 R0 a) n B D D' →
    (∀ δ' : ℝ, 0 < δ' → δ' < 1 → 4000000 ≤ d → d ^ 10 ≤ n →
      52 * 10 ^ 13 * Real.log d ^ 3 ≤ (d : ℝ) ^ 3 * min δ' (1 / 2) ^ 5 →
      ProgProbNN P K orc (initU d n δ r0 R0 a) n r0 D D'
        (112 / 10 ^ 10 * min δ' (1 / 2) ^ 2 * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n / Real.log d)
        (ENNReal.ofReal (1 - δ'))) ∧
    (4000000 ≤ d → d ^ 10 ≤ n →
      ProgMean P K orc (initU d n δ r0 R0 a) n r0 D D'
        (14 / 10 ^ 10 * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n / Real.log d)) ∧
    ProgMean P K orc (initU d n δ r0 R0 a) n r0 D D' (Real.sqrt n / (4 * Real.sqrt 3)) ∧
    ProgProb P K orc (initU d n δ r0 R0 a) n r0 D D' (Real.sqrt n / (8 * Real.sqrt 3)) (1 / 48)

open BitRAM BitRAMO Unified Minimax in
/-- **Theorem MM.** Constants `C, C', k` such that, for every input of `TheoremUnified`'s class with every weak
membership oracle, with `U = C d^{3/2} √n log(2dn/δ)^5`, `B = C' (d log(2dn/δ) S)^k` and `Λ = d^{3/2} √n / log d`:
some learner within cost and space `B` has every mean payoff at most `U + n δ` and every quantile payoff at most `U`;
`V⁺(G) ≤ V⁺_B(G) ≤ U + n δ` and `V_δ(G) ≤ V_{δ,B}(G) ≤ U`; `√n / (4 √3) ≤ V⁺(G)`; and, if `d ≥ 4·10^6` and
`n ≥ d^10`, `1.4·10^-9 Λ ≤ V⁺(G)`, `2.8·10^-9 Λ ≤ V_δ(G)` for `δ < 1/2`, and `2.8·10^-9 (1 - δ)^2 Λ ≤ V_δ(G)` for
`δ ≥ 1/2` with `d^3 ((1 - δ)/2)^5 ≥ 5.2·10^14 (log d)^3`. The minimax values are bounded from both sides; no identity
between the minimax and the maximin values is claimed. -/
def TheoremMinimax : Prop :=
  ∃ (C C' : ℝ) (k : ℕ),
    ∀ d : ℕ, 1 ≤ d → ∀ n : ℕ, 1 ≤ n → ∀ δ r0 R0 : ℚ, 0 < δ → δ < 1 → 0 < r0 → r0 ≤ R0 →
    ∀ (a : Fin d → ℚ) (K : Set (E d)), IsCompact K → Convex ℝ K →
      Metric.closedBall (toE a) (r0 : ℝ) ⊆ K → K ⊆ Metric.closedBall (toE a) (R0 : ℝ) →
    ∀ orc : (Fin d → ℚ) → ℕ → Bool, WeakMemOracle K orc →
      (∃ ℓ ∈ LearnersB K orc (initU d n δ r0 R0 a) n
          (C' * ((d : ℝ) * Real.log (2 * d * n / (δ : ℝ)) * sizeU δ r0 R0 a) ^ k),
        (∀ v ∈ payoffs K n (initU d n δ r0 R0 a) orc meanPosOf ℓ,
          v ≤ C * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n * Real.log (2 * d * n / (δ : ℝ)) ^ 5 + n * (δ : ℝ)) ∧
        ∀ v ∈ payoffs K n (initU d n δ r0 R0 a) orc (quantileOf (δ : ℝ)) ℓ,
          v ≤ C * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n * Real.log (2 * d * n / (δ : ℝ)) ^ 5) ∧
      valMean d n δ r0 R0 a K orc ≤
        valMeanB d n δ r0 R0 a K orc (C' * ((d : ℝ) * Real.log (2 * d * n / (δ : ℝ)) * sizeU δ r0 R0 a) ^ k) ∧
      valMeanB d n δ r0 R0 a K orc (C' * ((d : ℝ) * Real.log (2 * d * n / (δ : ℝ)) * sizeU δ r0 R0 a) ^ k) ≤
        C * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n * Real.log (2 * d * n / (δ : ℝ)) ^ 5 + n * (δ : ℝ) ∧
      valQuant d n δ r0 R0 a K orc δ ≤
        valQuantB d n δ r0 R0 a K orc
          (C' * ((d : ℝ) * Real.log (2 * d * n / (δ : ℝ)) * sizeU δ r0 R0 a) ^ k) δ ∧
      valQuantB d n δ r0 R0 a K orc
          (C' * ((d : ℝ) * Real.log (2 * d * n / (δ : ℝ)) * sizeU δ r0 R0 a) ^ k) δ ≤
        C * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n * Real.log (2 * d * n / (δ : ℝ)) ^ 5 ∧
      Real.sqrt n / (4 * Real.sqrt 3) ≤ valMean d n δ r0 R0 a K orc ∧
      (4000000 ≤ d → d ^ 10 ≤ n →
        14 / 10 ^ 10 * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n / Real.log d ≤ valMean d n δ r0 R0 a K orc ∧
        ((δ : ℝ) < 1 / 2 →
          28 / 10 ^ 10 * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n / Real.log d ≤ valQuant d n δ r0 R0 a K orc δ) ∧
        (1 / 2 ≤ (δ : ℝ) → 52 * 10 ^ 13 * Real.log d ^ 3 ≤ (d : ℝ) ^ 3 * ((1 - (δ : ℝ)) / 2) ^ 5 →
          28 / 10 ^ 10 * (1 - (δ : ℝ)) ^ 2 * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n / Real.log d ≤
            valQuant d n δ r0 R0 a K orc δ))

end AdversarialBco
