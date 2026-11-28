/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Matched.Upper
public import AdversarialBco.Matched.Lower
public import AdversarialBco.Matched.Sanity
public import AdversarialBco.LowerDeltaQ.Sanity
public import AdversarialBco.Grow.Main
public import AdversarialBco.UW.Main
public import AdversarialBco.LowerDeltaQ.Statement

@[expose] public section

/-!
# The matched minimax theorem

`theoremMinimaxMatched_of : TheoremUW → TheoremLowerUDProgQ → TheoremGrowGProg → TheoremMinimaxMatched`:

* the upper bounds and the learner within cost and space `B`: `minimax_upper_of_UW` (the bound on the mean value
  derived from the probability clause of `TheoremUW` and `Reg_n ≤ n`);
* `√n / (4 √3) ≤ V⁺(G)`: `minimax_lower_small_of_lowerUDQ`, clause (c) of `TheoremLowerUDProgQ`;
* `3.71·10^-9 Λ / log d ≤ V⁺(G)`: `minimax_lower_of_lowerUDQ`, clause (a) of `TheoremLowerUDProgQ` at the failure
  `1/2`, read through the tail;
* the matched clause: `minimax_matched_of`, from the same clause (a) and `TheoremGrowGProg`;
* the clause for `δ ≥ 1/2`: `minimax_lower_high_of_lowerUDQ`, clause (a) at the failure `(1 - δ)/2`.

Nothing deep is proved in the reduction: the three theorems are hypotheses. `theoremMinimaxMatched` applies it to
`UW.theoremUW` (UW/Main.lean), `LowerDeltaQ.theoremLowerUDProgQ` (LowerDeltaQ/Statement.lean) and
`Grow.theoremGrowGProg` (Grow/Main.lean). The module imports the sanity modules, AdversarialBco.UW.Main and
AdversarialBco.Grow.Main so that it is the solution module of the Comparator configuration config-matched.json
(`UW.theoremUW`, `Grow.theoremGrowG`, `Grow.theoremGrowGProg`, `Matched.theoremMinimaxMatched` and the witnesses).
-/

namespace AdversarialBco.Matched

open BitRAM BitRAMO Unified UnifiedLower Minimax

/-- **The matched minimax theorem from `TheoremUW`, `TheoremLowerUDProgQ` and `TheoremGrowGProg`.** -/
theorem theoremMinimaxMatched_of (hU : TheoremUW) (hLD : TheoremLowerUDProgQ) (hG : TheoremGrowGProg) :
    TheoremMinimaxMatched := by
  obtain ⟨C, C', k, -, h⟩ := minimax_upper_of_UW hU
  refine ⟨C, C', k, fun d hd n hn δ r0 R0 hδ0 hδ1 hr0 hr0R a K hK hc hb1 hb2 orc horc => ?_⟩
  obtain ⟨hne, h1, h2, h3, h4⟩ := h d hd n hn δ r0 R0 hδ0 hδ1 hr0 hr0R a K hK hc hb1 hb2 orc horc
  have hLne := learners_nonempty_of_UW hU d hd n hn δ r0 R0 hδ0 hδ1 hr0 hr0R a K hK hc hb1 hb2 orc horc
  refine ⟨hne, h1, h2, h3, h4,
    minimax_lower_small_of_lowerUDQ hLD hd hn hδ0 hδ1 hr0 hr0R a hK hc hb1 hb2 horc hLne, fun hd4 hn10 => ?_⟩
  obtain ⟨hM, -⟩ := minimax_lower_of_lowerUDQ hLD hd4 hn10 hδ0 hδ1 hr0 hr0R a hK hc hb1 hb2 horc hLne
  refine ⟨le_of_eq_of_le (by ring) hM, fun hδ hw =>
    minimax_matched_of hLD hG hd4 hn10 hδ0 hδ1 hr0 hr0R a hK hc hb1 hb2 horc hLne hδ hw, fun _ hr1 hr2 =>
    minimax_lower_high_of_lowerUDQ hLD hd4 hn10 hδ0 hδ1 hr0 hr0R a hK hc hb1 hb2 horc hLne hr1 hr2⟩

/-- **Theorem MM matched in `δ`** (`TheoremMinimaxMatched`, StatementMatched.lean). -/
theorem theoremMinimaxMatched : TheoremMinimaxMatched :=
  theoremMinimaxMatched_of UW.theoremUW LowerDeltaQ.theoremLowerUDProgQ Grow.theoremGrowGProg

end AdversarialBco.Matched
