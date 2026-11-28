#!/bin/bash
# Writes, or checks, the Comparator challenges of the statement files StatementUnified.lean (over StatementBitRAMO.lean
# and its machine StatementBitRAM.lean), StatementUW.lean, StatementConj1BitHP.lean (over StatementConj1Bit.lean),
# StatementMinimaxQ.lean (over StatementMinimax.lean and StatementConj1LowerPolyD.lean), StatementMatched.lean and StatementConj1.lean (Theorem body on the real RAM),
# with the statement files they import. Each challenge imports Mathlib only and copies the statement files verbatim,
# cut at the same module boundaries as the library:
#   AdversarialBco/ChallengeBase/StatementPoly.lean        the definitions E, AdmLoss, Advs of Statement.lean and
#                                                          StatementPoly.lean;
#   AdversarialBco/ChallengeBase/StatementConj1.lean       StatementConj1.lean, over the first;
#   AdversarialBco/ChallengeBase/StatementConj1Poly.lean   StatementConj1Poly.lean, over the second;
#   AdversarialBco/ChallengeBase/StatementBitRAM.lean      StatementBitRAM.lean, over the first;
#   AdversarialBco/ChallengeBase/StatementConj1Lower.lean  StatementConj1Lower.lean, over the second;
#   AdversarialBco/ChallengeBase/StatementBitRAMO.lean     StatementBitRAMO.lean, the machine with the oracle, over the
#                                                          fourth;
#   AdversarialBco/ChallengeBase/StatementUnified.lean     StatementUnified.lean, over the first and the sixth;
#   AdversarialBco/ChallengeBase/StatementUnifiedLower.lean  StatementUnifiedLower.lean, over the seventh and the
#                                                          fifth;
#   AdversarialBco/ChallengeBase/StatementMinimax.lean     StatementMinimax.lean, over the eighth;
#   AdversarialBco/ChallengeBase/StatementConj1LowerPolyD.lean  StatementConj1LowerPolyD.lean, over the fifth and the
#                                                          third;
#   AdversarialBco/ChallengeBase/StatementMinimaxQ.lean    StatementMinimaxQ.lean, over the ninth and the tenth;
#   AdversarialBco/ChallengeBase/StatementUW.lean          StatementUW.lean, over the seventh;
#   AdversarialBco/ChallengeBase/StatementConj1Bit.lean    StatementConj1Bit.lean, over the third and the fourth;
#   AdversarialBco/ChallengeUnified.lean                   StatementUnified.lean verbatim over the first and the sixth,
#                                                          its theorem and five non-vacuity witnesses, by `sorry`;
#   AdversarialBco/ChallengeUW.lean                        StatementUW.lean verbatim over the seventh, its theorem,
#                                                          Theorem U from it and the five witnesses of the previous
#                                                          challenge, by `sorry`;
#   AdversarialBco/ChallengeMinimaxQ.lean                  StatementMinimaxQ.lean verbatim over the ninth and the
#                                                          tenth, its four theorems, clause (b) of the two theorems of
#                                                          StatementUnifiedLower.lean from them and ten non-vacuity
#                                                          witnesses, by `sorry`;
#   AdversarialBco/ChallengeMatched.lean                   StatementMatched.lean verbatim over the eleventh and the
#                                                          twelfth, Theorem UW, its three theorems, the reduction and
#                                                          seven non-vacuity witnesses, by `sorry`;
#   AdversarialBco/ChallengeConj1BitHP.lean                StatementConj1BitHP.lean verbatim over the thirteenth, its
#                                                          theorem, its reduction to StatementConj1Bit.lean and three
#                                                          non-vacuity witnesses, by `sorry`;
#   AdversarialBco/ChallengeConj1.lean                     over the second, the theorem of StatementConj1.lean and
#                                                          three non-vacuity witnesses, by `sorry`;
# Usage, from the root of the repository: code/formal-proof/challenges.sh [--write]
#   prints `CHALLENGES OK` (exit 0), or the differences and `CHALLENGES DIFFER` (exit 1); --write writes them.
set -eu
d=AdversarialBco
st=$d/Statement.lean; sp=$d/StatementPoly.lean; sc=$d/StatementConj1.lean; scp=$d/StatementConj1Poly.lean
sr=$d/StatementBitRAM.lean; scl=$d/StatementConj1Lower.lean; so=$d/StatementBitRAMO.lean; su=$d/StatementUnified.lean
sl=$d/StatementUnifiedLower.lean; sm=$d/StatementMinimax.lean; spd=$d/StatementConj1LowerPolyD.lean
sq=$d/StatementMinimaxQ.lean; sw=$d/StatementUW.lean; sma=$d/StatementMatched.lean
sb=$d/StatementConj1Bit.lean; sh=$d/StatementConj1BitHP.lean
header() {
  printf '/-\nCopyright (c) 2026 mt0-svg. All rights reserved.\nReleased under Apache 2.0 license as described in the file LICENSE.\nAuthors: mt0-svg\n-/\n'
}
# The body of a statement file: without its header, `module`, its imports and the line that opens the public section.
body() { sed '1,/^-\/$/d' "$1" | sed '/^module$/d; /^public import /d; /^@\[expose\] public section$/d' | sed '/./,$!d'; }
imports() { sed -n 's/^public import \(Mathlib\..*\)$/public import \1/p' "$1"; }
# sorries NAME TYPE DOC: one theorem proved by `sorry`.
sorries() { printf '/-- %s -/\ntheorem %s : %s := by\n  sorry\n\n' "$3" "$1" "$2"; }
defs=$(awk '/^\/-- The ambient space/ { p = 1 } /^end AdversarialBco$/ { p = 0 } p' "$st")
[ "$(printf '%s\n' "$defs" | sed -nE 's/^(abbrev|def) ([A-Za-z]+) .*/\2/p' | tr '\n' ' ')" = "E AdmLoss Advs " ] ||
  { echo "$st: the block copied is not the definitions E, AdmLoss, Advs"; exit 1; }
for f in "$sp" "$sc" "$scp" "$sr" "$scl" "$so" "$su" "$sl" "$sm" "$spd" "$sq" "$sw" "$sma" "$sb" "$sh"; do
  [ "$(tail -1 "$f")" = "end AdversarialBco" ] || { echo "$f: last line is not the end of its namespace"; exit 1; }
done
# base N MODULE-FILE DESCRIPTION IMPORT...: a module of ChallengeBase, the statement file verbatim over the imports.
base() {
  local f=$1 desc=$2; shift 2
  header
  printf -- '-- %s\n' "$desc"
  printf 'module\n\n'
  for i in "$@"; do printf 'public import AdversarialBco.ChallengeBase.%s\n' "$i"; done
  imports "$f"
  printf '\n@[expose] public section\n\n'
  body "$f"
}
base1() {
  header
  cat <<'EOT'
-- Comparator challenges, first module, importing Mathlib only: the definitions `E`, `AdmLoss`, `Advs` of
-- AdversarialBco/Statement.lean and AdversarialBco/StatementPoly.lean verbatim (code/formal-proof/challenges.sh).
module

EOT
  imports "$st"; imports "$sp"
  printf '\n@[expose] public section\n\nsection\n\nopen MeasureTheory Real\n\nnamespace AdversarialBco\n\n'
  printf '%s\n' "$defs"
  printf '\nend AdversarialBco\n\nend\n\n'
  body "$sp"
}
base2() { base "$sc" 'Comparator challenges, second module: AdversarialBco/StatementConj1.lean verbatim over the first module
-- (code/formal-proof/challenges.sh).' StatementPoly; }
base3() { base "$scp" 'Comparator challenges, third module: AdversarialBco/StatementConj1Poly.lean verbatim over the second module
-- (code/formal-proof/challenges.sh).' StatementConj1; }
base4() { base "$sr" 'Comparator challenges, fourth module: the machine, AdversarialBco/StatementBitRAM.lean verbatim over the first
-- module (code/formal-proof/challenges.sh).' StatementPoly; }
base5() { base "$scl" 'Comparator challenges, fifth module: AdversarialBco/StatementConj1Lower.lean verbatim over the second module
-- (code/formal-proof/challenges.sh).' StatementConj1; }
base6() { base "$so" 'Comparator challenges, sixth module: the machine with the oracle, AdversarialBco/StatementBitRAMO.lean verbatim
-- over the fourth module (code/formal-proof/challenges.sh).' StatementBitRAM; }
base7() { base "$su" 'Comparator challenges, seventh module: AdversarialBco/StatementUnified.lean verbatim over the first and sixth
-- modules (code/formal-proof/challenges.sh).' StatementPoly StatementBitRAMO; }
base8() { base "$sl" 'Comparator challenges, eighth module: AdversarialBco/StatementUnifiedLower.lean verbatim over the seventh and
-- fifth modules (code/formal-proof/challenges.sh).' StatementUnified StatementConj1Lower; }
base9() { base "$sm" 'Comparator challenges, ninth module: AdversarialBco/StatementMinimax.lean verbatim over the eighth module
-- (code/formal-proof/challenges.sh).' StatementUnifiedLower; }
base10() { base "$spd" 'Comparator challenges, tenth module: AdversarialBco/StatementConj1LowerPolyD.lean verbatim over the fifth and
-- third modules (code/formal-proof/challenges.sh).' StatementConj1Lower StatementConj1Poly; }
base11() { base "$sq" 'Comparator challenges, eleventh module: AdversarialBco/StatementMinimaxQ.lean verbatim over the ninth and tenth
-- modules (code/formal-proof/challenges.sh).' StatementMinimax StatementConj1LowerPolyD; }
base12() { base "$sw" 'Comparator challenges, twelfth module: AdversarialBco/StatementUW.lean verbatim over the seventh module
-- (code/formal-proof/challenges.sh).' StatementUnified; }
base13() { base "$sb" 'Comparator challenges, thirteenth module: AdversarialBco/StatementConj1Bit.lean verbatim over the third and
-- fourth modules (code/formal-proof/challenges.sh).' StatementConj1Poly StatementBitRAM; }
# The theorem of config-unified.json and its five non-vacuity witnesses, which the solution proves in
# AdversarialBco/UW/TheoremU.lean and AdversarialBco/Unified/Sanity.lean.
blockU() {
  cat <<'EOT'
/-- Theorem U: the theorem that a solution module proves. -/
theorem theoremUnified : TheoremUnified := by
  sorry

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

EOT
}
# The five witnesses of the hypotheses of `TheoremUnified`, which are those of `TheoremUW`
# (AdversarialBco/Unified/Sanity.lean).
blockUS() {
  cat <<'EOT'
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

EOT
}
# Theorem UW and Theorem U from it, which the solution proves in AdversarialBco/UW/Main.lean and
# AdversarialBco/UW/ToUnified.lean.
blockUW() {
  cat <<'EOT'
namespace UW

/-- **Theorem UW** (`TheoremUW`): the theorem that a solution module proves. -/
theorem theoremUW : TheoremUW := by
  sorry

/-- **Theorem U from Theorem UW**, at the constant `2 max(C, 0)` with UW's program, cost constants and windows. -/
theorem theoremUnified_of_UW (h : TheoremUW) : TheoremUnified := by
  sorry

end UW

EOT
}
# The four theorems of StatementMinimaxQ.lean and its ten non-vacuity witnesses, which the solution proves in
# AdversarialBco/LowerDeltaQ/{Statement,Minimax,Conj1,Sanity}.lean, Conj1LowerPolyD/Sanity.lean, Minimax/Sanity.lean
# and UnifiedLower/Sanity.lean.
blockMQ() {
  cat <<'EOT'
namespace LowerDeltaQ

/-- **Theorem LU-DQ** (`TheoremLowerUDQ`). -/
theorem theoremLowerUDQ : TheoremLowerUDQ := by
  sorry

/-- **Theorem LU-DQ for the programs of the oracle machine, in the objects of `TheoremUnified`**
(`TheoremLowerUDProgQ`). -/
theorem theoremLowerUDProgQ : TheoremLowerUDProgQ := by
  sorry

/-- **Theorem MM at the constants of Theorem LU-DQ** (`TheoremMinimaxQ`). -/
theorem theoremMinimaxQ : TheoremMinimaxQ := by
  sorry

end LowerDeltaQ

/-- The lower half of Conjecture 1 on a polytope of the class of Bubeck, Eldan and Lee at `3.71·10^-9`
(`TheoremConj1LowerPolyDQ`). -/
theorem theoremConj1LowerPolyDQ_holds : TheoremConj1LowerPolyDQ := by
  sorry

namespace LowerDeltaQ.Sanity

open BitRAM BitRAMO

/-- The hypotheses of clause (a) of `TheoremLowerUDQ` and `TheoremLowerUDProgQ` hold together at `d = 10^7`,
`n = d^10`, `δ = 1/2`. -/
theorem lowerUDQ_a_hyps_satisfiable :
    ∃ (d n : ℕ) (δ : ℝ), 1 ≤ d ∧ 1 ≤ n ∧ 0 < δ ∧ δ < 1 ∧ 4000000 ≤ d ∧ d ^ 10 ≤ n ∧
      1024 * (120 * Real.log d + 68) ≤ min δ (1 / 2) * d ∧
      10 * (120 * Real.log d + 68) ≤ min δ (1 / 2) ^ (3 / 2 : ℝ) * d := by
  sorry

/-- The hypotheses of clause (a) of `TheoremLowerUDQ` and `TheoremLowerUDProgQ` hold together at `d = 10^8`,
`n = d^10` and a failure probability `δ = 1/20` below `1/2`. -/
theorem lowerUDQ_a_small_hyps_satisfiable :
    ∃ (d n : ℕ) (δ : ℝ), 1 ≤ d ∧ 1 ≤ n ∧ 0 < δ ∧ δ < 1 / 2 ∧ 4000000 ≤ d ∧ d ^ 10 ≤ n ∧
      1024 * (120 * Real.log d + 68) ≤ min δ (1 / 2) * d ∧
      10 * (120 * Real.log d + 68) ≤ min δ (1 / 2) ^ (3 / 2 : ℝ) * d := by
  sorry

/-- The hypotheses of the last clause of `TheoremMinimaxQ` hold together at `d = 10^8`, `n = d^10` and the rational
`δ = 1/2`, with the closed unit ball about the rational centre `0`, compact, convex, with a weak membership oracle. -/
theorem minimaxQ_high_hyps_satisfiable :
    ∃ (d n : ℕ) (δ : ℚ), 1 ≤ d ∧ 1 ≤ n ∧ 0 < δ ∧ δ < 1 ∧ 4000000 ≤ d ∧ d ^ 10 ≤ n ∧ 1 / 2 ≤ (δ : ℝ) ∧
      1024 * (120 * Real.log d + 68) ≤ (1 - (δ : ℝ)) / 2 * d ∧
      10 * (120 * Real.log d + 68) ≤ ((1 - (δ : ℝ)) / 2) ^ (3 / 2 : ℝ) * d ∧
      IsCompact (Metric.closedBall (BitRAM.toE (0 : Fin d → ℚ)) 1) ∧
      Convex ℝ (Metric.closedBall (BitRAM.toE (0 : Fin d → ℚ)) 1) ∧
      ∃ orc : (Fin d → ℚ) → ℕ → Bool,
        BitRAMO.WeakMemOracle (Metric.closedBall (BitRAM.toE (0 : Fin d → ℚ)) 1) orc := by
  sorry

open MeasureTheory RealRAM in
/-- The bound of `TheoremConj1LowerPolyDQ` is positive and at most `n / 2` on its regime. -/
theorem boundDQ_facts {d n : ℕ} (hd : 4000000 ≤ d) (hn : d ^ 10 ≤ n) :
    0 < 371 / 10 ^ 11 * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n / Real.log d ∧
      371 / 10 ^ 11 * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n / Real.log d ≤ n / 2 := by
  sorry

open MeasureTheory RealRAM in
/-- On every nonempty convex body, the zero strategy is in the class and fails the bound of `TheoremConj1LowerPolyDQ`
against every learner. -/
theorem zeroStrat_fails_of_nonemptyDQ {d n : ℕ} (hd : 4000000 ≤ d) (hn : d ^ 10 ≤ n) {K : Set (E d)}
    (hK : K.Nonempty) (hKc : Convex ℝ K) {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (pol : Lower.Learner Ω d) :
    (fun _ _ _ _ => 0 : Strategy d) ∈ Lower.StratsLip K n ∧
      ¬ 371 / 10 ^ 11 * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n / Real.log d ≤
        ∫ ω, Lower.regretAd K (fun _ _ _ _ => 0) (fun t => pol t ω) n ∂μ := by
  sorry

end LowerDeltaQ.Sanity

namespace Lower.PolyDSanity

open RealRAM

/-- On every body `K` with a point `c`, the constant learner that plays `c` is a learner of the class, for every `n`. -/
theorem constLearner_mem_of_mem {d : ℕ} {K : Set (E d)} {c : E d} (hc : c ∈ K) (n : ℕ) :
    IsLearnerAd (Ω := Unit) K n (fun _ _ _ _ => c) := by
  sorry

end Lower.PolyDSanity

namespace Minimax.MinimaxSanity

open BitRAM BitRAMO

/-- The payoffs of every learner of `Learners` on a convex nonempty `K` form nonempty sets inside `[0, n]` for the mean
and inside `[-n, n]` for the quantile at every level `δ' < 1`. -/
theorem payoffs_bounded {d : ℕ} (K : Set (E d)) (orc : (Fin d → ℚ) → ℕ → Bool) (s0 : State d) (n : ℕ)
    (ℓ : ProgWin) (hK : Convex ℝ K) (hne : K.Nonempty) (hℓ : ℓ ∈ Learners K orc s0 n) :
    (payoffs K n s0 orc meanPosOf ℓ).Nonempty ∧ payoffs K n s0 orc meanPosOf ℓ ⊆ Set.Icc 0 (n : ℝ) ∧
      ∀ δ' : ℝ, δ' < 1 → (payoffs K n s0 orc (quantileOf δ') ℓ).Nonempty ∧
        payoffs K n s0 orc (quantileOf δ') ℓ ⊆ Set.Icc (-(n : ℝ)) n := by
  sorry

/-- The mean of the positive part read from the tail of an almost everywhere strongly measurable `X` is
`∫ max(X, 0) dμ`. -/
theorem meanPosOf_tail_eq_integral {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ℝ)
    (hX : AEStronglyMeasurable X μ) : meanPosOf (fun u => μ {ω | u < X ω}) = ∫ ω, max (X ω) 0 ∂μ := by
  sorry

end Minimax.MinimaxSanity

namespace UnifiedLower.LowerSanity

open BitRAM BitRAMO Unified
open RealRAM (Strategy Strats regretPts)
open Lower (Learner IsLearnerAd regretAd)

/-- The hypotheses of `TheoremLowerU` hold for every `d` and `n`: the closed unit ball about `0` (`r0 = R0 = 1`) and
the constant learner `0` on `Unit` with the Dirac measure. -/
theorem lowerU_hyps_satisfiable (d n : ℕ) :
    BodyU (Metric.closedBall (0 : E d) 1) 0 1 1 ∧ IsProbabilityMeasure (Measure.dirac ()) ∧
      IsLearnerAd (Metric.closedBall (0 : E d) 1) n (fun _ _ _ _ => 0 : Learner Unit d) := by
  sorry

/-- The hypotheses of `TheoremLowerUProg` hold for every `d`, `n` and `δ`: the closed unit ball about the rational
centre `0` (`r0 = R0 = 1`) is compact and convex, has an exact membership oracle, which is a weak membership oracle;
and for every oracle the program `M (-1) := -2`, `play (-1)`, `jmp 1`, which plays the point `0` in every round and
reads no coin, meets `MachineOK` on the input with some cost bound `B` and the windows `D = D' = 0`. -/
theorem progU_hyps_satisfiable (d n : ℕ) (δ : ℚ) :
    IsCompact (Metric.closedBall (toE (0 : Fin d → ℚ)) 1) ∧
      Convex ℝ (Metric.closedBall (toE (0 : Fin d → ℚ)) 1) ∧
      Metric.closedBall (toE (0 : Fin d → ℚ)) ((1 : ℚ) : ℝ) ⊆ Metric.closedBall (toE (0 : Fin d → ℚ)) 1 ∧
      Metric.closedBall (toE (0 : Fin d → ℚ)) 1 ⊆ Metric.closedBall (toE (0 : Fin d → ℚ)) ((1 : ℚ) : ℝ) ∧
      (∃ orc : (Fin d → ℚ) → ℕ → Bool, WeakMemOracle (Metric.closedBall (toE (0 : Fin d → ℚ)) 1) orc ∧
        ∀ y k, orc y k = true ↔ toE y ∈ Metric.closedBall (toE (0 : Fin d → ℚ)) 1) ∧
      ∀ orc : (Fin d → ℚ) → ℕ → Bool, ∃ B : ℝ,
        MachineOK [.base (.const (-1) (-2)), .base (.play (-1)), .base (.jmp 1)]
          (Metric.closedBall (toE (0 : Fin d → ℚ)) 1) orc (initU d n δ 1 1 0) n B (fun _ => 0) (fun _ => 0) := by
  sorry

end UnifiedLower.LowerSanity

EOT
}
# Clause (b) of `TheoremLowerU` and of `TheoremLowerUProg` (StatementUnifiedLower.lean, release v2.3) from Theorem LU-DQ
# at `δ = 1/2`, which the solution proves in AdversarialBco/LowerDeltaQ/LowerUB.lean.
blockLUB() {
  cat <<'EOT'
namespace LowerDeltaQ

open BitRAM BitRAMO Unified UnifiedLower Minimax
open RealRAM (Strategy)
open Lower (Learner IsLearnerAd regretAd)

/-- **Clause (b) of `TheoremLowerU` from `TheoremLowerUDQ`**: at `δ = 1/2`, clause (a). -/
theorem lowerU_b_of_UDQ (h : TheoremLowerUDQ) :
    ∀ d : ℕ, 1 ≤ d → ∀ n : ℕ, 1 ≤ n → ∀ (a : E d) (r0 R0 : ℝ) (K : Set (E d)), BodyU K a r0 R0 →
    ∀ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω), IsProbabilityMeasure μ →
    ∀ pol : Learner Ω d, IsLearnerAd K n pol → 4000000 ≤ d → d ^ 10 ≤ n →
      LowerProb K n r0 μ pol (28 / 10 ^ 10 * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n / Real.log d) (1 / 2) := by
  sorry

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
  sorry

end LowerDeltaQ
EOT
}
# Theorem UW, the three theorems of StatementMatched.lean, the reduction and the seven non-vacuity witnesses, which the
# solution proves in AdversarialBco/UW/Main.lean, Grow/Main.lean, Matched/Main.lean, Matched/Sanity.lean,
# LowerDeltaQ/Sanity.lean and UnifiedLower/Sanity.lean.
blockMM() {
  cat <<'EOT'
namespace UW

/-- **Theorem UW** (`TheoremUW`). -/
theorem theoremUW : TheoremUW := by
  sorry

end UW

namespace Grow

/-- **Route G** (`TheoremGrowG`). -/
theorem theoremGrowG : TheoremGrowG := by
  sorry

/-- **Route G for the programs of the oracle machine, in the objects of `TheoremUnified`** (`TheoremGrowGProg`). -/
theorem theoremGrowGProg : TheoremGrowGProg := by
  sorry

end Grow

namespace Matched

/-- **Theorem MM matched in `δ`** (`TheoremMinimaxMatched`). -/
theorem theoremMinimaxMatched : TheoremMinimaxMatched := by
  sorry

/-- **The matched minimax theorem from `TheoremUW`, `TheoremLowerUDProgQ` and `TheoremGrowGProg`.** -/
theorem theoremMinimaxMatched_of (hU : TheoremUW) (hLD : TheoremLowerUDProgQ) (hG : TheoremGrowGProg) :
    TheoremMinimaxMatched := by
  sorry

end Matched

namespace Matched.MatchedSanity

open BitRAM BitRAMO

/-- The hypotheses of `TheoremGrowG` and `TheoremGrowGProg` hold together at `d = 4·10^6`, `n = d^10`,
`δ = 2^{-d^4}`. -/
theorem growG_hyps_satisfiable :
    ∃ (d n : ℕ) (δ : ℝ), 1 ≤ d ∧ 1 ≤ n ∧ 0 < δ ∧ 4000000 ≤ d ∧ 60 ≤ Real.log (1 / δ) ∧
      (d : ℝ) ^ 6 * Real.log (1 / δ) ≤ n := by
  sorry

/-- The hypotheses of the matched clause of `TheoremMinimaxMatched` hold together at `d = 4·10^6`, `n = d^10` and the
rational `δ = 2^{-d^4}`, with `log (1/δ) ≥ 60`, and the closed unit ball about the rational centre `0`, compact,
convex, with a weak membership oracle. -/
theorem matched_hyps_satisfiable :
    ∃ (d n : ℕ) (δ : ℚ), 1 ≤ d ∧ 1 ≤ n ∧ 0 < δ ∧ δ < 1 ∧ 4000000 ≤ d ∧ d ^ 10 ≤ n ∧ (δ : ℝ) < 1 / 2 ∧
      Real.log (1 / (δ : ℝ)) ≤ n / (d : ℝ) ^ 6 ∧ 60 ≤ Real.log (1 / (δ : ℝ)) ∧
      IsCompact (Metric.closedBall (BitRAM.toE (0 : Fin d → ℚ)) 1) ∧
      Convex ℝ (Metric.closedBall (BitRAM.toE (0 : Fin d → ℚ)) 1) ∧
      ∃ orc : (Fin d → ℚ) → ℕ → Bool,
        BitRAMO.WeakMemOracle (Metric.closedBall (BitRAM.toE (0 : Fin d → ℚ)) 1) orc := by
  sorry

/-- At the point of `matched_hyps_satisfiable`, the lower bound of the matched clause of `TheoremMinimaxMatched` is
more than `10^8` times the bound `7.42·10^-9 d^{3/2} n^{1/2} / log d` of `TheoremMinimaxQ`. -/
theorem matched_exceeds_flat :
    10 ^ 8 * (742 / 10 ^ 11 * ((4000000 : ℕ) : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt ((4000000 ^ 10 : ℕ) : ℝ) /
        Real.log ((4000000 : ℕ) : ℝ)) <
      7 / 10 ^ 9 * (((4000000 : ℕ) : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt ((4000000 ^ 10 : ℕ) : ℝ) /
          Real.log ((4000000 : ℕ) : ℝ) +
        ((4000000 : ℕ) : ℝ) * Real.sqrt (((4000000 ^ 10 : ℕ) : ℝ) *
            Real.log (1 / (((1 / 2 : ℚ) ^ (4000000 ^ 4) : ℚ) : ℝ))) /
          (Real.log ((4000000 : ℕ) : ℝ) * Real.sqrt (Real.log ((4000000 ^ 10 : ℕ) : ℝ)))) := by
  sorry

open Unified UnifiedLower in
/-- Every hypothesis of `TheoremGrowGProg` and of the matched clause of `TheoremMinimaxMatched` holds at one point:
`d = 4·10^6`, `n = d^10`, the rational `δ = δ' = 2^{-d^4}`, the closed unit ball about the rational centre `0`
(`r0 = R0 = 1`) with a weak membership oracle, and the three-instruction program of `progU_hyps_satisfiable`, which
meets `MachineOK` with the windows `D = D' = 0` and some budget `B`. -/
theorem growGProg_matched_hyps_satisfiable :
    ∃ (d n : ℕ) (δ r0 R0 : ℚ) (a : Fin d → ℚ) (K : Set (E d)) (orc : (Fin d → ℚ) → ℕ → Bool) (P : List InstrO)
      (B : ℝ) (D D' : ℕ → ℕ),
      1 ≤ d ∧ 1 ≤ n ∧ 0 < δ ∧ δ < 1 ∧ 0 < r0 ∧ r0 ≤ R0 ∧ IsCompact K ∧ Convex ℝ K ∧
      Metric.closedBall (toE a) (r0 : ℝ) ⊆ K ∧ K ⊆ Metric.closedBall (toE a) (R0 : ℝ) ∧
      WeakMemOracle K orc ∧ MachineOK P K orc (initU d n δ r0 R0 a) n B D D' ∧
      (0 : ℝ) < δ ∧ 4000000 ≤ d ∧ 60 ≤ Real.log (1 / (δ : ℝ)) ∧ (d : ℝ) ^ 6 * Real.log (1 / (δ : ℝ)) ≤ n ∧
      d ^ 10 ≤ n ∧ (δ : ℝ) < 1 / 2 ∧ Real.log (1 / (δ : ℝ)) ≤ n / (d : ℝ) ^ 6 := by
  sorry

end Matched.MatchedSanity

namespace LowerDeltaQ.Sanity

open BitRAM BitRAMO

/-- The hypotheses of the last clause of `TheoremMinimaxQ` hold together at `d = 10^8`, `n = d^10` and the rational
`δ = 1/2`, with the closed unit ball about the rational centre `0`, compact, convex, with a weak membership oracle. -/
theorem minimaxQ_high_hyps_satisfiable :
    ∃ (d n : ℕ) (δ : ℚ), 1 ≤ d ∧ 1 ≤ n ∧ 0 < δ ∧ δ < 1 ∧ 4000000 ≤ d ∧ d ^ 10 ≤ n ∧ 1 / 2 ≤ (δ : ℝ) ∧
      1024 * (120 * Real.log d + 68) ≤ (1 - (δ : ℝ)) / 2 * d ∧
      10 * (120 * Real.log d + 68) ≤ ((1 - (δ : ℝ)) / 2) ^ (3 / 2 : ℝ) * d ∧
      IsCompact (Metric.closedBall (BitRAM.toE (0 : Fin d → ℚ)) 1) ∧
      Convex ℝ (Metric.closedBall (BitRAM.toE (0 : Fin d → ℚ)) 1) ∧
      ∃ orc : (Fin d → ℚ) → ℕ → Bool,
        BitRAMO.WeakMemOracle (Metric.closedBall (BitRAM.toE (0 : Fin d → ℚ)) 1) orc := by
  sorry

end LowerDeltaQ.Sanity

namespace UnifiedLower.LowerSanity

open BitRAM BitRAMO Unified
open RealRAM (Strategy Strats regretPts)
open Lower (Learner IsLearnerAd regretAd)

/-- The hypotheses of `TheoremLowerU` hold for every `d` and `n`: the closed unit ball about `0` (`r0 = R0 = 1`) and
the constant learner `0` on `Unit` with the Dirac measure. -/
theorem lowerU_hyps_satisfiable (d n : ℕ) :
    BodyU (Metric.closedBall (0 : E d) 1) 0 1 1 ∧ IsProbabilityMeasure (Measure.dirac ()) ∧
      IsLearnerAd (Metric.closedBall (0 : E d) 1) n (fun _ _ _ _ => 0 : Learner Unit d) := by
  sorry

/-- The hypotheses of `TheoremLowerUProg` hold for every `d`, `n` and `δ`: the closed unit ball about the rational
centre `0` (`r0 = R0 = 1`) is compact and convex, has an exact membership oracle, which is a weak membership oracle;
and for every oracle the program `M (-1) := -2`, `play (-1)`, `jmp 1`, which plays the point `0` in every round and
reads no coin, meets `MachineOK` on the input with some cost bound `B` and the windows `D = D' = 0`. -/
theorem progU_hyps_satisfiable (d n : ℕ) (δ : ℚ) :
    IsCompact (Metric.closedBall (toE (0 : Fin d → ℚ)) 1) ∧
      Convex ℝ (Metric.closedBall (toE (0 : Fin d → ℚ)) 1) ∧
      Metric.closedBall (toE (0 : Fin d → ℚ)) ((1 : ℚ) : ℝ) ⊆ Metric.closedBall (toE (0 : Fin d → ℚ)) 1 ∧
      Metric.closedBall (toE (0 : Fin d → ℚ)) 1 ⊆ Metric.closedBall (toE (0 : Fin d → ℚ)) ((1 : ℚ) : ℝ) ∧
      (∃ orc : (Fin d → ℚ) → ℕ → Bool, WeakMemOracle (Metric.closedBall (toE (0 : Fin d → ℚ)) 1) orc ∧
        ∀ y k, orc y k = true ↔ toE y ∈ Metric.closedBall (toE (0 : Fin d → ℚ)) 1) ∧
      ∀ orc : (Fin d → ℚ) → ℕ → Bool, ∃ B : ℝ,
        MachineOK [.base (.const (-1) (-2)), .base (.play (-1)), .base (.jmp 1)]
          (Metric.closedBall (toE (0 : Fin d → ℚ)) 1) orc (initU d n δ 1 1 0) n B (fun _ => 0) (fun _ => 0) := by
  sorry

end UnifiedLower.LowerSanity

EOT
}
chUnified() {
  header
  cat <<'EOT'
-- Comparator challenge of config-unified.json: AdversarialBco/StatementUnified.lean verbatim over the first and sixth
-- modules, its theorem and five non-vacuity witnesses, each proved by `sorry` (code/formal-proof/challenges.sh).
-- Nothing imports this module; the warnings `declaration uses sorry` are expected.
module

public import AdversarialBco.ChallengeBase.StatementPoly
public import AdversarialBco.ChallengeBase.StatementBitRAMO
EOT
  imports "$su"
  printf '\n@[expose] public section\n\n'
  body "$su" | sed '$d'
  blockU
  printf 'end AdversarialBco\n'
}
chUW() {
  header
  cat <<'EOT'
-- Comparator challenge of config-uw.json: AdversarialBco/StatementUW.lean verbatim over the seventh module, its theorem,
-- Theorem U from it and the five non-vacuity witnesses of the hypotheses, each proved by `sorry`
-- (code/formal-proof/challenges.sh). Nothing imports this module; the warnings `declaration uses sorry` are expected.
module

public import AdversarialBco.ChallengeBase.StatementUnified
EOT
  imports "$sw"
  printf '\n@[expose] public section\n\n'
  body "$sw" | sed '$d'
  blockUW
  blockUS
  printf 'end AdversarialBco\n'
}
chMinimaxQ() {
  header
  cat <<'EOT'
-- Comparator challenge of config-minimax-q.json: AdversarialBco/StatementMinimaxQ.lean verbatim over the ninth and tenth
-- modules, its four theorems, clause (b) of the two theorems of StatementUnifiedLower.lean from them and ten non-vacuity
-- witnesses, each proved by `sorry` (code/formal-proof/challenges.sh). Nothing imports this module; the warnings
-- `declaration uses sorry` are expected.
module

public import AdversarialBco.ChallengeBase.StatementMinimax
public import AdversarialBco.ChallengeBase.StatementConj1LowerPolyD
EOT
  imports "$sq"
  printf '\n@[expose] public section\n\n'
  body "$sq" | sed '$d'
  blockMQ
  blockLUB
  printf 'end AdversarialBco\n'
}
chMatched() {
  header
  cat <<'EOT'
-- Comparator challenge of config-matched.json: AdversarialBco/StatementMatched.lean verbatim over the eleventh and
-- twelfth modules, Theorem UW, its three theorems, the reduction and seven non-vacuity witnesses, each proved by
-- `sorry` (code/formal-proof/challenges.sh). Nothing imports this module; the warnings `declaration uses sorry` are
-- expected.
module

public import AdversarialBco.ChallengeBase.StatementMinimaxQ
public import AdversarialBco.ChallengeBase.StatementUW
EOT
  imports "$sma"
  printf '\n@[expose] public section\n\n'
  body "$sma" | sed '$d'
  blockMM
  printf 'end AdversarialBco\n'
}
# The non-vacuity witnesses of the bit-model statement, which the solution proves in
# AdversarialBco/Conj1Bit/Sanity.lean and the configuration config-conj1-bit-hp.json names:
# the hypotheses hold together in every dimension, the deterministic adversaries are randomised adversaries, and the
# empty program fails the cost clause.
bitWitnesses() {
  cat <<'EOT'
namespace BitRAM.Conj1BitSanity

open RealRAM (Strategy polytope HeightLE)

/-- The hypotheses are satisfiable in every dimension, by a randomised adversary whose strategy depends on its seed. -/
theorem hyps_satisfiable_exists (d : ℕ) (hd : 1 ≤ d) :
    ∃ (n m M : ℕ) (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ), 1 ≤ n ∧ HeightLE A b M ∧
      (∃ c : E d, Metric.closedBall c 1 ⊆ polytope A b) ∧
      (∀ x ∈ polytope A b, ∀ y ∈ polytope A b, dist x y ≤ n) ∧
      ∃ (ρ : Measure Bool) (σ : Bool → Strategy d), IsProbabilityMeasure ρ ∧ RandAdv (polytope A b) n σ ∧
        σ true ≠ σ false := by
  sorry

/-- A deterministic strategy with admissible losses is a randomised adversary on `Unit`, with no measurability. -/
theorem randAdv_unit {d : ℕ} {K : Set (E d)} {n : ℕ} (σ : Strategy d)
    (h : ∀ t < n, ∀ x o, AdmLoss K (σ t x o)) : RandAdv K n (fun _ : Unit => σ) := by
  sorry

/-- The empty program never plays: it fails the cost clause. -/
theorem nil_not_costOKBit {d : ℕ} (g : GameBit d) (s0 : State d) (n : ℕ) (B : ℝ) (h0 : s0.rounds < n) :
    ¬ CostOKBit [] g s0 n B := by
  sorry

end BitRAM.Conj1BitSanity

EOT
}
chBitHP() {
  header
  cat <<'EOT'
-- Comparator challenge of config-conj1-bit-hp.json: AdversarialBco/StatementConj1BitHP.lean verbatim over the copy of
-- the statement file it imports, its theorems and the three non-vacuity witnesses of the bit model (the hypotheses are
-- those of StatementConj1Bit.lean), each proved by `sorry` (code/formal-proof/challenges.sh). Nothing imports this
-- module; the warnings `declaration uses sorry` are expected.
module

public import AdversarialBco.ChallengeBase.StatementConj1Bit
EOT
  imports "$sh"
  printf '\n@[expose] public section\n\n'
  body "$sh" | sed '$d'
  sorries theoremConj1UpperBitHP TheoremConj1UpperBitHP 'The first sentence of Conjecture 1 in the bit-cost model, in expectation and with high probability: the theorem
that the solution module `AdversarialBco.Conj1BitHP.Main` proves.'
  sorries theoremConj1UpperBit_of_hp 'TheoremConj1UpperBitHP → TheoremConj1UpperBit' 'The statement with high probability implies the statement with a majorant in expectation.'
  bitWitnesses
  printf 'end AdversarialBco\n'
}
# The non-vacuity witnesses of `TheoremConj1Upper`, which the solution proves in AdversarialBco/Conj1/Sanity.lean and
# config-conj1.json names: the hypotheses hold together for every dimension and horizon with a strategy that reads the
# observations, the law of the runs is a probability measure, and the empty program fails the cost clause.
chConj1() {
  header
  cat <<'EOT'
-- Comparator challenge of config-conj1.json: the theorem `theoremConj1Upper` and three non-vacuity witnesses, each
-- proved by `sorry`, over the copy of AdversarialBco/StatementConj1.lean (code/formal-proof/challenges.sh). Nothing
-- imports this module; the warnings `declaration uses sorry` are expected.
module

public import AdversarialBco.ChallengeBase.StatementConj1

@[expose] public section

open MeasureTheory

namespace AdversarialBco

EOT
  sorries theoremConj1Upper TheoremConj1Upper 'The upper bound on a convex body given by a membership oracle, on the real RAM: the theorem that the solution
module `AdversarialBco.Conj1.Main` proves.'
  cat <<'EOT'
namespace RealRAM.Conj1Sanity

/-- The hypotheses hold together for every `d` and `n`, with a strategy of the class whose loss of round `1` reads the
observation of round `0`. -/
theorem hyps_satisfiable_exists (d n : ℕ) :
    ∃ (r0 R0 δ : ℝ) (K : Set (E d)) (σ : Strategy d) (ν : Measure (ℕ → ℝ)),
      0 < r0 ∧ r0 ≤ R0 ∧ 0 < δ ∧ δ < 1 ∧ IsCompact K ∧ Convex ℝ K ∧ Metric.closedBall 0 r0 ⊆ K ∧
        K ⊆ Metric.closedBall 0 R0 ∧ σ ∈ Strats K n ∧ NoiseOK ν ∧
        ∀ (x : Fin 1 → E d) (y : E d), σ 1 x (fun _ => 0) y ≠ σ 1 x (fun _ => 1) y := by
  sorry

/-- The law of the runs in the regret clause is a probability measure for every noise law that meets `NoiseOK`. -/
theorem isProbabilityMeasure_runs (ν : Measure (ℕ → ℝ)) (h : NoiseOK ν) :
    IsProbabilityMeasure (gaussStream.prod ν) := by
  sorry

/-- The empty program never plays: it fails the cost clause on every instance. -/
theorem nil_not_costOKAd {d : ℕ} (g : GameAd d) (n : ℕ) (r0 R0 δ B0 B : ℝ) :
    ¬ CostOKAd [] g (init d n r0 R0 δ) n B0 B := by
  sorry

end RealRAM.Conj1Sanity

end AdversarialBco
EOT
}
pairs="base1:$d/ChallengeBase/StatementPoly.lean base2:$d/ChallengeBase/StatementConj1.lean
base3:$d/ChallengeBase/StatementConj1Poly.lean base4:$d/ChallengeBase/StatementBitRAM.lean
base5:$d/ChallengeBase/StatementConj1Lower.lean base6:$d/ChallengeBase/StatementBitRAMO.lean
base7:$d/ChallengeBase/StatementUnified.lean base8:$d/ChallengeBase/StatementUnifiedLower.lean
base9:$d/ChallengeBase/StatementMinimax.lean base10:$d/ChallengeBase/StatementConj1LowerPolyD.lean
base11:$d/ChallengeBase/StatementMinimaxQ.lean base12:$d/ChallengeBase/StatementUW.lean
base13:$d/ChallengeBase/StatementConj1Bit.lean
chUnified:$d/ChallengeUnified.lean chUW:$d/ChallengeUW.lean chMinimaxQ:$d/ChallengeMinimaxQ.lean
chMatched:$d/ChallengeMatched.lean chBitHP:$d/ChallengeConj1BitHP.lean chConj1:$d/ChallengeConj1.lean"
if [ "${1:-}" = --write ]; then
  mkdir -p $d/ChallengeBase
  for p in $pairs; do "${p%%:*}" > "${p#*:}"; done
  echo "wrote $(for p in $pairs; do printf '%s ' "${p#*:}"; done)"; exit 0
fi
ok=1
for p in $pairs; do diff <("${p%%:*}") "${p#*:}" || ok=0; done
if [ $ok = 1 ]; then echo "CHALLENGES OK"; else echo "CHALLENGES DIFFER"; exit 1; fi
