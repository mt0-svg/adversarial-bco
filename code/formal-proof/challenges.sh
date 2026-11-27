#!/bin/bash
# Writes, or checks, the Comparator challenges of the statement files StatementConj1BitHP.lean (over
# StatementConj1Bit.lean and its machine StatementBitRAM.lean), StatementConj1.lean and StatementConj1LowerPoly.lean,
# with the statement files they import. Each challenge imports Mathlib only and copies the statement files verbatim,
# cut at the same module boundaries as the library:
#   AdversarialBco/ChallengeBase/StatementPoly.lean   the definitions E, AdmLoss, Advs of Statement.lean and
#                                                     StatementPoly.lean;
#   AdversarialBco/ChallengeBase/StatementConj1.lean  StatementConj1.lean, over the first;
#   AdversarialBco/ChallengeBase/StatementConj1Poly.lean  StatementConj1Poly.lean, over the second;
#   AdversarialBco/ChallengeBase/StatementBitRAM.lean  StatementBitRAM.lean, over the first;
#   AdversarialBco/ChallengeBase/StatementConj1Bit.lean  StatementConj1Bit.lean, over the third and the fourth;
#   AdversarialBco/ChallengeBase/StatementConj1Lower.lean  StatementConj1Lower.lean, over the second;
#   AdversarialBco/ChallengeConj1BitHP.lean            StatementConj1BitHP.lean verbatim over the fifth, its
#                                                     theorems and three non-vacuity witnesses, by `sorry`;
#   AdversarialBco/ChallengeConj1.lean                 over the second, its theorem and three non-vacuity witnesses,
#                                                     by `sorry`;
#   AdversarialBco/ChallengeConj1LowerPoly.lean        StatementConj1LowerPoly.lean verbatim over the sixth and the
#                                                     third, its theorem and two non-vacuity witnesses, by `sorry`;
#   AdversarialBco/ChallengeBase/StatementBitRAMO.lean  StatementBitRAMO.lean, the machine with the oracle, over the
#                                                     fourth;
#   AdversarialBco/ChallengeBase/StatementUnified.lean  StatementUnified.lean, over the first and the seventh;
#   AdversarialBco/ChallengeUnified.lean               StatementUnified.lean verbatim over the first and the seventh,
#                                                     its theorem and five non-vacuity witnesses, by `sorry`;
#   AdversarialBco/ChallengeUnifiedLower.lean          StatementUnifiedLower.lean verbatim over the eighth and the
#                                                     sixth, its two theorems, their instance on the cube and nine
#                                                     non-vacuity witnesses, by `sorry`;
#   AdversarialBco/ChallengeMatch.lean                 StatementUnifiedLower.lean verbatim over the eighth and the
#                                                     sixth, its corollary and the fourteen witnesses of the two
#                                                     previous challenges, by `sorry`.
# Usage, from the root of the repository: code/formal-proof/challenges.sh [--write]
#   prints `CHALLENGES OK` (exit 0), or the differences and `CHALLENGES DIFFER` (exit 1); --write writes them.
set -eu
d=AdversarialBco
st=$d/Statement.lean; sp=$d/StatementPoly.lean; sc=$d/StatementConj1.lean; scp=$d/StatementConj1Poly.lean
sr=$d/StatementBitRAM.lean; sb=$d/StatementConj1Bit.lean; sh=$d/StatementConj1BitHP.lean
so=$d/StatementBitRAMO.lean; su=$d/StatementUnified.lean; sl=$d/StatementUnifiedLower.lean
header() {
  printf '/-\nCopyright (c) 2026 mt0-svg. All rights reserved.\nReleased under Apache 2.0 license as described in the file LICENSE.\nAuthors: mt0-svg\n-/\n'
}
# The body of a statement file: without its header, `module`, its imports and the line that opens the public section.
body() { sed '1,/^-\/$/d' "$1" | sed '/^module$/d; /^public import /d; /^@\[expose\] public section$/d' | sed '/./,$!d'; }
imports() { sed -n 's/^public import \(Mathlib\..*\)$/public import \1/p' "$1"; }
defs=$(awk '/^\/-- The ambient space/ { p = 1 } /^end AdversarialBco$/ { p = 0 } p' "$st")
[ "$(printf '%s\n' "$defs" | sed -nE 's/^(abbrev|def) ([A-Za-z]+) .*/\2/p' | tr '\n' ' ')" = "E AdmLoss Advs " ] ||
  { echo "$st: the block copied is not the definitions E, AdmLoss, Advs"; exit 1; }
for f in "$sp" "$sc" $d/StatementConj1Lower.lean "$scp" "$sr" "$sb" "$sh" \
  $d/StatementConj1LowerPoly.lean "$so" "$su" "$sl"; do
  [ "$(tail -1 "$f")" = "end AdversarialBco" ] || { echo "$f: last line is not the end of its namespace"; exit 1; }
done
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
base2() {
  header
  cat <<'EOT'
-- Comparator challenges, second module: AdversarialBco/StatementConj1.lean verbatim over the first module
-- (code/formal-proof/challenges.sh).
module

public import AdversarialBco.ChallengeBase.StatementPoly
EOT
  imports "$sc"
  printf '\n@[expose] public section\n\n'
  body "$sc"
}
base3() {
  header
  cat <<'EOT'
-- Comparator challenges, third module: AdversarialBco/StatementConj1Poly.lean verbatim over the second module
-- (code/formal-proof/challenges.sh).
module

public import AdversarialBco.ChallengeBase.StatementConj1
EOT
  imports "$scp"
  printf '\n@[expose] public section\n\n'
  body "$scp"
}
# sorries NAME TYPE DOC: one theorem proved by `sorry`.
sorries() { printf '/-- %s -/\ntheorem %s : %s := by\n  sorry\n\n' "$3" "$1" "$2"; }
base4() {
  header
  cat <<'EOT'
-- Comparator challenges, fourth module: the machine, AdversarialBco/StatementBitRAM.lean verbatim over the first
-- module (code/formal-proof/challenges.sh).
module

public import AdversarialBco.ChallengeBase.StatementPoly
EOT
  imports "$sr"
  printf '\n@[expose] public section\n\n'
  body "$sr"
}
base5() {
  header
  cat <<'EOT'
-- Comparator challenges, fifth module: AdversarialBco/StatementConj1Bit.lean verbatim over the third and fourth
-- modules (code/formal-proof/challenges.sh).
module

public import AdversarialBco.ChallengeBase.StatementConj1Poly
public import AdversarialBco.ChallengeBase.StatementBitRAM
EOT
  imports "$sb"
  printf '\n@[expose] public section\n\n'
  body "$sb"
}
base6() {
  header
  cat <<'EOT'
-- Comparator challenges, sixth module: AdversarialBco/StatementConj1Lower.lean verbatim over the second module
-- (code/formal-proof/challenges.sh).
module

public import AdversarialBco.ChallengeBase.StatementConj1
EOT
  imports $d/StatementConj1Lower.lean
  printf '\n@[expose] public section\n\n'
  body $d/StatementConj1Lower.lean
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
chLowerPoly() {
  header
  cat <<'EOT'
-- Comparator challenge of config-conj1-lower-poly.json: AdversarialBco/StatementConj1LowerPoly.lean verbatim over the
-- copies of the statement files it imports, its theorem and two non-vacuity witnesses, each proved by `sorry`
-- (code/formal-proof/challenges.sh). Nothing imports this module; the warnings `declaration uses sorry` are expected.
module

public import AdversarialBco.ChallengeBase.StatementConj1Lower
public import AdversarialBco.ChallengeBase.StatementConj1Poly
EOT
  imports $d/StatementConj1LowerPoly.lean
  printf '\n@[expose] public section\n\n'
  body $d/StatementConj1LowerPoly.lean | sed '$d'
  sorries theoremConj1LowerPoly_holds TheoremConj1LowerPoly 'The lower bound on a polytope: the theorem that the solution module `AdversarialBco.Conj1LowerPoly.Main` proves.'
  cat <<'EOT'
namespace Lower.Sanity

open RealRAM

/-- On every body `K` with a point `c`, the constant learner that plays `c` is a learner of the class, for every `n`. -/
theorem constLearner_mem_of_mem {d : ℕ} {K : Set (E d)} {c : E d} (hc : c ∈ K) (n : ℕ) :
    IsLearnerAd (Ω := Unit) K n (fun _ _ _ _ => c) := by
  sorry

/-- On every nonempty body, the zero strategy fails the bound against every learner. -/
theorem zeroStrat_fails_of_nonempty {d n : ℕ} (hd : 4000000 ≤ d) (hn : d ^ 10 ≤ n) {K : Set (E d)}
    (hK : K.Nonempty) {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (pol : Learner Ω d) :
    ¬ 7 / 10 ^ 9 * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n / Real.log d ≤
        ∫ ω, regretAd K (fun _ _ _ _ => 0) (fun t => pol t ω) n ∂μ := by
  sorry

end Lower.Sanity

EOT
  printf 'end AdversarialBco\n'
}
base7() {
  header
  cat <<'EOT'
-- Comparator challenges, seventh module: the machine with the oracle, AdversarialBco/StatementBitRAMO.lean verbatim
-- over the fourth module (code/formal-proof/challenges.sh).
module

public import AdversarialBco.ChallengeBase.StatementBitRAM
EOT
  imports "$so"
  printf '\n@[expose] public section\n\n'
  body "$so"
}
base8() {
  header
  cat <<'EOT'
-- Comparator challenges, eighth module: AdversarialBco/StatementUnified.lean verbatim over the first and seventh
-- modules (code/formal-proof/challenges.sh).
module

public import AdversarialBco.ChallengeBase.StatementPoly
public import AdversarialBco.ChallengeBase.StatementBitRAMO
EOT
  imports "$su"
  printf '\n@[expose] public section\n\n'
  body "$su"
}
# The theorem of config-unified.json and its five non-vacuity witnesses, which the solution proves in
# AdversarialBco/Unified/Main.lean and AdversarialBco/Unified/Sanity.lean.
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
# The theorems of config-unified-lower.json, the instance on the cube and the nine non-vacuity witnesses, which the
# solution proves in AdversarialBco/UnifiedLower/Main.lean and AdversarialBco/UnifiedLower/Sanity.lean.
blockLU() {
  cat <<'EOT'
/-- Theorem LU, with Lemma SMALL: the theorem that a solution module proves. -/
theorem theoremLowerU : TheoremLowerU := by
  sorry

/-- Theorem LU for the programs of the oracle machine, in the objects of `TheoremUnified`: the theorem that a solution
module proves. -/
theorem theoremLowerUProg : TheoremLowerUProg := by
  sorry

open Lower UnifiedLower in
/-- Theorem LU on the cube `[-1, 1]^d` (`a = 0`, `r0 = 1`, `R0 = √d`): the instance that a solution module proves. -/
theorem theoremLowerU_cube :
    ∀ d : ℕ, 1 ≤ d → ∀ n : ℕ, 1 ≤ n →
    ∀ (Ω : Type) (_ : MeasurableSpace Ω) (μ : MeasureTheory.Measure Ω), MeasureTheory.IsProbabilityMeasure μ →
    ∀ pol : Learner Ω d, IsLearnerAd {x : E d | ∀ i, |x i| ≤ 1} n pol →
      (4000000 ≤ d → d ^ 10 ≤ n →
        LowerMean {x : E d | ∀ i, |x i| ≤ 1} n 1 μ pol
            (7 / 10 ^ 9 * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n / Real.log d) ∧
          LowerProb {x : E d | ∀ i, |x i| ≤ 1} n 1 μ pol
            (28 / 10 ^ 10 * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n / Real.log d) (1 / 2)) ∧
      LowerMean {x : E d | ∀ i, |x i| ≤ 1} n 1 μ pol (Real.sqrt n / (4 * Real.sqrt 3)) ∧
      LowerProb {x : E d | ∀ i, |x i| ≤ 1} n 1 μ pol (Real.sqrt n / (8 * Real.sqrt 3)) (1 / 48) := by
  sorry

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

/-- The conclusions of `TheoremLowerU` hold at the threshold `0`, with probability `1`, for every learner on a convex
nonempty `K` and every `r0 > 0`: against the constant loss `1/2` the regret is `0`. -/
theorem lowerU_zero {d : ℕ} {K : Set (E d)} (hK : Convex ℝ K) (hne : K.Nonempty) (n : ℕ) {r0 : ℝ} (hr0 : 0 < r0)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (pol : Learner Ω d) :
    LowerMean K n r0 μ pol 0 ∧ LowerProb K n r0 μ pol 0 1 := by
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

/-- The empty program never plays, so it fails `MachineOK` on every input with `n ≥ 1`, for every convex `K`. -/
theorem nil_not_machineOK {d : ℕ} {K : Set (E d)} (hK : Convex ℝ K) (orc : (Fin d → ℚ) → ℕ → Bool) (s0 : State d)
    (n : ℕ) (B : ℝ) (D D' : ℕ → ℕ) (h0 : s0.rounds < n) : ¬ MachineOK [] K orc s0 n B D D' := by
  sorry

/-- The conclusions of `TheoremLowerUProg` hold at the threshold `0`, with probability `1`, for every program on a
convex nonempty `K` and every `r0 > 0`: the constant loss `1/2` is a strategy of `StratsLowU` in closed loop with any
program, with zero noise it is a noisy adversary with any windows, and the regret against it is `0`. -/
theorem progU_zero {d : ℕ} (P : List InstrO) {K : Set (E d)} (hK : Convex ℝ K) (hne : K.Nonempty)
    (orc : (Fin d → ℚ) → ℕ → Bool) (s0 : State d) (n : ℕ) {r0 : ℝ} (hr0 : 0 < r0) (D D' : ℕ → ℕ) :
    ProgMean P K orc s0 n r0 D D' 0 ∧ ProgProb P K orc s0 n r0 D D' 0 1 := by
  sorry

/-- Every body of `TheoremUnified` (rational centre and radii) is a body of `BodyU`. -/
theorem bodyU_of_unified {d : ℕ} {r0 R0 : ℚ} (h0 : 0 < r0) (h1 : r0 ≤ R0) (a : Fin d → ℚ) {K : Set (E d)}
    (hK : IsCompact K) (hc : Convex ℝ K) (hb1 : Metric.closedBall (toE a) (r0 : ℝ) ⊆ K)
    (hb2 : K ⊆ Metric.closedBall (toE a) (R0 : ℝ)) : BodyU K (toE a) r0 R0 := by
  sorry

/-- `TheoremLowerU` contains the lower statement of v2.1 (`TheoremConj1Lower`, StatementConj1Lower.lean): its clause (a)
on the closed unit ball about `0` (`r0 = R0 = 1`), whose strategies are `1/4`-Lipschitz on all of `E d`, hence on the
ball. -/
theorem theoremConj1Lower_of_lowerU : TheoremLowerU → TheoremConj1Lower := by
  sorry

/-- Corollary MATCH from the two theorems: the program of `TheoremUnified` meets `MachineOK` with its own bound and
windows, so `TheoremLowerUProg` applies to it, in environments of its own class. -/
theorem corollaryMatch_of_unified_lower : TheoremUnified → TheoremLowerUProg → CorollaryMatch := by
  sorry

/-- The upper part of `CorollaryMatch` is `TheoremUnified` word for word. -/
theorem theoremUnified_of_corollaryMatch : CorollaryMatch → TheoremUnified := by
  sorry

end UnifiedLower.LowerSanity

EOT
}
# The corollary of config-match.json and the fourteen witnesses of the two previous configurations, which the solution
# proves in AdversarialBco/UnifiedMatch/Main.lean and the two sanity modules.
blockM() {
  cat <<'EOT'
/-- Corollary MATCH: the corollary that a solution module proves. -/
theorem corollaryMatch : CorollaryMatch := by
  sorry

section

open ProbabilityTheory

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

end

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

/-- The conclusions of `TheoremLowerU` hold at the threshold `0`, with probability `1`, for every learner on a convex
nonempty `K` and every `r0 > 0`: against the constant loss `1/2` the regret is `0`. -/
theorem lowerU_zero {d : ℕ} {K : Set (E d)} (hK : Convex ℝ K) (hne : K.Nonempty) (n : ℕ) {r0 : ℝ} (hr0 : 0 < r0)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (pol : Learner Ω d) :
    LowerMean K n r0 μ pol 0 ∧ LowerProb K n r0 μ pol 0 1 := by
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

/-- The empty program never plays, so it fails `MachineOK` on every input with `n ≥ 1`, for every convex `K`. -/
theorem nil_not_machineOK {d : ℕ} {K : Set (E d)} (hK : Convex ℝ K) (orc : (Fin d → ℚ) → ℕ → Bool) (s0 : State d)
    (n : ℕ) (B : ℝ) (D D' : ℕ → ℕ) (h0 : s0.rounds < n) : ¬ MachineOK [] K orc s0 n B D D' := by
  sorry

/-- The conclusions of `TheoremLowerUProg` hold at the threshold `0`, with probability `1`, for every program on a
convex nonempty `K` and every `r0 > 0`: the constant loss `1/2` is a strategy of `StratsLowU` in closed loop with any
program, with zero noise it is a noisy adversary with any windows, and the regret against it is `0`. -/
theorem progU_zero {d : ℕ} (P : List InstrO) {K : Set (E d)} (hK : Convex ℝ K) (hne : K.Nonempty)
    (orc : (Fin d → ℚ) → ℕ → Bool) (s0 : State d) (n : ℕ) {r0 : ℝ} (hr0 : 0 < r0) (D D' : ℕ → ℕ) :
    ProgMean P K orc s0 n r0 D D' 0 ∧ ProgProb P K orc s0 n r0 D D' 0 1 := by
  sorry

/-- Every body of `TheoremUnified` (rational centre and radii) is a body of `BodyU`. -/
theorem bodyU_of_unified {d : ℕ} {r0 R0 : ℚ} (h0 : 0 < r0) (h1 : r0 ≤ R0) (a : Fin d → ℚ) {K : Set (E d)}
    (hK : IsCompact K) (hc : Convex ℝ K) (hb1 : Metric.closedBall (toE a) (r0 : ℝ) ⊆ K)
    (hb2 : K ⊆ Metric.closedBall (toE a) (R0 : ℝ)) : BodyU K (toE a) r0 R0 := by
  sorry

/-- `TheoremLowerU` contains the lower statement of v2.1 (`TheoremConj1Lower`, StatementConj1Lower.lean): its clause (a)
on the closed unit ball about `0` (`r0 = R0 = 1`), whose strategies are `1/4`-Lipschitz on all of `E d`, hence on the
ball. -/
theorem theoremConj1Lower_of_lowerU : TheoremLowerU → TheoremConj1Lower := by
  sorry

/-- Corollary MATCH from the two theorems: the program of `TheoremUnified` meets `MachineOK` with its own bound and
windows, so `TheoremLowerUProg` applies to it, in environments of its own class. -/
theorem corollaryMatch_of_unified_lower : TheoremUnified → TheoremLowerUProg → CorollaryMatch := by
  sorry

/-- The upper part of `CorollaryMatch` is `TheoremUnified` word for word. -/
theorem theoremUnified_of_corollaryMatch : CorollaryMatch → TheoremUnified := by
  sorry

end UnifiedLower.LowerSanity

EOT
}
chUnified() {
  header
  cat <<'EOT'
-- Comparator challenge of config-unified.json: AdversarialBco/StatementUnified.lean verbatim over the first and seventh
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
chUnifiedLower() {
  header
  cat <<'EOT'
-- Comparator challenge of config-unified-lower.json: AdversarialBco/StatementUnifiedLower.lean verbatim over the eighth
-- and sixth modules, its two theorems, their instance on the cube and nine non-vacuity witnesses, each proved by
-- `sorry` (code/formal-proof/challenges.sh). Nothing imports this module; the warnings `declaration uses sorry` are
-- expected.
module

public import AdversarialBco.ChallengeBase.StatementUnified
public import AdversarialBco.ChallengeBase.StatementConj1Lower
EOT
  imports "$sl"
  printf '\n@[expose] public section\n\n'
  body "$sl" | sed '$d'
  blockLU
  printf 'end AdversarialBco\n'
}
chMatch() {
  header
  cat <<'EOT'
-- Comparator challenge of config-match.json: AdversarialBco/StatementUnifiedLower.lean verbatim over the eighth and
-- sixth modules, its corollary and the fourteen non-vacuity witnesses of config-unified.json and
-- config-unified-lower.json, each proved by `sorry` (code/formal-proof/challenges.sh). Nothing imports this module; the
-- warnings `declaration uses sorry` are expected.
module

public import AdversarialBco.ChallengeBase.StatementUnified
public import AdversarialBco.ChallengeBase.StatementConj1Lower
EOT
  imports "$sl"
  printf '\n@[expose] public section\n\n'
  body "$sl" | sed '$d'
  blockM
  printf 'end AdversarialBco\n'
}
pairs="base1:$d/ChallengeBase/StatementPoly.lean base2:$d/ChallengeBase/StatementConj1.lean
base3:$d/ChallengeBase/StatementConj1Poly.lean base4:$d/ChallengeBase/StatementBitRAM.lean
base5:$d/ChallengeBase/StatementConj1Bit.lean base6:$d/ChallengeBase/StatementConj1Lower.lean
chBitHP:$d/ChallengeConj1BitHP.lean chConj1:$d/ChallengeConj1.lean chLowerPoly:$d/ChallengeConj1LowerPoly.lean
base7:$d/ChallengeBase/StatementBitRAMO.lean base8:$d/ChallengeBase/StatementUnified.lean
chUnified:$d/ChallengeUnified.lean chUnifiedLower:$d/ChallengeUnifiedLower.lean chMatch:$d/ChallengeMatch.lean"
if [ "${1:-}" = --write ]; then
  mkdir -p $d/ChallengeBase
  for p in $pairs; do "${p%%:*}" > "${p#*:}"; done
  echo "wrote $(for p in $pairs; do printf '%s ' "${p#*:}"; done)"; exit 0
fi
ok=1
for p in $pairs; do diff <("${p%%:*}") "${p#*:}" || ok=0; done
if [ $ok = 1 ]; then echo "CHALLENGES OK"; else echo "CHALLENGES DIFFER"; exit 1; fi
