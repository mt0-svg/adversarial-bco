#!/bin/bash
# Writes, or checks, the Comparator challenges of the statement files StatementConj1Bit.lean (with its machine
# StatementBitRAM.lean), StatementConj1BitExp.lean and StatementConj1LowerPoly.lean, with the statement files they
# import. Each challenge imports Mathlib only and copies the statement files verbatim, cut at the same module
# boundaries as the library:
#   AdversarialBco/ChallengeBase/StatementPoly.lean   the definitions E, AdmLoss of Statement.lean and
#                                                     StatementPoly.lean;
#   AdversarialBco/ChallengeBase/StatementConj1.lean  StatementConj1.lean, over the first;
#   AdversarialBco/ChallengeBase/StatementConj1Poly.lean  StatementConj1Poly.lean, over the second;
#   AdversarialBco/ChallengeBase/StatementBitRAM.lean  StatementBitRAM.lean, over the first;
#   AdversarialBco/ChallengeBase/StatementConj1Bit.lean  StatementConj1Bit.lean, over the third and the fourth;
#   AdversarialBco/ChallengeBase/StatementConj1Lower.lean  StatementConj1Lower.lean, over the second;
#   AdversarialBco/ChallengeConj1Bit.lean              StatementConj1Bit.lean verbatim over the third and the fourth,
#                                                     its theorem and three non-vacuity witnesses, by `sorry`;
#   AdversarialBco/ChallengeConj1BitExp.lean           StatementConj1BitExp.lean verbatim over the fifth, its
#                                                     theorems and the same three witnesses, by `sorry`;
#   AdversarialBco/ChallengeConj1LowerPoly.lean        StatementConj1LowerPoly.lean verbatim over the sixth and the
#                                                     third, its theorem and two non-vacuity witnesses, by `sorry`.
# Usage, from the root of the repository: code/formal-proof/challenges.sh [--write]
#   prints `CHALLENGES OK` (exit 0), or the differences and `CHALLENGES DIFFER` (exit 1); --write writes them.
set -eu
d=AdversarialBco
st=$d/Statement.lean; sp=$d/StatementPoly.lean; sc=$d/StatementConj1.lean; scp=$d/StatementConj1Poly.lean
sr=$d/StatementBitRAM.lean; sb=$d/StatementConj1Bit.lean
header() {
  printf '/-\nCopyright (c) 2026 mt0-svg. All rights reserved.\nReleased under Apache 2.0 license as described in the file LICENSE.\nAuthors: mt0-svg\n-/\n'
}
# The body of a statement file: without its header, `module`, its imports and the line that opens the public section.
body() { sed '1,/^-\/$/d' "$1" | sed '/^module$/d; /^public import /d; /^@\[expose\] public section$/d' | sed '/./,$!d'; }
imports() { sed -n 's/^public import \(Mathlib\..*\)$/public import \1/p' "$1"; }
defs=$(awk '/^\/-- The ambient space/ { p = 1 } /^end AdversarialBco$/ { p = 0 } p' "$st")
[ "$(printf '%s\n' "$defs" | sed -nE 's/^(abbrev|def) ([A-Za-z]+) .*/\2/p' | tr '\n' ' ')" = "E AdmLoss " ] ||
  { echo "$st: the block copied is not the definitions E, AdmLoss"; exit 1; }
for f in "$sp" "$sc" $d/StatementConj1Lower.lean "$scp" "$sr" "$sb" $d/StatementConj1BitExp.lean \
  $d/StatementConj1LowerPoly.lean; do
  [ "$(tail -1 "$f")" = "end AdversarialBco" ] || { echo "$f: last line is not the end of its namespace"; exit 1; }
done
base1() {
  header
  cat <<'EOT'
-- Comparator challenges, first module, importing Mathlib only: the definitions `E`, `AdmLoss` of
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
# The non-vacuity witnesses of the two bit-model statements, which the solution proves in
# AdversarialBco/Conj1Bit/Sanity.lean and the configurations config-conj1-bit.json and config-conj1-bit-exp.json name:
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
chBit() {
  header
  cat <<'EOT'
-- Comparator challenge of config-conj1-bit.json: AdversarialBco/StatementConj1Bit.lean verbatim over the copies of the
-- statement files it imports, the theorem `theoremConj1UpperBit` and three non-vacuity witnesses, each proved by
-- `sorry` (code/formal-proof/challenges.sh). Nothing imports this module; the warnings `declaration uses sorry` are
-- expected.
module

public import AdversarialBco.ChallengeBase.StatementConj1Poly
public import AdversarialBco.ChallengeBase.StatementBitRAM
EOT
  imports "$sb"
  printf '\n@[expose] public section\n\n'
  body "$sb" | sed '$d'
  cat <<'EOT'
/-- The first sentence of Conjecture 1 in the bit-cost model: the theorem that a solution module proves. -/
theorem theoremConj1UpperBit : TheoremConj1UpperBit := by
  sorry

EOT
  bitWitnesses
  printf 'end AdversarialBco\n'
}
chBitExp() {
  header
  cat <<'EOT'
-- Comparator challenge of config-conj1-bit-exp.json: AdversarialBco/StatementConj1BitExp.lean verbatim over the copy of
-- the statement file it imports, its theorems and the three non-vacuity witnesses of the bit model (the hypotheses are
-- those of StatementConj1Bit.lean), each proved by `sorry` (code/formal-proof/challenges.sh). Nothing imports this
-- module; the warnings `declaration uses sorry` are expected.
module

public import AdversarialBco.ChallengeBase.StatementConj1Bit
EOT
  imports $d/StatementConj1BitExp.lean
  printf '\n@[expose] public section\n\n'
  body $d/StatementConj1BitExp.lean | sed '$d'
  sorries theoremConj1UpperBitExp TheoremConj1UpperBitExp 'The corollary in expectation of the bit-model upper bound: the theorem that the solution module
`AdversarialBco.Conj1BitExp.Main` proves.'
  sorries theoremConj1UpperBitExp_of_bit 'TheoremConj1UpperBit → TheoremConj1UpperBitExp' 'The bit-model upper bound (the main theorem of the paper) implies the corollary in expectation of the bit-model
upper bound.'
  bitWitnesses
  printf 'end AdversarialBco\n'
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
pairs="base1:$d/ChallengeBase/StatementPoly.lean base2:$d/ChallengeBase/StatementConj1.lean
base3:$d/ChallengeBase/StatementConj1Poly.lean base4:$d/ChallengeBase/StatementBitRAM.lean
base5:$d/ChallengeBase/StatementConj1Bit.lean base6:$d/ChallengeBase/StatementConj1Lower.lean
chBit:$d/ChallengeConj1Bit.lean chBitExp:$d/ChallengeConj1BitExp.lean chLowerPoly:$d/ChallengeConj1LowerPoly.lean"
if [ "${1:-}" = --write ]; then
  mkdir -p $d/ChallengeBase
  for p in $pairs; do "${p%%:*}" > "${p#*:}"; done
  echo "wrote $(for p in $pairs; do printf '%s ' "${p#*:}"; done)"; exit 0
fi
ok=1
for p in $pairs; do diff <("${p%%:*}") "${p#*:}" || ok=0; done
if [ $ok = 1 ]; then echo "CHALLENGES OK"; else echo "CHALLENGES DIFFER"; exit 1; fi
