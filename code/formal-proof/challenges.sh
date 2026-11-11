#!/bin/bash
# Writes, or checks, the Comparator challenges of the statement files StatementPoly.lean, StatementConj1.lean,
# StatementConj1Exp.lean, StatementConj1Lower.lean, StatementConj1Poly.lean and StatementConj1PolyExp.lean. Each
# challenge imports Mathlib only and copies the statement files verbatim, cut at the same module boundaries as the library:
#   AdversarialBco/ChallengeBase/StatementPoly.lean   the definitions E, AdmLoss, Advs of Statement.lean and
#                                                     StatementPoly.lean;
#   AdversarialBco/ChallengeBase/StatementConj1.lean  StatementConj1.lean, over the first;
#   AdversarialBco/ChallengeBase/StatementConj1Poly.lean  StatementConj1Poly.lean, over the second;
#   AdversarialBco/ChallengePoly.lean, ChallengeConj1.lean, ChallengeConj1Poly.lean  the theorems proved by `sorry`,
#                                                     over the first, second or third;
#   AdversarialBco/ChallengeConj1Exp.lean, ChallengeConj1Lower.lean  the statement file verbatim over the second, and
#                                                     its theorems proved by `sorry`;
#   AdversarialBco/ChallengeConj1PolyExp.lean          StatementConj1PolyExp.lean verbatim over the third, and its
#                                                     theorems proved by `sorry`.
# Usage, from the root of the repository: code/formal-proof/challenges.sh [--write]
#   prints `CHALLENGES OK` (exit 0), or the differences and `CHALLENGES DIFFER` (exit 1); --write writes them.
set -eu
d=AdversarialBco
st=$d/Statement.lean; sp=$d/StatementPoly.lean; sc=$d/StatementConj1.lean; scp=$d/StatementConj1Poly.lean
header() {
  printf '/-\nCopyright (c) 2026 mt0-svg. All rights reserved.\nReleased under Apache 2.0 license as described in the file LICENSE.\nAuthors: mt0-svg\n-/\n'
}
# The body of a statement file: without its header, `module`, its imports and the line that opens the public section.
body() { sed '1,/^-\/$/d' "$1" | sed '/^module$/d; /^public import /d; /^@\[expose\] public section$/d' | sed '/./,$!d'; }
imports() { sed -n 's/^public import \(Mathlib\..*\)$/public import \1/p' "$1"; }
defs=$(awk '/^\/-- The ambient space/ { p = 1 } /^\/-- Observations/ { p = 0 } p' "$st")
[ "$(printf '%s\n' "$defs" | sed -nE 's/^(abbrev|def) ([A-Za-z]+) .*/\2/p' | tr '\n' ' ')" = "E AdmLoss Advs " ] ||
  { echo "$st: the block copied is not the definitions E, AdmLoss, Advs"; exit 1; }
for f in "$sp" "$sc" $d/StatementConj1Exp.lean $d/StatementConj1Lower.lean "$scp" $d/StatementConj1PolyExp.lean; do
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
over() { # over CONFIG BASE: the head of a challenge whose theorems sit over BASE
  header
  printf -- '-- Comparator challenge of %s: the theorems proved by `sorry` over the copies of the statement files\n' "$1"
  printf -- '-- (code/formal-proof/challenges.sh). Nothing imports this module; the warnings `declaration uses sorry` are\n'
  printf -- '-- expected.\nmodule\n\npublic import AdversarialBco.ChallengeBase.%s\n\n@[expose] public section\n\n' "$2"
}
third() { # third CONFIG FILE [BASE]: the head of a challenge that copies FILE over BASE, the second module by default
  header
  printf -- '-- Comparator challenge of %s: AdversarialBco/%s verbatim over the copies of the\n' "$1" "$(basename "$2")"
  printf -- '-- statement files it imports, and its theorems proved by `sorry` (code/formal-proof/challenges.sh). Nothing\n'
  printf -- '-- imports this module; the warnings `declaration uses sorry` are expected.\nmodule\n\npublic import AdversarialBco.ChallengeBase.%s\n' "${3:-StatementConj1}"
  imports "$2"
  printf '\n@[expose] public section\n\n'
  body "$2" | sed '$d'
}
chPoly() {
  over config-poly.json StatementPoly
  printf 'namespace AdversarialBco\n\n'
  sorries theoremPoly32O_holds TheoremPoly32O 'Corollary 8.6 (POLY): the theorem that the solution module `AdversarialBco.Poly.Poly32OFinal` proves.'
  printf 'end AdversarialBco\n'
}
chConj1() {
  over config-conj1.json StatementConj1
  printf 'namespace AdversarialBco\n\n'
  sorries theoremConj1Upper TheoremConj1Upper 'Remark 1.2: the theorem that the solution module `AdversarialBco.Conj1.Main` proves.'
  sorries theoremPoly32O_of_conj1 'TheoremConj1Upper → TheoremPoly32O' 'Remark 1.2 implies Corollary 8.6 (POLY).'
  printf 'end AdversarialBco\n'
}
chExp() {
  third config-conj1-exp.json $d/StatementConj1Exp.lean
  sorries theoremConj1UpperExp TheoremConj1UpperExp 'Theorem 1.1: the theorem that the solution module `AdversarialBco.Conj1Exp.Main` proves.'
  sorries theoremConj1UpperExp_of_conj1 'TheoremConj1Upper → TheoremConj1UpperExp' 'Remark 1.2 implies Theorem 1.1.'
  printf 'end AdversarialBco\n'
}
chLower() {
  third config-conj1-lower.json $d/StatementConj1Lower.lean
  sorries theoremConj1Lower TheoremConj1Lower 'Theorem 1.4: the theorem that the solution module `AdversarialBco.Conj1Lower.Main` proves.'
  printf 'end AdversarialBco\n'
}
chPolytope() {
  over config-conj1-poly.json StatementConj1Poly
  printf 'namespace AdversarialBco\n\n'
  sorries theoremConj1UpperPoly TheoremConj1UpperPoly 'Theorem 1.3 (a): the theorem that the solution module `AdversarialBco.Conj1Poly.Main` proves.'
  sorries theoremConj1UpperPoly_of_conj1 'TheoremConj1Upper → TheoremConj1UpperPoly' 'Remark 1.2 implies Theorem 1.3 (a).'
  printf 'end AdversarialBco\n'
}
chPolyExp() {
  third config-conj1-poly-exp.json $d/StatementConj1PolyExp.lean StatementConj1Poly
  sorries theoremConj1UpperPolyExp TheoremConj1UpperPolyExp 'Theorem 1.3 (b): the theorem that the solution module `AdversarialBco.Conj1PolyExp.Main` proves.'
  sorries theoremConj1UpperPolyExp_of_poly 'TheoremConj1UpperPoly → TheoremConj1UpperPolyExp' 'Theorem 1.3 (a) implies Theorem 1.3 (b).'
  printf 'end AdversarialBco\n'
}
pairs="base1:$d/ChallengeBase/StatementPoly.lean base2:$d/ChallengeBase/StatementConj1.lean
base3:$d/ChallengeBase/StatementConj1Poly.lean chPoly:$d/ChallengePoly.lean chConj1:$d/ChallengeConj1.lean
chExp:$d/ChallengeConj1Exp.lean chLower:$d/ChallengeConj1Lower.lean chPolytope:$d/ChallengeConj1Poly.lean
chPolyExp:$d/ChallengeConj1PolyExp.lean"
if [ "${1:-}" = --write ]; then
  mkdir -p $d/ChallengeBase
  for p in $pairs; do "${p%%:*}" > "${p#*:}"; done
  echo "wrote $(for p in $pairs; do printf '%s ' "${p#*:}"; done)"; exit 0
fi
ok=1
for p in $pairs; do diff <("${p%%:*}") "${p#*:}" || ok=0; done
if [ $ok = 1 ]; then echo "CHALLENGES OK"; else echo "CHALLENGES DIFFER"; exit 1; fi
