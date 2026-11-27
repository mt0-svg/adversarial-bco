/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
-- Comparator challenges, seventh module: the machine with the oracle, AdversarialBco/StatementBitRAMO.lean verbatim
-- over the fourth module (code/formal-proof/challenges.sh).
module

public import AdversarialBco.ChallengeBase.StatementBitRAM

@[expose] public section

/-!
# The machine of the unified statement: the bit RAM with a weak membership oracle and a clipped reading (release v2.3)

The learner of `TheoremUnified` (StatementUnified.lean) is one finite program `P : List InstrO` of the machine defined
here, the same for every input. The machine is the logarithmic-cost RAM with fair coins of StatementBitRAM.lean
(frozen for release v2.1, unchanged and imported), with two instructions added:

* `orc dst src prec`: a query to a weak membership oracle of the convex body;
* `obsR dst prec rng`: the reading of the noisy feedback at a precision and a range that the program chooses.

Everything else is the bit machine: the state (`State`), the space (`SpaceLE`), the coins (`coinStream`) and the twelve
instructions of `Instr`, which the program writes as `base i`.

## The two new instructions and their costs

With `M x` the content of the cell `x` and `len z` the bit length of `|z|` (StatementBitRAM.lean):

* `orc dst src prec`: `M dst := 1` if the oracle answers `true` at the rational point `y = ptAt d M (M src)`, that is
  `y_i = M (c + 1 + i) / M c` with `c = M src` (the layout of `play`), and the precision `k = max (M prec) 0`, and
  `M dst := 0` if it answers `false`; cost
  `1 + len dst + len src + len prec + len (M prec) + len c + playCost d M c + k`, where
  `playCost d M c = Σ_{i ≤ d} (1 + len (c + i) + len (M (c + i)))` is what `play` charges to read the same cells. So
  a query costs its precision plus the length of the point asked, as writing a question of length `ℓ` costs `ℓ` on an
  oracle Turing machine (Grötschel, Lovász and Schrijver, Geometric Algorithms and Combinatorial Optimization, 2nd ed.
  1993, Sec. 1.2), where the precision `2^{-k}` is written in `k` digits.
* `obsR dst prec rng`: `M dst := clip q ⌊2^p o⌋`, `p = max (M prec) 0`, `q = max (M rng) 0`, `o` the feedback of the
  last round played (`0` before the first play), `clip q z = max (-2^q) (min z (2^q))`; cost
  `1 + len dst + len prec + len rng + len (M prec) + len (M rng) + p + q`. The result has at most `q + 1` binary
  digits, so it is charged at least its length, as every instruction of the bit machine is.

The feedback is the noisy one: in the world `w`, the feedback of round `t` at the point `x` is `w.f t x + w.noise t`
(`WorldO.toW`). Both `obsR` and the bit machine's `obs` read it; `obs dst prec` reads `⌊2^p o⌋` unclipped at cost
`p + len ⌊2^p o⌋`, so it stays an honest bit cost, and `obsR` is what makes the cost of a round bounded on every run
against an unbounded noise: an unclipped read of a noise of size `2^{2^n}` would cost `2^n`.

## The oracle

A weak membership oracle for `K` (`WeakMemOracle`) is a function `orc : (Fin d → ℚ) → ℕ → Bool` such that at every
rational point `y` and precision `k`: `orc y k = true` only if `y` is within `2^{-k}` of a point of `K`
(`y ∈ K + B(0, 2^{-k})`), and `orc y k = false` only if the closed ball of radius `2^{-k}` about `y` is not inside `K`
(`y ∉ K - B(0, 2^{-k})`). This is the weak membership problem WMEM of Grötschel, Lovász and Schrijver (op. cit.,
(2.1.14)) at the error `2^{-k}`. Where both answers are allowed the oracle may give either; the statement asks the
program to work for every such function, so the ambiguous answers are chosen against it. The oracle is a fixed
function, part of the instance: the same query gets the same answer on every run.

## The machine (`stepO`, `runO`)

A base instruction steps as the bit machine: `stepO P w s = step (lowerP P) w.toW s` when the instruction at the counter
is `base i`, where `lowerP P` replaces every instruction `base i` by `i` (and every new instruction by a jump past the
end of the code; `step (lowerP P)` is applied only at a base instruction, so these jumps are never executed). So `jlt`
and `jmp` targets are indices of `P`, a base instruction has the semantics and the cost of
StatementBitRAM.lean, and the base instructions see the world `w.toW`: the coins `w.cs` and the noisy feedback. The
program halts when the counter leaves the code; a halted state does not change and costs nothing more.

## Junk values

A point with denominator cell `0` is the origin (`q / 0 = 0` in `ℚ`), as for `play`: the oracle is asked at the origin,
and the program can test the denominator with one comparison. A negative precision or range is read as `0`
(`Int.toNat`). The other junk values are those of StatementBitRAM.lean.
-/

namespace AdversarialBco

namespace BitRAMO

open BitRAM

/-- The instructions of the oracle machine. Every operand `dst`, `src`, `prec`, `rng` is the address of a cell. -/
inductive InstrO
  /-- An instruction of the bit machine of StatementBitRAM.lean. -/
  | base (i : Instr)
  /-- `M dst := 1` if the oracle answers `true` at the point `ptAt d M (M src)` and the precision `max (M prec) 0`, else
  `M dst := 0`. -/
  | orc (dst src prec : ℤ)
  /-- `M dst := clip q ⌊2^p o⌋`, `p = max (M prec) 0`, `q = max (M rng) 0`, `o` the feedback of the last round played. -/
  | obsR (dst prec rng : ℤ)

/-- What the oracle machine interacts with: the losses of the rounds, the noise of the rounds, the coin stream and the
membership oracle. -/
structure WorldO (d : ℕ) where
  /-- The loss of each round. -/
  f : ℕ → E d → ℝ
  /-- The noise of each round, added to the loss in the feedback. -/
  noise : ℕ → ℝ
  /-- The coin stream, `true` for heads. -/
  cs : ℕ → Bool
  /-- The membership oracle: the answer at a rational point and a precision. -/
  orc : (Fin d → ℚ) → ℕ → Bool

/-- The world that the base instructions see: the coins, and the noisy feedback `f t x + noise t` of round `t`. -/
def WorldO.toW {d : ℕ} (w : WorldO d) : World d :=
  ⟨fun t x => w.f t x + w.noise t, w.cs⟩

/-- A base instruction is itself; a new instruction becomes a jump to `L`, past the end of a code of length `L`. -/
def lowerI (L : ℕ) : InstrO → Instr
  | .base i => i
  | _ => .jmp L

/-- The lowered program, a program of the bit machine. -/
def lowerP (P : List InstrO) : List Instr :=
  P.map (lowerI P.length)

/-- The clip of an integer to `[-2^q, 2^q]`. -/
def clip (q : ℕ) (z : ℤ) : ℤ :=
  max (-(2 : ℤ) ^ q) (min z ((2 : ℤ) ^ q))

/-- One step of the oracle machine, the cost of the instruction added to `cost`. -/
noncomputable def stepO {d : ℕ} (P : List InstrO) (w : WorldO d) (s : State d) : State d :=
  match P[s.pc]? with
  | none => s
  | some (.base _) => step (lowerP P) w.toW s
  | some (.orc dst src prec) =>
    { s with pc := s.pc + 1,
             mem := Function.update s.mem dst
               (if w.orc (ptAt d s.mem (s.mem src)) (s.mem prec).toNat then 1 else 0),
             cost := s.cost + (1 + len dst + len src + len prec + len (s.mem prec) + len (s.mem src) +
               playCost d s.mem (s.mem src) + (s.mem prec).toNat) }
  | some (.obsR dst prec rng) =>
    { s with pc := s.pc + 1,
             mem := Function.update s.mem dst (clip (s.mem rng).toNat (reading w.toW s (s.mem prec).toNat)),
             cost := s.cost + (1 + len dst + len prec + len rng + len (s.mem prec) + len (s.mem rng) +
               (s.mem prec).toNat + (s.mem rng).toNat) }

/-- The state after `k` steps in a fixed world. -/
noncomputable def runO {d : ℕ} (P : List InstrO) (w : WorldO d) (s0 : State d) (k : ℕ) : State d :=
  (stepO P w)^[k] s0

open Classical in
/-- The point played in round `t`, as a point of `E d` (`0` if that round never comes). -/
noncomputable def playedO {d : ℕ} (P : List InstrO) (w : WorldO d) (s0 : State d) (t : ℕ) : E d :=
  if h : ∃ k, t < (runO P w s0 k).rounds then toE ((runO P w s0 (Nat.find h)).pts t) else 0

/-- The cost clause: from every step at which fewer than `n` rounds have been played, one more round is played within
cost `B`. -/
def CostOKO {d : ℕ} (P : List InstrO) (w : WorldO d) (s0 : State d) (n : ℕ) (B : ℝ) : Prop :=
  ∀ k : ℕ, (runO P w s0 k).rounds < n →
    ∃ j : ℕ, (runO P w s0 k).rounds < (runO P w s0 (k + j)).rounds ∧
      ((runO P w s0 (k + j)).cost : ℝ) ≤ (runO P w s0 k).cost + B

/-- The space clause: at every step at which fewer than `n` rounds have been played, the cells in use have total bit
length at most `B`. -/
def SpaceOKO {d : ℕ} (P : List InstrO) (w : WorldO d) (s0 : State d) (n : ℕ) (B : ℝ) : Prop :=
  ∀ k : ℕ, (runO P w s0 k).rounds < n → SpaceLE (runO P w s0 k) B

/-- A weak membership oracle for `K`: at every rational point `y` and precision `k`, the answer `true` only if `y` is
within `2^{-k}` of a point of `K`, and the answer `false` only if the closed ball of radius `2^{-k}` about `y` is not
inside `K`. -/
def WeakMemOracle {d : ℕ} (K : Set (E d)) (orc : (Fin d → ℚ) → ℕ → Bool) : Prop :=
  ∀ (y : Fin d → ℚ) (k : ℕ),
    (orc y k = true → ∃ z ∈ K, dist (toE y) z ≤ (2 : ℝ)⁻¹ ^ k) ∧
      (orc y k = false → ¬ Metric.closedBall (toE y) ((2 : ℝ)⁻¹ ^ k) ⊆ K)

end BitRAMO

end AdversarialBco
