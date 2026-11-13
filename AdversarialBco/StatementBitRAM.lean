/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import Mathlib.Data.Nat.Size
public import Mathlib.Probability.ProductMeasure
public import AdversarialBco.Statement

@[expose] public section

/-!
# The machine of the bit-model statement: a logarithmic-cost RAM with fair coins

The learner of `TheoremConj1UpperBit` (StatementConj1Bit.lean) is one finite program `P : List Instr` of the machine
defined here, the same for every input. The machine is a random access machine on integers in the sense of Cook and
Reckhow (1973) and of Aho, Hopcroft and Ullman (1974), with the logarithmic cost criterion: an instruction costs the
bit lengths of the addresses it names and of the integers it reads, and a multiplication or a division the product of
the lengths of its operands, the count of the schoolbook algorithms. Its randomness is a stream of fair coins. It
holds no real number: the only real numbers of the game, the losses, reach it through the instruction `obs`, which
reads finitely many binary digits of the feedback at a cost of one per digit. No instruction is idealized: there is no
real arithmetic, no square root, exponential or logarithm, no Gaussian draw, no spectral function, no membership
oracle.

## The machine

* State: a program counter `pc`, a memory `mem : ℤ → ℤ` of integer cells indexed by the integers, the number of coins
  used, the number of rounds played, the points played (rational points of `ℚ^d`), and the cost spent so far.
* Operands: every operand `dst`, `a`, `b`, `src`, `prec` of an instruction is the address of a cell, an integer
  written in the program; `M x` below is the content of the cell `x`. Indirect access is by `load` and `store`.
* Instructions and their costs, with `len z` the number of binary digits of `|z|` (`len 0 = 0`):

  * `const dst c`: `M dst := c`; cost `1 + len dst + len c`.
  * `add dst a b`, `sub dst a b`: `M dst := M a + M b`, `M a - M b`; cost
    `1 + len dst + len a + len b + len (M a) + len (M b)`.
  * `mul dst a b`, `div dst a b`: `M dst := M a * M b`, `M a / M b` (the Euclidean quotient); cost
    `1 + len dst + len a + len b + (len (M a) + 1) (len (M b) + 1)`.
  * `load dst src`: `M dst := M (M src)`; cost `1 + len dst + len src + len (M src) + len (M (M src))`.
  * `store dst src`: `M (M dst) := M src`; cost `1 + len dst + len src + len (M dst) + len (M src)`.
  * `jlt a b target`: jump to `target` if `M a < M b`; cost `1 + len a + len b + len (M a) + len (M b)`.
  * `jmp target`: jump to `target`; cost `1`.
  * `coins dst cnt`: `M dst :=` the integer whose binary digits, the most significant first, are the next `k`
    unused coins (`1` for heads), `k = max (M cnt) 0`, a uniform integer of `[0, 2^k)`; one coin is `k = 1`; cost
    `1 + len dst + len cnt + len (M cnt) + k`.
  * `play src`: play the point `x` of `ℚ^d`, `x_i = M (a + 1 + i) / M a`, `a = M src`; cost
    `1 + len src + len a + Σ_{i ≤ d} (1 + len (a + i) + len (M (a + i)))`.
  * `obs dst prec`: `M dst := ⌊2^p o⌋`, `p = max (M prec) 0`, `o` the feedback of the last round played; cost
    `1 + len dst + len prec + len (M prec) + p + len ⌊2^p o⌋`.

* The program halts when the counter leaves the code; a halted state does not change and costs nothing more. A run is
  the sequence of states from the initial one, `run P w s0 k` the state after `k` steps, and `(run P w s0 k).cost` the
  cost of its first `k` steps.
* Space (`SpaceLE`): the cells in use are those with a nonzero content, and the space of a state is the total bit
  length of their addresses and contents. `SpaceLE s B` says that it is at most `B`, as a bound on every finite set of
  cells in use; since each of them counts at least `1`, it also says that there are at most `B` of them. The points
  played are not counted: they are the machine's output, which no instruction reads back (the world reads the last
  one to compute the feedback).
* What the machine interacts with (`World`): the losses `f t : E d → ℝ` of the rounds, read by `obs` at the point
  played in the last round, and the coin stream `cs : ℕ → Bool`, read by `coins`, `true` for heads. The statement runs
  the machine against a strategy of the adversary, whose loss of round `t` is fixed by the rounds before `t`
  (StatementConj1Bit.lean); here the losses are any sequence.
* The coins (`coinLaw`, `coinStream`): each coin is `true` or `false` with probability `1/2`, and the stream is the
  product of these laws over `ℕ` (`Measure.infinitePi`), so the coins are independent and fair.

## Why this is a bit-cost model

The cost is polynomially related to the number of steps of a multitape Turing machine with a read-only input tape, a
tape of fair coins, an output tape for the points played and the binary digits of the feedback on request, in both
directions.

* A Turing machine simulates the RAM: every integer written by an instruction has at most as many binary digits as
  the cost of that instruction (`len (u + v) ≤ len u + len v + 1`, `len (u v) ≤ len u + len v`, and a copy is charged
  its length), so after a run of cost `T` on an input of length `N` the cells written and their addresses fill at most
  `O(N + T)` tape cells. Each instruction is then simulated by a scan of that list and a schoolbook operation, in time
  `O((N + T)(1 + c))` for an instruction of cost `c`, so the whole run in time `O((N + T)^2)`.
* The RAM simulates a Turing machine of time `T` with a bounded number of instructions per step, each on integers of
  `O(log T)` digits (one cell per tape square, the head positions in cells), once the input is written out in binary
  at a cost polynomial in its length; a block of `k` coins costs `k`.

So the cost of a whole run and the number of steps of a Turing machine are polynomially related. Per round, the cost is
the time of the logarithmic-cost RAM; a Turing machine simulates a round of cost `c` in time `O((N + S)(1 + c))`, `S`
the total length of the cells in use (`SpaceLE`). `TheoremConj1UpperBit` bounds `S` at every step of every round by
the same polynomial in `d`, `m`, `log n` and `log M` as the cost of a round (`SpaceOKBit`, StatementConj1Bit.lean), and
the input length `N` is polynomial in these quantities, so a Turing machine simulates each round in time polynomial in
`d`, `m`, `log n` and `log M`.

## Choices against cheating, for the referee

* One program for all inputs, finite, with integer constants: no advice, no table indexed by the dimension.
* Addresses are charged their length, so a large address is not a free hash table, and the memory is indexed by `ℤ`, so
  no address is clipped.
* Multiplication and division are charged the product of the lengths: with unit cost, multiplication lets a RAM
  decide PSPACE-hard problems in polynomially many steps (Hartmanis and Simon); with the length alone it is still
  polynomial (the length of a product is at most the sum), so the product only makes the count closer to bit operations.
* No real number is stored, so nothing of the real RAM survives (exact `sqrt`, `exp`, `log`, the sign of an exp-log
  constant, the PosSLP problem): the machine is a deterministic integer RAM driven by coins and by the binary digits
  of the feedback that it pays for.
* The points played are rational and written out: `play` reads `d + 1` cells and charges their lengths and addresses,
  so a point costs at least its length.
* The randomness is the coin stream only, read by `coins` at a cost of one per coin; a block of `k` coins is one
  instruction, and any sampler (a Gaussian to `B` bits, a uniform integer) is a program, charged as such.
* The feedback is read through `obs` only, `p` binary digits at a time, at cost `p` plus the length of the result. It
  may be read again, at any precision, until the next play.

## Junk values

`M a / 0 = 0` (the Euclidean quotient of `Int`, `Int.ediv`), and a point with denominator cell `0` is the origin
(`q / 0 = 0` in `ℚ`): the program can test a zero divisor with one comparison, so these give it nothing. A negative
precision reads `0` digits and a negative count `0` coins (`Int.toNat`). `obs` before the first play reads the
feedback `0`. A jump target beyond the code halts the machine. The cells of the memory not set by the input are `0`.
`SpaceLE s B` with `B < 0` is false (the empty set of cells has length `0`).
`coinStream` is `Measure.infinitePi` of the fair coin law, which is a probability measure (the sanity module proves
it), so the product is the true one and not the junk value `0` that `Measure.infinitePi` takes on a family with a
measure that is not a probability measure.
-/

open MeasureTheory

namespace AdversarialBco

namespace BitRAM

/-- The bit length of an integer: the number of binary digits of its absolute value, `0` for `0`. -/
def len (z : ℤ) : ℕ := z.natAbs.size

/-- The instructions. Every operand `dst`, `a`, `b`, `src`, `prec` is the address of a cell, written in the program;
`M x` denotes the content of the cell `x`. -/
inductive Instr
  /-- `M dst := c`. -/
  | const (dst c : ℤ)
  /-- `M dst := M a + M b`. -/
  | add (dst a b : ℤ)
  /-- `M dst := M a - M b`. -/
  | sub (dst a b : ℤ)
  /-- `M dst := M a * M b`. -/
  | mul (dst a b : ℤ)
  /-- `M dst := M a / M b`, the Euclidean quotient (`x / 0 = 0`). -/
  | div (dst a b : ℤ)
  /-- `M dst := M (M src)`. -/
  | load (dst src : ℤ)
  /-- `M (M dst) := M src`. -/
  | store (dst src : ℤ)
  /-- Jump to `target` if `M a < M b`. -/
  | jlt (a b : ℤ) (target : ℕ)
  /-- Jump to `target`. -/
  | jmp (target : ℕ)
  /-- `M dst :=` the integer whose binary digits, the most significant first, are the next `k = max (M cnt) 0` unused
  coins, `1` for heads (`true`) and `0` for tails. -/
  | coins (dst cnt : ℤ)
  /-- Play the rational point `(M (a + 1) / M a, ..., M (a + d) / M a)`, `a = M src`. -/
  | play (src : ℤ)
  /-- `M dst := ⌊2^p o⌋`, `p = max (M prec) 0` and `o` the feedback of the last round played. -/
  | obs (dst prec : ℤ)

/-- The state of the machine. -/
structure State (d : ℕ) where
  /-- The program counter. -/
  pc : ℕ
  /-- The memory: an integer in each cell, the cells indexed by the integers. -/
  mem : ℤ → ℤ
  /-- The number of coins used. -/
  coins : ℕ
  /-- The number of rounds played. -/
  rounds : ℕ
  /-- `pts t`: the point played in round `t`, for `t < rounds`. -/
  pts : ℕ → Fin d → ℚ
  /-- The cost spent so far. -/
  cost : ℕ

/-- What the program interacts with: the losses of the rounds (through `obs`) and the coin stream (through `coins`). -/
structure World (d : ℕ) where
  /-- The loss of each round. -/
  f : ℕ → E d → ℝ
  /-- The coin stream, `true` for heads. -/
  cs : ℕ → Bool

/-- A rational point as a point of `E d`. -/
def toE {d : ℕ} (q : Fin d → ℚ) : E d :=
  WithLp.toLp 2 fun i => (q i : ℝ)

/-- The rational point with denominator in the cell `a` and numerators in the cells `a + 1, ..., a + d`. -/
def ptAt (d : ℕ) (m : ℤ → ℤ) (a : ℤ) : Fin d → ℚ :=
  fun i => (m (a + 1 + (i : ℕ)) : ℚ) / (m a : ℚ)

/-- The cost of reading the cells `a, ..., a + d` of a point: their addresses and their contents. -/
def playCost (d : ℕ) (m : ℤ → ℤ) (a : ℤ) : ℕ :=
  ∑ i ∈ Finset.range (d + 1), (1 + len (a + i) + len (m (a + i)))

/-- The feedback of the last round played, `f t (x_t)` for `t = rounds - 1` (`0` before the first play). -/
noncomputable def feedback {d : ℕ} (w : World d) (s : State d) : ℝ :=
  if s.rounds = 0 then 0 else w.f (s.rounds - 1) (toE (s.pts (s.rounds - 1)))

/-- The integer whose binary digits, the most significant first, are the coins `c, c + 1, ..., c + k - 1` of the
stream `cs` (`1` for `true`). -/
def readCoins (cs : ℕ → Bool) (c : ℕ) : ℕ → ℤ
  | 0 => 0
  | k + 1 => 2 * readCoins cs c k + (if cs (c + k) then 1 else 0)

/-- The reading of `p` binary digits of the feedback: `⌊2^p o⌋`. -/
noncomputable def reading {d : ℕ} (w : World d) (s : State d) (p : ℕ) : ℤ :=
  ⌊(2 : ℝ) ^ p * feedback w s⌋

/-- One step of the machine, the cost of the instruction added to `cost`. -/
noncomputable def step {d : ℕ} (P : List Instr) (w : World d) (s : State d) : State d :=
  match P[s.pc]? with
  | none => s
  | some ins =>
    match ins with
    | .const dst c =>
      { s with pc := s.pc + 1, mem := Function.update s.mem dst c, cost := s.cost + (1 + len dst + len c) }
    | .add dst a b =>
      { s with pc := s.pc + 1, mem := Function.update s.mem dst (s.mem a + s.mem b),
               cost := s.cost + (1 + len dst + len a + len b + len (s.mem a) + len (s.mem b)) }
    | .sub dst a b =>
      { s with pc := s.pc + 1, mem := Function.update s.mem dst (s.mem a - s.mem b),
               cost := s.cost + (1 + len dst + len a + len b + len (s.mem a) + len (s.mem b)) }
    | .mul dst a b =>
      { s with pc := s.pc + 1, mem := Function.update s.mem dst (s.mem a * s.mem b),
               cost := s.cost + (1 + len dst + len a + len b + (len (s.mem a) + 1) * (len (s.mem b) + 1)) }
    | .div dst a b =>
      { s with pc := s.pc + 1, mem := Function.update s.mem dst (s.mem a / s.mem b),
               cost := s.cost + (1 + len dst + len a + len b + (len (s.mem a) + 1) * (len (s.mem b) + 1)) }
    | .load dst src =>
      { s with pc := s.pc + 1, mem := Function.update s.mem dst (s.mem (s.mem src)),
               cost := s.cost + (1 + len dst + len src + len (s.mem src) + len (s.mem (s.mem src))) }
    | .store dst src =>
      { s with pc := s.pc + 1, mem := Function.update s.mem (s.mem dst) (s.mem src),
               cost := s.cost + (1 + len dst + len src + len (s.mem dst) + len (s.mem src)) }
    | .jlt a b target =>
      { s with pc := if s.mem a < s.mem b then target else s.pc + 1,
               cost := s.cost + (1 + len a + len b + len (s.mem a) + len (s.mem b)) }
    | .jmp target => { s with pc := target, cost := s.cost + 1 }
    | .coins dst cnt =>
      { s with pc := s.pc + 1, mem := Function.update s.mem dst (readCoins w.cs s.coins (s.mem cnt).toNat),
               coins := s.coins + (s.mem cnt).toNat,
               cost := s.cost + (1 + len dst + len cnt + len (s.mem cnt) + (s.mem cnt).toNat) }
    | .play src =>
      { s with pc := s.pc + 1, rounds := s.rounds + 1,
               pts := Function.update s.pts s.rounds (ptAt d s.mem (s.mem src)),
               cost := s.cost + (1 + len src + len (s.mem src) + playCost d s.mem (s.mem src)) }
    | .obs dst prec =>
      { s with pc := s.pc + 1, mem := Function.update s.mem dst (reading w s (s.mem prec).toNat),
               cost := s.cost + (1 + len dst + len prec + len (s.mem prec) + (s.mem prec).toNat +
                 len (reading w s (s.mem prec).toNat)) }

/-- The state after `k` steps in a fixed world. -/
noncomputable def run {d : ℕ} (P : List Instr) (w : World d) (s0 : State d) (k : ℕ) : State d :=
  (step P w)^[k] s0

/-- The space of the state `s` is at most `B`: every finite set of cells in use (with a nonzero content) has addresses
and contents of total bit length at most `B`. -/
def SpaceLE {d : ℕ} (s : State d) (B : ℝ) : Prop :=
  ∀ F : Finset ℤ, (∀ c ∈ F, s.mem c ≠ 0) → ((∑ c ∈ F, (len c + len (s.mem c)) : ℕ) : ℝ) ≤ B

/-- The law of one fair coin: `true` and `false`, each with probability `1/2`. -/
noncomputable def coinLaw : Measure Bool :=
  (2⁻¹ : ENNReal) • (Measure.dirac true + Measure.dirac false)

/-- The coin stream: independent fair coins, the product of `coinLaw` over `ℕ`. -/
noncomputable def coinStream : Measure (ℕ → Bool) :=
  Measure.infinitePi fun _ : ℕ => coinLaw

end BitRAM

end AdversarialBco
