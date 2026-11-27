/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.PolyRC
public import AdversarialBco.StatementBitRAMO

@[expose] public section

/-!
# UNI-POLY, part 2: the compiled program

A program `P` of the oracle machine (StatementBitRAMO.lean) becomes a program of the bit machine: a prologue, then one
block per instruction of `P`.

* Memory: the cell `x` of `P` is the cell `φ x = -N0 - 2x` (`x ≥ 0`), `-N0 + 2x + 1` (`x < 0`), a bijection of `ℤ`
  onto the cells `≤ -N0`. The cells above `-N0` hold the input of the bit machine, what the prologue left, the scratch
  cells of the blocks (`cZ`, ..., all `0` between blocks) and the buffer `Y` (`d + 1` cells from the address held in
  `cYB`, `0` between blocks).
* Blocks: a base instruction with direct operands is itself on the cells `φ`; `jlt` and `jmp` jump to the block of
  their target (`F`); `load`, `store` compute `φ` of the address at run time (`PHI`); `play` copies the point into `Y`
  with a positive denominator (`COPYN`), plays `Y` and clears it (`CLEARY`); `orc` copies, tests membership in the
  polytope of the input rows (`ROWMEM`) and clears; `obsR` reads with `obs`, computes `2^q` and clips.
-/

namespace AdversarialBco.UniPoly

open AdversarialBco BitRAM BitRAMO

variable {d : ℕ}

/-! ## The relocation -/

/-- The first cell of `P`'s region, negated. -/
abbrev N0 : ℤ := 1000

/-- The cell of `P`'s cell `x`. -/
def φ (x : ℤ) : ℤ := if 0 ≤ x then -N0 - 2 * x else -N0 + 2 * x + 1

theorem φ_le (x : ℤ) : φ x ≤ -N0 := by unfold φ; split_ifs <;> omega

theorem φ_ne_of_gt {x c : ℤ} (h : -N0 < c) : φ x ≠ c := fun e => by have := φ_le x; omega

theorem φ_inj {x y : ℤ} (h : φ x = φ y) : x = y := by
  unfold φ at h; split_ifs at h <;> omega

theorem φ_ne {x y : ℤ} (h : x ≠ y) : φ x ≠ φ y := fun e => h (φ_inj e)

theorem φ_surj {c : ℤ} (h : c ≤ -N0) : ∃ x, φ x = c := by
  unfold φ N0 at *
  rcases Int.emod_two_eq_zero_or_one (c + 1000) with h2 | h2
  · refine ⟨-(c + 1000) / 2, ?_⟩
    split_ifs <;> omega
  · refine ⟨(c + 1000 - 1) / 2, ?_⟩
    split_ifs <;> omega

theorem φ_natAbs (x : ℤ) : (φ x).natAbs ≤ 1001 + 2 * x.natAbs := by unfold φ N0; split_ifs <;> omega

theorem len_φ (x : ℤ) : len (φ x) ≤ len x + 11 := by
  rw [len_le_iff]
  have h1 := φ_natAbs x
  have h2 := Nat.lt_size_self x.natAbs
  have h3 : (2 : ℕ) ^ (len x + 11) = 2 ^ len x * 2048 := by rw [pow_add]; norm_num
  unfold len at h3 ⊢
  rw [h3]; nlinarith [Nat.one_le_two_pow (n := x.natAbs.size)]

/-! ## Scratch cells -/

/-- The cell always `0`. -/
scoped notation "cZ" => (-600 : ℤ)
/-- The cell holding the address of the buffer `Y`. -/
scoped notation "cYB" => (-601 : ℤ)
scoped notation "cA" => (-602 : ℤ)
scoped notation "cC" => (-603 : ℤ)
scoped notation "cV" => (-604 : ℤ)
scoped notation "cI" => (-605 : ℤ)
scoped notation "cD1" => (-606 : ℤ)
scoped notation "cOne" => (-607 : ℤ)
scoped notation "cX" => (-608 : ℤ)
scoped notation "cB" => (-609 : ℤ)
scoped notation "cS" => (-610 : ℤ)
scoped notation "cQ" => (-611 : ℤ)
scoped notation "cN" => (-612 : ℤ)
scoped notation "cDD" => (-613 : ℤ)
scoped notation "cY" => (-614 : ℤ)
scoped notation "cT" => (-615 : ℤ)
scoped notation "cE" => (-616 : ℤ)
scoped notation "cE1" => (-617 : ℤ)
scoped notation "cJ" => (-618 : ℤ)
scoped notation "cYP" => (-619 : ℤ)
scoped notation "cR" => (-620 : ℤ)
scoped notation "cL" => (-621 : ℤ)
scoped notation "cRt" => (-622 : ℤ)
scoped notation "cSg" => (-623 : ℤ)
scoped notation "cY0" => (-624 : ℤ)
scoped notation "cP" => (-625 : ℤ)
scoped notation "cNP" => (-626 : ℤ)
scoped notation "cAa" => (-627 : ℤ)

/-- A scratch cell (all but `cYB`): `-627 ≤ c ≤ -602` or `c = -600`. -/
def IsScr (c : ℤ) : Prop := c = cZ ∨ (-627 ≤ c ∧ c ≤ -602)

/-! ## The blocks -/

open RCmd

/-- `seq` of a list of commands. -/
def seqL : List RCmd → RCmd
  | [] => .skip
  | [c] => c
  | c :: cs => .seq c (seqL cs)

/-- A straight line of instructions. -/
def seqI : List Instr → RCmd
  | [] => .skip
  | [i] => .ins i
  | i :: is => .seq (.ins i) (seqI is)

/-- `dst := φ (M src)`, through `cC`, which ends at `0`. -/
def PHI (src dst : ℤ) : RCmd :=
  seqL [.ifLt src cZ
    (seqL [.ins (.add dst src src), .ins (.const cC (1 - N0)), .ins (.add dst dst cC)])
    (seqL [.ins (.add dst src src), .ins (.const cC (-N0)), .ins (.sub dst cC dst)]),
    .ins (.const cC 0)]

/-- `load dst src` of `P`. -/
def LOADB (dst src : ℤ) : RCmd :=
  seqL [PHI (φ src) cA, seqI [.load (φ dst) cA, .const cA 0]]

/-- `store dst src` of `P`. -/
def STOREB (dst src : ℤ) : RCmd :=
  seqL [PHI (φ dst) cA, seqI [.store cA (φ src), .const cA 0]]

/-- The copy loop: `Y_i := sg · y_i` for `i ≤ d`, `y_i` the cell `a + i` of `P`, `a` in `cAa`. -/
def COPYLOOP : RCmd :=
  .whileLt cI cD1 (seqL [.ins (.add cX cAa cI), PHI cX cA,
    seqI [.load cV cA, .mul cV cV cSg, .add cB cYB cI, .store cB cV, .add cI cI cOne, .const cX 0, .const cA 0,
      .const cV 0, .const cB 0]])

/-- The scratch cells that `COPYN` clears. -/
def copyClr : List Instr :=
  [.const cAa 0, .const cOne 0, .const cD1 0, .const cY0 0, .const cSg 0, .const cI 0, .const cX 0, .const cV 0,
    .const cB 0, .const cA 0]

/-- The point of `P` at `a = M src` into `Y`, with a positive denominator and the same point: `Y = sg · y` with
`sg` the sign of `y_0`, or `Y = (1, 0, ..., 0)` if `y_0 = 0`. The scratch cells end at `0`. -/
def COPYN (src : ℤ) : RCmd :=
  seqL [seqI [.add cAa (φ src) cZ, .const cOne 1, .add cD1 0 cOne], PHI cAa cA,
    seqI [.load cY0 cA, .const cSg 1, .const cA 0],
    .ifLt cY0 cZ (.ins (.const cSg (-1))) .skip,
    .ifLt cZ cY0 COPYLOOP (.ifLt cY0 cZ COPYLOOP (.ins (.store cYB cOne))),
    seqI copyClr]

/-- `Y := 0`. -/
def CLEARY : RCmd :=
  seqL [seqI [.const cOne 1, .add cD1 0 cOne],
    .whileLt cI cD1 (seqI [.add cB cYB cI, .store cB cZ, .add cI cI cOne, .const cB 0]),
    seqI [.const cOne 0, .const cD1 0, .const cI 0, .const cB 0]]

/-- The inner loop of `ROWMEM` over the columns `j < d` of a row: `S/Q := S/Q + (num/den) Y_{1+j}`. -/
def ROWIN : RCmd :=
  .whileLt cJ 0 (seqI [.load cN cE, .add cE1 cE cOne, .load cDD cE1, .load cY cYP,
    .mul cS cS cDD, .mul cT cN cY, .mul cT cT cQ, .add cS cS cT, .mul cQ cQ cDD,
    .add cE cE1 cOne, .add cYP cYP cOne, .add cJ cJ cOne, .const cN 0, .const cE1 0, .const cDD 0, .const cY 0,
    .const cT 0])

/-- The body of `ROWMEM` for one row. -/
def ROWBODY : RCmd :=
  seqL [seqI [.const cS 0, .const cQ 1, .const cJ 0, .add cYP cYB cOne], ROWIN,
    seqI [.load cN cE, .add cE1 cE cOne, .load cDD cE1, .load cY0 cYB, .mul cL cS cDD, .mul cRt cN cQ,
      .mul cRt cRt cY0],
    .ifLt cRt cL (.ins (.const cR 0)) .skip,
    seqI [.add cE cE1 cOne, .add cI cI cOne, .const cN 0, .const cE1 0, .const cDD 0, .const cY0 0, .const cL 0,
      .const cRt 0, .const cS 0, .const cQ 0, .const cJ 0, .const cYP 0]]

/-- The scratch cells that `ROWMEM` clears. -/
def rowClr : List Instr := [.const cOne 0, .const cE 0, .const cI 0]

/-- Membership of the point `Y` (`Y_0 > 0`) in the polytope of the input rows: `cR := 1` or `0`. -/
def ROWMEM : RCmd :=
  seqL [seqI [.const cR 1, .const cOne 1, .const cE 3], .whileLt cI 2 ROWBODY, seqI rowClr]

/-- `play src` of `P`. -/
def PLAYB (src : ℤ) : RCmd := seqL [COPYN src, .ins (.play cYB), CLEARY]

/-- `orc dst src prec` of `P`, with the exact membership in the polytope. -/
def ORCB (dst src : ℤ) : RCmd :=
  seqL [COPYN src, ROWMEM, seqI [.add (φ dst) cR cZ, .const cR 0], CLEARY]

/-- `obsR dst prec rng` of `P`: `obs`, `2^q` by doubling, the clip. -/
def OBSRB (dst prec rng : ℤ) : RCmd :=
  seqL [seqI [.obs cV (φ prec), .const cOne 1, .const cP 1, .add cQ (φ rng) cZ],
    .whileLt cI cQ (seqI [.add cP cP cP, .add cI cI cOne]),
    .ifLt cP cV (.ins (.add cV cP cZ)) .skip, .ins (.sub cNP cZ cP),
    .ifLt cV cNP (.ins (.add cV cNP cZ)) .skip,
    seqI [.add (φ dst) cV cZ, .const cV 0, .const cOne 0, .const cP 0, .const cQ 0, .const cI 0, .const cNP 0]]

/-- The block of an instruction of `P` other than a jump. -/
def blk : InstrO → RCmd
  | .base (.const dst c) => .ins (.const (φ dst) c)
  | .base (.add dst a b) => .ins (.add (φ dst) (φ a) (φ b))
  | .base (.sub dst a b) => .ins (.sub (φ dst) (φ a) (φ b))
  | .base (.mul dst a b) => .ins (.mul (φ dst) (φ a) (φ b))
  | .base (.div dst a b) => .ins (.div (φ dst) (φ a) (φ b))
  | .base (.load dst src) => LOADB dst src
  | .base (.store dst src) => STOREB dst src
  | .base (.jlt _ _ _) => .skip
  | .base (.jmp _) => .skip
  | .base (.coins dst cnt) => .ins (.coins (φ dst) (φ cnt))
  | .base (.play src) => PLAYB src
  | .base (.obs dst prec) => .ins (.obs (φ dst) (φ prec))
  | .orc dst src _ => ORCB dst src
  | .obsR dst prec rng => OBSRB dst prec rng

/-- The length of the block of an instruction. -/
def blen : InstrO → ℕ
  | .base (.jlt _ _ _) => 1
  | .base (.jmp _) => 1
  | i => rlen (blk i)

/-- The code of the block of an instruction at `o`, with the jump targets through `F`. -/
def code (F : ℕ → ℕ) : InstrO → ℕ → List Instr
  | .base (.jlt a b tg), _ => [.jlt (φ a) (φ b) (F tg)]
  | .base (.jmp tg), _ => [.jmp (F tg)]
  | i, o => rtr (blk i) o

theorem length_code (F : ℕ → ℕ) (i : InstrO) (o : ℕ) : (code F i o).length = blen i := by
  rcases i with i | _ | _
  · cases i <;> simp [code, blen, length_rtr]
  · simp [code, blen, length_rtr]
  · simp [code, blen, length_rtr]

/-- The length of the block of the instruction at `j` (`1` past the end). -/
def blenAt (P : List InstrO) (j : ℕ) : ℕ :=
  match P[j]? with
  | some i => blen i
  | none => 1

/-- The address of the block of the instruction at `i`, the blocks from `ob` on. -/
def Fa (P : List InstrO) (ob i : ℕ) : ℕ := ob + ((List.range i).map (blenAt P)).sum

/-- The blocks of the instructions of `l`, the first at `o`. -/
def compB (F : ℕ → ℕ) : List InstrO → ℕ → List Instr
  | [], _ => []
  | i :: l, o => code F i o ++ compB F l (o + blen i)

/-- The compiled program: the prologue `pro`, then the blocks. -/
def compP (pro : List Instr) (P : List InstrO) : List Instr :=
  pro ++ compB (Fa P pro.length) P pro.length

/-! ## The state of `P` in the state of the compiled program -/

/-- The bit state `t` of the compiled program holds the state `s` of `P`: the counter at the block of `s.pc`, the cells
of `P` at `φ`, the cells above `-N0` as in `Fix`, the coins used, the rounds and the points played. -/
structure Rel (F : ℕ → ℕ) (Fix : ℤ → ℤ) (s t : State d) : Prop where
  pc : t.pc = F s.pc
  z : ∀ x, t.mem (φ x) = s.mem x
  fix : ∀ c, -N0 < c → t.mem c = Fix c
  coins : t.coins = s.coins
  rounds : t.rounds = s.rounds
  pts : t.pts = s.pts

end AdversarialBco.UniPoly
