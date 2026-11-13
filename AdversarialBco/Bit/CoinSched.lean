/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.ShadowIface

@[expose] public section

/-!
# BL's coin schedule and the digit map of (W0)

The shared interface between BL's program (or its pure Lean function) and the coupled world of SHADOW: which coins BL
reads, in which blocks, and what each coin is on the Gaussian stream.

**The schedule.** BL reads its coins in a fixed order, the same on every run (W0c). The prologue reads the coins
`0, ..., K0 - 1` (TRI-OGD staged reads the first `m_st L` of them). Then round `t` reads `nBlk d = ⌈d/2⌉ + 1` blocks of
`2B` coins, block `q` from the coin `blkStart d K0 B t q`; in each block the first `B` coins are the digits of `U`, the
next `B` those of `W`, most significant first (`readCoins`, StatementBitRAM.lean), and BL runs `BM-INT(B)` on `(U, W)`.
Block `q < ⌈d/2⌉` gives the draws `ξ'_{2q}, ξ'_{2q+1}` (for odd `d` the last of them gives `ξ'_{d-1}` and drops its
second output); the last block, `q = ⌈d/2⌉`, gives the dither `ζ'` (half its first output).

**The digit map** (`beta`). Every block sits on a pair of terms of the Gaussian stream (`pairOf`): the prologue block
`k` (coins `2Bk, ..., 2Bk + 2B - 1`) on the odd terms `4k + 1`, `4k + 3`; the block `q` of round `t` on the terms of
roles `2q`, `2q + 1` of round `t` (`cIdx`, Bit/ShadowIface.lean; role `d` is the padding `π'_t` when `d` is odd) for
the draws, on the roles `d + 1`, `d + 2` (`Z̃_t` and its padding `π_t`) for the dither. On the pair `(x, y)` of a
block, `(u, w) = bmInv (x, y) = (exp(-(x² + y²)/2), arg(x + iy)/(2π))` with the angle in `(0, 2π]`, and the block's
coins are the `B` digits of `⌈2^B u⌉ - 1` and the `B` digits of `⌈2^B w⌉ - 1` (`dig`). So `BM-INT` runs on the dyadic
cell of the exact pair `bmInv (x, y)`, whose Box-Muller image is `(x, y)`.
-/

open MeasureTheory

namespace AdversarialBco.Bit.Sched

open AdversarialBco.Bit.Cpl

/-! ## The schedule -/

/-- The number of blocks of a round: `⌈d/2⌉` draw pairs and the dither pair. -/
def nBlk (d : ℕ) : ℕ := (d + 1) / 2 + 1

/-- The first coin of block `q` of round `t`: after the `K0` coins of the prologue, the rounds, `nBlk d` blocks of `2B`
coins each. -/
def blkStart (d K0 B t q : ℕ) : ℕ := K0 + 2 * B * (t * nBlk d + q)

/-- The block of coin `j`: `inl k`, the block `k` of the prologue; `inr k`, the block `k` of the rounds (block `q` of
round `t` is `t * nBlk d + q`). -/
def blkOf (K0 B j : ℕ) : ℕ ⊕ ℕ := if j < K0 then .inl (j / (2 * B)) else .inr ((j - K0) / (2 * B))

/-- The position of coin `j` in its block, in `[0, 2B)`. -/
def posOf (K0 B j : ℕ) : ℕ := if j < K0 then j % (2 * B) else (j - K0) % (2 * B)

/-- The two terms of the Gaussian stream of a block: the prologue block `k` on `4k + 1`, `4k + 3`; the round block
`t * nBlk d + q` on the roles `2q`, `2q + 1` of round `t` for `q + 1 < nBlk d`, on the roles `d + 1`, `d + 2` for the
last block. -/
def pairOf (d : ℕ) : ℕ ⊕ ℕ → ℕ × ℕ
  | .inl k => (4 * k + 1, 4 * k + 3)
  | .inr k =>
    if k % nBlk d + 1 = nBlk d then (cIdx d (k / nBlk d) (d + 1), cIdx d (k / nBlk d) (d + 2))
    else (cIdx d (k / nBlk d) (2 * (k % nBlk d)), cIdx d (k / nBlk d) (2 * (k % nBlk d) + 1))

/-- The coins read before round `t`. -/
def rdBefore (d K0 B t : ℕ) : Set ℕ := {j | j < blkStart d K0 B t 0}

/-- The group of coin `j`: the two terms of the Gaussian stream of its block. -/
def grp (d K0 B j : ℕ) : Set ℕ := {(pairOf d (blkOf K0 B j)).1, (pairOf d (blkOf K0 B j)).2}

/-! ## The inverse Box-Muller map and the digits -/

/-- The angle of `(x, y)` over `2π`, in `(0, 1]`. -/
noncomputable def bmW (x y : ℝ) : ℝ :=
  if 0 < Complex.arg ⟨x, y⟩ then Complex.arg ⟨x, y⟩ / (2 * Real.pi) else Complex.arg ⟨x, y⟩ / (2 * Real.pi) + 1

/-- The inverse of the Box-Muller map (LAW-4): `(exp(-(x² + y²)/2), bmW x y)`. -/
noncomputable def bmInv (p : ℝ × ℝ) : ℝ × ℝ := (Real.exp (-(p.1 ^ 2 + p.2 ^ 2) / 2), bmW p.1 p.2)

/-- The Box-Muller map `(u, w) ↦ ((-2 log u)^{1/2} cos 2πw, (-2 log u)^{1/2} sin 2πw)` (`boxMuller_law2`). -/
noncomputable def bm (p : ℝ × ℝ) : ℝ × ℝ :=
  (Real.sqrt (-2 * Real.log p.1) * Real.cos (2 * Real.pi * p.2),
    Real.sqrt (-2 * Real.log p.1) * Real.sin (2 * Real.pi * p.2))

/-- The cell of `v ∈ (0, 1]` at the grid `2^{-B}`: `⌈2^B v⌉ - 1 ∈ [0, 2^B)`. -/
noncomputable def cellIdx (B : ℕ) (v : ℝ) : ℕ := (⌈(2 : ℝ) ^ B * v⌉ - 1).toNat

/-- The digit `i < B` of the cell of `v`, most significant first. -/
noncomputable def dig (B : ℕ) (v : ℝ) (i : ℕ) : Bool := (cellIdx B v).testBit (B - 1 - i)

/-- The coins of a block on the pair `p` of the stream: position `s < B` the digit `s` of the cell of `u`, position
`B + s` the digit `s` of the cell of `w`, `(u, w) = bmInv p`. -/
noncomputable def blkCoin (B : ℕ) (p : ℝ × ℝ) (s : ℕ) : Bool :=
  if s < B then dig B (bmInv p).1 s else dig B (bmInv p).2 (s - B)

/-- The digit map of (W0): coin `j` is the coin at position `posOf K0 B j` of its block, on the pair of the stream of
the block. -/
noncomputable def beta (d K0 B : ℕ) (x : ℕ → ℝ) (j : ℕ) : Bool :=
  blkCoin B (x (pairOf d (blkOf K0 B j)).1, x (pairOf d (blkOf K0 B j)).2) (posOf K0 B j)

end AdversarialBco.Bit.Sched
