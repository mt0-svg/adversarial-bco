/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.PolyMap

@[expose] public section

/-!
# UNI-POLY, part 10: where the blocks sit in the compiled program

* `Fa_zero`, `Fa_succ`: the address of the block of the instruction `k + 1` is that of `k` plus its length.
* `codeAt_blk`: the block of the instruction at `k` of `P` sits at `Fa P pro.length k` of `compP pro P`.
* `rlen_blk`: a block other than a jump has the length of its command.
-/

namespace AdversarialBco.UniPoly

open AdversarialBco BitRAM BitRAMO
open AdversarialBco.Bit.Transfer (B.CodeAt)

theorem Fa_zero (P : List InstrO) (ob : ℕ) : Fa P ob 0 = ob := by simp [Fa]

theorem Fa_succ (P : List InstrO) (ob k : ℕ) : Fa P ob (k + 1) = Fa P ob k + blenAt P k := by
  simp [Fa, List.range_succ, Nat.add_assoc]

theorem blenAt_of (P : List InstrO) {k : ℕ} (hk : k < P.length) : blenAt P k = blen P[k] := by
  simp [blenAt, List.getElem?_eq_getElem hk]

theorem codeAt_append (l₁ l₂ : List Instr) : B.CodeAt (l₁ ++ l₂) l₁.length l₂ := fun i hi => by
  rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]

/-- The blocks from the instruction `k` on sit at `Fa P pro.length k`. -/
theorem codeAt_drop (pro : List Instr) (P : List InstrO) (k : ℕ) (hk : k ≤ P.length) :
    B.CodeAt (compP pro P) (Fa P pro.length k)
      (compB (Fa P pro.length) (P.drop k) (Fa P pro.length k)) := by
  induction k with
  | zero => rw [Fa_zero, List.drop_zero]; exact codeAt_append _ _
  | succ k ih =>
    have h := ih (by omega)
    rw [List.drop_eq_getElem_cons (by omega)] at h
    simp only [compB] at h
    have h2 := h.append_right
    rw [length_code, ← blenAt_of P (by omega), ← Fa_succ] at h2
    exact h2

/-- The block of the instruction at `k` sits at `Fa P pro.length k`. -/
theorem codeAt_blk (pro : List Instr) (P : List InstrO) {k : ℕ} (hk : k < P.length) :
    B.CodeAt (compP pro P) (Fa P pro.length k) (code (Fa P pro.length) P[k] (Fa P pro.length k)) := by
  have h := codeAt_drop pro P k (by omega)
  rw [List.drop_eq_getElem_cons hk] at h
  simp only [compB] at h
  exact h.append_left

end AdversarialBco.UniPoly
