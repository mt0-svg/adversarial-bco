/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.StatementBitRAM

@[expose] public section

/-!
# Leaves of the unified route: the lift of bit-machine runs to the oracle machine

UNI-MACH: the oracle machine adds a weak membership
query `orc` and a clipped noisy reading `obsR` to the bit machine of StatementBitRAM.lean, and steps a base
instruction as the bit machine on the lowered program, where every new instruction becomes a jump past the end. A run
of the oracle machine whose lowered run stays inside the code never met a new instruction, so it is the run of the bit
machine on the lowered program; every block-level fact about code without the new instructions carries
over through it.

`uni_lift_gen` is the lift for
any machine of this shape (a step that halts off the code, and on the code either steps as the bit machine on the
lowered program or is lowered to a jump past the end), so the oracle machine of StatementBitRAMO.lean gets its
`LiftOK` from it in a few lines (LeafFrozen.lean).
-/

namespace AdversarialBco

namespace Uni

open BitRAM

/-- A state at or past the end of the code is a fixed point of the bit machine. -/
theorem uni_step_halted {d : ℕ} (P : List Instr) (W : World d) (s : State d) (h : P.length ≤ s.pc) :
    step P W s = s := by
  unfold step
  rw [List.getElem?_eq_none h]

/-- The lift for any machine of the lowering shape: if the machine `stepO` halts off the code `P` and, at an
instruction `i` of `P`, either steps as the bit machine on the lowered code `P.map low` or `i` is lowered to a jump
past the end, then every run of `stepO` whose lowered run ends inside the code is that lowered run. -/
theorem uni_lift_gen {d : ℕ} {α : Type*} (P : List α) (low : α → Instr) (W : World d)
    (stepO : State d → State d) (hnone : ∀ s : State d, P[s.pc]? = none → stepO s = s)
    (hsome : ∀ (s : State d) (i : α), P[s.pc]? = some i →
      stepO s = step (P.map low) W s ∨ low i = .jmp P.length)
    (s : State d) (k : ℕ) (hpc : (run (P.map low) W s k).pc < P.length) :
    stepO^[k] s = run (P.map low) W s k := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
    have hrun : run (P.map low) W s (k + 1) = run (P.map low) W (step (P.map low) W s) k :=
      Function.iterate_succ_apply _ _ _
    rw [hrun] at hpc ⊢
    rw [Function.iterate_succ_apply]
    cases hPs : P[s.pc]? with
    | none =>
      have hL : (P.map low)[s.pc]? = none := by rw [List.getElem?_map, hPs]; rfl
      have h1 : step (P.map low) W s = s := by unfold step; rw [hL]
      rw [h1] at hpc
      rw [hnone s hPs, h1]
      exact ih s hpc
    | some i =>
      rcases hsome s i hPs with h | h
      · rw [h]
        exact ih _ hpc
      · exfalso
        have hL : (P.map low)[s.pc]? = some (.jmp P.length) := by
          rw [List.getElem?_map, hPs, Option.map_some, h]
        have h1 : (step (P.map low) W s).pc = P.length := by unfold step; rw [hL]
        have h2 : run (P.map low) W (step (P.map low) W s) k = step (P.map low) W s :=
          Function.iterate_fixed (uni_step_halted _ _ _ (by rw [List.length_map, h1])) k
        rw [h2, h1] at hpc
        exact lt_irrefl _ hpc

end Uni

end AdversarialBco
