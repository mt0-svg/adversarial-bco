/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.PolyInst
public import AdversarialBco.Unified.PolyPro
public import AdversarialBco.Unified.PolyStep2

@[expose] public section

/-!
# UNI-POLY, part 16: the compiled program and the simulation (`sim`)

The compiled program is `compP proPr P`: the prologue of PolyPro.lean, then one block per instruction of `P`. From the
end of the prologue (`pro_run`), each step of `P` is matched by a stretch of the compiled program (`step_sim`), within
`Kc · c^3` when the feedback is in `[0, 1]`, `c` the cost of the step of `P`.

* `sim`: the times `g k` at which the compiled program is related to the `k`-th state of `P`, with the cost bounds.
-/

open MeasureTheory ProbabilityTheory

namespace AdversarialBco.UniPoly

open BitRAM BitRAMO Unified
open RealRAM (Strategy lossAd regretPts polytope HeightLE)
open Bit.Asm (InputOK)
open Bit.Transfer (B.run_add)

variable {d : ℕ}

/-! ## The program -/

/-- The prologue. -/
def proP : List Instr := proPr

/-- The compiled program. -/
def progP (P : List InstrO) : List Instr := compP proP P

/-- The bound on the bit length of the end of the buffer `Y`. -/
def LYv (d m : ℕ) : ℕ := YBv d m + d + 1

/-- The cost of a block for an instruction of cost `c`: `Kc d m M c^3`. -/
def Kc (d m M : ℕ) : ℕ := Kc0 d m M.size (LYv d m)

/-- The cost of the prologue. -/
def Cpro (d n m M : ℕ) : ℕ := CpL d n m M + Cset d n m M

/-! ## The simulation -/

/-- **The simulation.** -/
theorem sim (P : List InstrO) {n m M : ℕ} {A : Matrix (Fin m) (Fin d) ℚ} {b : Fin m → ℚ}
    (hI : InputOK d n m M A b) (w : World d) :
    ∃ g : ℕ → ℕ,
      (∀ k, Rel (Fa P proP.length) (run (progP P) w (initBit d n m A b) (g 0)).mem
        (runO P (worldO A b w) (s0U d n m A b) k) (run (progP P) w (initBit d n m A b) (g k))) ∧
      Monotone g ∧
      (run (progP P) w (initBit d n m A b) (g 0)).cost ≤ Cpro d n m M ∧
      ∀ k, FbOK w (run (progP P) w (initBit d n m A b) (g k)) →
        (run (progP P) w (initBit d n m A b) (g (k + 1))).cost ≤
          (run (progP P) w (initBit d n m A b) (g k)).cost +
            Kc d m M * ((runO P (worldO A b w) (s0U d n m A b) (k + 1)).cost -
              (runO P (worldO A b w) (s0U d n m A b) k).cost) ^ 3 := by
  obtain ⟨k0, hR0, hF, hc0⟩ := pro_run P hI w
  have hLY : len ((YBv d m : ℤ) + d + 1) ≤ LYv d m := by
    have := len_le_self_add (YBv d m + d + 1)
    push_cast at this
    exact this
  have hstep : ∀ s t : State d, ∃ j,
      Rel (Fa P proP.length) (run (progP P) w (initBit d n m A b) k0).mem s t →
        Rel (Fa P proP.length) (run (progP P) w (initBit d n m A b) k0).mem (stepO P (worldO A b w) s)
            (run (progP P) w t j) ∧
          (0 ≤ feedback w t → feedback w t ≤ 1 →
            (run (progP P) w t j).cost ≤ t.cost + Kc d m M * dC P (worldO A b w) s ^ 3) := by
    intro s t
    by_cases h : Rel (Fa P proP.length) (run (progP P) w (initBit d n m A b) k0).mem s t
    · obtain ⟨j, hj⟩ := step_sim (pro := proP) (worldO_toW A b w) (fun _ _ => rfl) hI.height hF hLY h
      exact ⟨j, fun _ => hj⟩
    · exact ⟨0, fun h' => absurd h' h⟩
  choose J hJ using hstep
  obtain ⟨g, hg0, hgs⟩ : ∃ g : ℕ → ℕ, g 0 = k0 ∧ ∀ k, g (k + 1) = g k +
      J (runO P (worldO A b w) (s0U d n m A b) k) (run (progP P) w (initBit d n m A b) (g k)) :=
    ⟨fun k => Nat.rec (motive := fun _ => ℕ) k0 (fun i gi =>
      gi + J (runO P (worldO A b w) (s0U d n m A b) i) (run (progP P) w (initBit d n m A b) gi)) k,
      rfl, fun _ => rfl⟩
  have hrel : ∀ k, Rel (Fa P proP.length) (run (progP P) w (initBit d n m A b) k0).mem
      (runO P (worldO A b w) (s0U d n m A b) k) (run (progP P) w (initBit d n m A b) (g k)) := by
    intro k
    induction k with
    | zero => rw [hg0]; exact hR0
    | succ k ih =>
      rw [hgs, B.run_add, RunFacts.runO_succ]
      exact (hJ _ _ ih).1
  refine ⟨g, fun k => by rw [hg0]; exact hrel k, monotone_nat_of_le_succ fun k => by rw [hgs k]; omega,
    by rw [hg0]; exact hc0, fun k hfb => ?_⟩
  rw [hgs, B.run_add, RunFacts.runO_succ]
  exact (hJ _ _ (hrel k)).2 hfb.1 hfb.2

end AdversarialBco.UniPoly
