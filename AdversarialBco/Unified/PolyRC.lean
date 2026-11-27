/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.Trans

@[expose] public section

/-!
# UNI-POLY, part 1: a structured language on the states of the bit machine

Corollary P compiles a program of the oracle machine into one of the bit machine. The code that
stands in for the oracle, the clipped reading and the indirect accesses is written in `RCmd`, a structured language
whose commands act directly on the states of the bit machine (StatementBitRAM.lean): an instruction other than a jump,
sequence, a test `M a < M b` with two branches, a loop on that test.

* `rtr c o`: the code of `c` placed at address `o`; `rlen c` its length.
* `RX w L c t n t'`: from the state `t`, `c` runs in the world `w` in `n` steps of the machine to the state `t'`
  (the counter of `t` kept, the cost of the tests and jumps charged), every address and value it touches of bit length
  at most `L` (`InsOK`, `TestOK`).
* `rtr_run`: the code `rtr c o` at address `o` of a program runs from `t` (counter set to `o`) in exactly `n` steps to
  `t'` (counter set to `o + rlen c`).
* `RX.cost_le`: the cost grows by at most `n * U d L`, `U d L = 4 + 6 L + (L + 1)² + (d + 1) (1 + 2 L)`.
-/

namespace AdversarialBco.UniPoly

open AdversarialBco BitRAM
open AdversarialBco.Bit.Transfer (B.CodeAt B.run_add B.run_one B.run_zero B.step_jlt B.step_jmp)

variable {d : ℕ}

/-! ## Lengths -/

theorem len_le_iff (z : ℤ) (L : ℕ) : len z ≤ L ↔ z.natAbs < 2 ^ L := Nat.size_le

theorem len_le_of_natAbs_lt {z : ℤ} {L : ℕ} (h : z.natAbs < 2 ^ L) : len z ≤ L := (len_le_iff z L).2 h

theorem natAbs_lt_of_len_le {z : ℤ} {L : ℕ} (h : len z ≤ L) : z.natAbs < 2 ^ L := (len_le_iff z L).1 h

theorem len_neg (z : ℤ) : len (-z) = len z := by simp [len]

theorem len_zero : len (0 : ℤ) = 0 := rfl

theorem len_one : len (1 : ℤ) = 1 := rfl

/-! ## The language -/

/-- An instruction that is not a jump. -/
def NJ : Instr → Prop
  | .jlt .. => False
  | .jmp _ => False
  | _ => True

/-- Structured commands on the states of the bit machine. -/
inductive RCmd
  | skip
  | ins (i : Instr)
  | seq (c₁ c₂ : RCmd)
  /-- `if M a < M b then c₁ else c₂`. -/
  | ifLt (a b : ℤ) (c₁ c₂ : RCmd)
  /-- `while M a < M b do c`. -/
  | whileLt (a b : ℤ) (c : RCmd)

/-- The length of the code of a command. -/
def rlen : RCmd → ℕ
  | .skip => 0
  | .ins _ => 1
  | .seq c₁ c₂ => rlen c₁ + rlen c₂
  | .ifLt _ _ c₁ c₂ => rlen c₁ + rlen c₂ + 2
  | .whileLt _ _ c => rlen c + 3

/-- The code of a command placed at address `o`: `ifLt` jumps to its first branch on the test, `whileLt` tests, jumps
out, runs the body and jumps back. -/
def rtr : RCmd → ℕ → List Instr
  | .skip, _ => []
  | .ins i, _ => [i]
  | .seq c₁ c₂, o => rtr c₁ o ++ rtr c₂ (o + rlen c₁)
  | .ifLt a b c₁ c₂, o =>
    Instr.jlt a b (o + 2 + rlen c₂) :: (rtr c₂ (o + 1) ++ (Instr.jmp (o + 2 + rlen c₂ + rlen c₁) ::
      rtr c₁ (o + 2 + rlen c₂)))
  | .whileLt a b c, o =>
    Instr.jlt a b (o + 2) :: Instr.jmp (o + 3 + rlen c) :: (rtr c (o + 2) ++ [Instr.jmp o])

theorem length_rtr (c : RCmd) (o : ℕ) : (rtr c o).length = rlen c := by
  induction c generalizing o <;> simp [rtr, rlen, *] ; omega

/-! ## Semantics -/

/-- One step of a non-jump instruction, the counter kept. -/
noncomputable def stepI (w : World d) (i : Instr) (t : State d) : State d :=
  { step [i] w { t with pc := 0 } with pc := t.pc }

/-- The state with `k` added to its cost. -/
def addC (t : State d) (k : ℕ) : State d := { t with cost := t.cost + k }

/-- The cost of the test `M a < M b`. -/
def tcost (a b : ℤ) (t : State d) : ℕ := 1 + len a + len b + len (t.mem a) + len (t.mem b)

/-- The bound on the cost of one instruction whose addresses and values have bit length at most `L`. -/
def U (d L : ℕ) : ℕ := 4 + 6 * L + (L + 1) ^ 2 + (d + 1) * (1 + 2 * L)

/-- An instruction within the bound `L`: its operands, the addresses it reads through, the values it reads and writes,
its counts and precisions of bit length (or size) at most `L`. -/
def InsOK (w : World d) (L : ℕ) (t : State d) : Instr → Prop
  | .const dst c => len dst ≤ L ∧ len c ≤ L
  | .add dst a b => len dst ≤ L ∧ len a ≤ L ∧ len b ≤ L ∧ len (t.mem a) ≤ L ∧ len (t.mem b) ≤ L
  | .sub dst a b => len dst ≤ L ∧ len a ≤ L ∧ len b ≤ L ∧ len (t.mem a) ≤ L ∧ len (t.mem b) ≤ L
  | .mul dst a b => len dst ≤ L ∧ len a ≤ L ∧ len b ≤ L ∧ len (t.mem a) ≤ L ∧ len (t.mem b) ≤ L
  | .div dst a b => len dst ≤ L ∧ len a ≤ L ∧ len b ≤ L ∧ len (t.mem a) ≤ L ∧ len (t.mem b) ≤ L
  | .load dst src => len dst ≤ L ∧ len src ≤ L ∧ len (t.mem src) ≤ L ∧ len (t.mem (t.mem src)) ≤ L
  | .store dst src => len dst ≤ L ∧ len src ≤ L ∧ len (t.mem dst) ≤ L ∧ len (t.mem src) ≤ L
  | .jlt .. => False
  | .jmp _ => False
  | .coins dst cnt => len dst ≤ L ∧ len cnt ≤ L ∧ len (t.mem cnt) ≤ L ∧ (t.mem cnt).toNat ≤ L
  | .play src => len src ≤ L ∧ len (t.mem src) ≤ L ∧
      ∀ i ≤ d, len (t.mem src + i) ≤ L ∧ len (t.mem (t.mem src + i)) ≤ L
  | .obs dst prec => len dst ≤ L ∧ len prec ≤ L ∧ len (t.mem prec) ≤ L ∧ (t.mem prec).toNat ≤ L ∧
      len (reading w t (t.mem prec).toNat) ≤ L

/-- A test within the bound `L`. -/
def TestOK (L : ℕ) (a b : ℤ) (t : State d) : Prop :=
  len a ≤ L ∧ len b ≤ L ∧ len (t.mem a) ≤ L ∧ len (t.mem b) ≤ L

/-- The big-step semantics with the step count `n` and the bound `L`. -/
inductive RX (w : World d) (L : ℕ) : RCmd → State d → ℕ → State d → Prop
  | skip (t : State d) : RX w L .skip t 0 t
  | ins (i : Instr) (t : State d) : InsOK w L t i → RX w L (.ins i) t 1 (stepI w i t)
  | seq {c₁ c₂ : RCmd} {t t₁ t₂ : State d} {n₁ n₂ : ℕ} :
      RX w L c₁ t n₁ t₁ → RX w L c₂ t₁ n₂ t₂ → RX w L (.seq c₁ c₂) t (n₁ + n₂) t₂
  | ifT {a b : ℤ} {c₁ c₂ : RCmd} {t t' : State d} {n : ℕ} :
      TestOK L a b t → t.mem a < t.mem b → RX w L c₁ (addC t (tcost a b t)) n t' →
        RX w L (.ifLt a b c₁ c₂) t (n + 1) t'
  | ifF {a b : ℤ} {c₁ c₂ : RCmd} {t t' : State d} {n : ℕ} :
      TestOK L a b t → ¬ t.mem a < t.mem b → RX w L c₂ (addC t (tcost a b t)) n t' →
        RX w L (.ifLt a b c₁ c₂) t (n + 2) (addC t' 1)
  | whT {a b : ℤ} {c : RCmd} {t t₁ t₂ : State d} {n₁ n₂ : ℕ} :
      TestOK L a b t → t.mem a < t.mem b → RX w L c (addC t (tcost a b t)) n₁ t₁ →
        RX w L (.whileLt a b c) (addC t₁ 1) n₂ t₂ → RX w L (.whileLt a b c) t (n₁ + n₂ + 2) t₂
  | whF {a b : ℤ} {c : RCmd} {t : State d} :
      TestOK L a b t → ¬ t.mem a < t.mem b → RX w L (.whileLt a b c) t 2 (addC t (tcost a b t + 1))

/-! ## The instructions -/

theorem stepI_eq {P : List Instr} {w : World d} {t : State d} {i : Instr} (h : P[t.pc]? = some i) (hi : NJ i) :
    step P w t = { stepI w i t with pc := t.pc + 1 } := by
  cases i <;> simp_all [stepI, step, NJ, feedback, reading]

theorem InsOK.nj {w : World d} {L : ℕ} {t : State d} {i : Instr} (h : InsOK w L t i) : NJ i := by
  cases i <;> simp_all [InsOK, NJ]

/-! ## The code runs -/

/-- The jump test at the start of a compiled `ifLt` or `whileLt`. -/
theorem run_jlt {P : List Instr} {w : World d} {t : State d} {o tg : ℕ} {a b : ℤ}
    (hj : P[o]? = some (.jlt a b tg)) :
    run P w { t with pc := o } 1 =
      { addC t (tcost a b t) with pc := if t.mem a < t.mem b then tg else o + 1 } := by
  have hj' : P[({ t with pc := o } : State d).pc]? = some (.jlt a b tg) := hj
  rw [B.run_one, B.step_jlt hj']
  simp [addC, tcost]

theorem run_jmp {P : List Instr} {w : World d} {t : State d} {o tg : ℕ} (hj : P[o]? = some (.jmp tg)) :
    run P w { t with pc := o } 1 = { addC t 1 with pc := tg } := by
  have hj' : P[({ t with pc := o } : State d).pc]? = some (.jmp tg) := hj
  rw [B.run_one, B.step_jmp hj']
  simp [addC]

theorem rtr_run {P : List Instr} {w : World d} {L : ℕ} {c : RCmd} {t t' : State d} {n : ℕ}
    (h : RX w L c t n t') : ∀ o, B.CodeAt P o (rtr c o) →
      run P w { t with pc := o } n = { t' with pc := o + rlen c } := by
  induction h with
  | skip t => intro o _; simp [rlen, B.run_zero]
  | ins i t hi =>
    intro o hc
    have h0 : P[({ t with pc := o } : State d).pc]? = some i := by simpa [rtr] using hc.cons_head
    rw [B.run_one, stepI_eq h0 hi.nj]
    cases t; simp [stepI, rlen]
  | seq _ _ ih₁ ih₂ =>
    intro o hc
    simp only [rtr] at hc
    have h1 := ih₁ o hc.append_left
    have h2 := ih₂ (o + rlen _) (by have := hc.append_right; rwa [length_rtr] at this)
    rw [B.run_add, h1, h2]
    simp [rlen, Nat.add_assoc]
  | @ifT a b c₁ c₂ t t' n ht hlt _ ih =>
    intro o hc
    simp only [rtr] at hc
    have hc₁ := hc.cons_tail.append_right.cons_tail
    rw [length_rtr] at hc₁
    have s1 := run_jlt (w := w) (t := t) hc.cons_head
    simp only [hlt, ↓reduceIte] at s1
    have s2 := ih (o + 2 + rlen c₂) (by rw [show o + 1 + rlen c₂ + 1 = o + 2 + rlen c₂ by omega] at hc₁; exact hc₁)
    rw [Nat.add_comm n 1, B.run_add, s1, s2]
    simp only [rlen]; congr 1; omega
  | @ifF a b c₁ c₂ t t' n ht hlt _ ih =>
    intro o hc
    simp only [rtr] at hc
    have hc₂ := hc.cons_tail.append_left
    have hjmp := hc.cons_tail.append_right.cons_head
    rw [length_rtr] at hjmp
    have s1 := run_jlt (w := w) (t := t) hc.cons_head
    simp only [hlt, ↓reduceIte] at s1
    have s2 := ih (o + 1) hc₂
    have s3 := run_jmp (w := w) (t := t') hjmp
    rw [show n + 2 = 1 + n + 1 by omega, B.run_add, B.run_add, s1, s2, s3]
    simp only [rlen]; congr 1; omega
  | @whT a b c t t₁ t₂ n₁ n₂ ht hlt _ _ ih₁ ih₂ =>
    intro o hc
    have hc' := hc
    simp only [rtr] at hc
    have hb := hc.cons_tail.cons_tail.append_left
    have hback := hc.cons_tail.cons_tail.append_right.cons_head
    rw [length_rtr] at hback
    have s1 := run_jlt (w := w) (t := t) hc.cons_head
    simp only [hlt, ↓reduceIte] at s1
    have s2 := ih₁ (o + 2) (by rw [show o + 2 = o + 1 + 1 by omega]; exact hb)
    have s3 := run_jmp (w := w) (t := t₁) (o := o + 1 + 1 + rlen c) hback
    have s4 := ih₂ o hc'
    rw [show n₁ + n₂ + 2 = 1 + n₁ + 1 + n₂ by omega, B.run_add, B.run_add, B.run_add, s1, s2,
      show o + 2 + rlen c = o + 1 + 1 + rlen c by omega, s3, s4]
  | @whF a b c t ht hlt =>
    intro o hc
    simp only [rtr] at hc
    have s1 := run_jlt (w := w) (t := t) hc.cons_head
    simp only [hlt, ↓reduceIte] at s1
    have s2 := run_jmp (w := w) (t := addC t (tcost a b t)) hc.cons_tail.cons_head
    rw [show (2 : ℕ) = 1 + 1 from rfl, B.run_add, s1, s2]
    simp only [rlen, addC]; congr 1; omega

/-! ## Cost -/

theorem cost_stepI {w : World d} {L : ℕ} {t : State d} {i : Instr} (h : InsOK w L t i) :
    (stepI w i t).cost ≤ t.cost + U d L := by
  unfold U
  have hsq : ∀ a b : ℕ, a ≤ L → b ≤ L → (a + 1) * (b + 1) ≤ (L + 1) ^ 2 := fun a b ha hb => by
    nlinarith
  cases i with
  | const dst c => obtain ⟨h1, h2⟩ := h; simp [stepI, step]; omega
  | add dst a b => obtain ⟨h1, h2, h3, h4, h5⟩ := h; simp [stepI, step]; omega
  | sub dst a b => obtain ⟨h1, h2, h3, h4, h5⟩ := h; simp [stepI, step]; omega
  | mul dst a b =>
    obtain ⟨h1, h2, h3, h4, h5⟩ := h; simp [stepI, step]
    have := hsq _ _ h4 h5; omega
  | div dst a b =>
    obtain ⟨h1, h2, h3, h4, h5⟩ := h; simp [stepI, step]
    have := hsq _ _ h4 h5; omega
  | load dst src => obtain ⟨h1, h2, h3, h4⟩ := h; simp [stepI, step]; omega
  | store dst src => obtain ⟨h1, h2, h3, h4⟩ := h; simp [stepI, step]; omega
  | jlt a b tg => exact h.elim
  | jmp tg => exact h.elim
  | coins dst cnt => obtain ⟨h1, h2, h3, h4⟩ := h; simp [stepI, step]; omega
  | play src =>
    obtain ⟨h1, h2, h3⟩ := h
    simp only [stepI, step, List.getElem?_cons_zero]
    have hpc : playCost d t.mem (t.mem src) ≤ (d + 1) * (1 + 2 * L) := by
      unfold playCost
      calc ∑ i ∈ Finset.range (d + 1), (1 + len (t.mem src + i) + len (t.mem (t.mem src + i)))
          ≤ ∑ _i ∈ Finset.range (d + 1), (1 + 2 * L) := Finset.sum_le_sum fun i hi => by
            have := h3 i (by simp at hi; omega); omega
        _ = (d + 1) * (1 + 2 * L) := by simp
    omega
  | obs dst prec =>
    obtain ⟨h1, h2, h3, h4, h5⟩ := h
    simp only [stepI, step, List.getElem?_cons_zero]
    have e : reading w { t with pc := 0 } (t.mem prec).toNat = reading w t (t.mem prec).toNat := rfl
    rw [e]; omega

theorem tcost_le {L : ℕ} {a b : ℤ} {t : State d} (h : TestOK L a b t) : tcost a b t ≤ 1 + 4 * L := by
  obtain ⟨h1, h2, h3, h4⟩ := h; unfold tcost; omega

theorem tcost_le_U {L : ℕ} {a b : ℤ} {t : State d} (h : TestOK L a b t) : tcost a b t + 1 ≤ 2 * U d L := by
  have := tcost_le h; unfold U; nlinarith

theorem tcost_le_U1 {L : ℕ} {a b : ℤ} {t : State d} (h : TestOK L a b t) : tcost a b t ≤ U d L := by
  have := tcost_le h; unfold U; nlinarith

/-- The cost grows by at most `n * U d L`. -/
theorem RX.cost_le {w : World d} {L : ℕ} {c : RCmd} {t t' : State d} {n : ℕ} (h : RX w L c t n t') :
    t'.cost ≤ t.cost + n * U d L := by
  induction h with
  | skip t => simp
  | ins i t hi => have := cost_stepI hi; simpa using this
  | seq _ _ ih₁ ih₂ => rw [Nat.add_mul]; omega
  | ifT ht _ _ ih =>
    have := tcost_le_U1 (d := d) ht; simp only [addC] at ih; rw [Nat.add_mul]; omega
  | @ifF a b c₁ c₂ t t' n ht _ _ ih =>
    have h1 := tcost_le_U (d := d) ht
    have h2 : (addC t' 1).cost = t'.cost + 1 := rfl
    have h3 : (addC t (tcost a b t)).cost = t.cost + tcost a b t := rfl
    rw [h2, Nat.add_mul]; rw [h3] at ih; omega
  | whT ht _ _ _ ih₁ ih₂ =>
    have := tcost_le_U (d := d) ht; simp only [addC] at ih₁ ih₂; rw [Nat.add_mul, Nat.add_mul]; omega
  | whF ht _ =>
    have := tcost_le_U (d := d) ht; simp only [addC]; omega

end AdversarialBco.UniPoly
