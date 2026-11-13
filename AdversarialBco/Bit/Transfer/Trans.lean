/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.StatementBitRAM
public import AdversarialBco.Poly.MachLang
public import AdversarialBco.Bit.Transfer.Len

@[expose] public section

/-!
# The integer fragment of the real machine, and the bit machine

* Runs of the frozen bit machine (`StatementBitRAM.lean`): `run_add`, `run_one`, `run_zero`; `CodeAt P o l`, the code
  `l` placed at address `o` of `P`; one step of each instruction (`step_const` to `step_jmp`, `const_spec` to
  `jmp_spec`).
* The cells: natural register `i` is the cell `rg i = -(i + 4)`, real cell `j` is the cell `j`, and the cells `-1`,
  `-2` (`T1`, `T2`) are scratch; `opI`, `opZ`: the instruction and the integer value of a binary operation.
* `ExecB ℓa ℓ w c s k s'`: `Exec` (`Poly/MachLang.lean`) restricted to the integer fragment (integer constants,
  `+ - ×` on cells, natural constants, sums, differences without truncation and casts, both tests, both loops), with
  every register index and register content below `2 ^ ℓa` and every real value read or written of absolute value
  below `2 ^ ℓ`.
* The bit lengths of the cells and of the values (`len_rg`, `len_nat`, `len_val`), the cost `opC` of an operation.
-/

namespace AdversarialBco.Bit.Transfer

open AdversarialBco
open AdversarialBco.Poly.Mach (Prim Cmd condR condN)

variable {d : ℕ}

/-! ## Runs of the bit machine -/

namespace B

open BitRAM

theorem run_add (P : List Instr) (w : World d) (s : State d) (k j : ℕ) :
    run P w s (k + j) = run P w (run P w s k) j := by
  simp only [run]; rw [add_comm, Function.iterate_add_apply]

theorem run_one (P : List Instr) (w : World d) (s : State d) : run P w s 1 = step P w s := rfl

theorem run_zero (P : List Instr) (w : World d) (s : State d) : run P w s 0 = s := rfl

/-- The list `l` sits at address `o` of `P`. -/
def CodeAt (P : List Instr) (o : ℕ) (l : List Instr) : Prop := ∀ i < l.length, P[o + i]? = l[i]?

theorem CodeAt.append_left {P : List Instr} {o : ℕ} {l₁ l₂ : List Instr} (h : CodeAt P o (l₁ ++ l₂)) :
    CodeAt P o l₁ := fun i hi => by
  rw [h i (by simp; omega), List.getElem?_append_left hi]

theorem CodeAt.append_right {P : List Instr} {o : ℕ} {l₁ l₂ : List Instr} (h : CodeAt P o (l₁ ++ l₂)) :
    CodeAt P (o + l₁.length) l₂ := fun i hi => by
  have := h (l₁.length + i) (by simp; omega)
  rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left] at this
  rw [← this, Nat.add_assoc]

theorem CodeAt.cons_head {P : List Instr} {o : ℕ} {x : Instr} {l : List Instr} (h : CodeAt P o (x :: l)) :
    P[o]? = some x := by
  simpa using h 0 (by simp)

theorem CodeAt.cons_tail {P : List Instr} {o : ℕ} {x : Instr} {l : List Instr} (h : CodeAt P o (x :: l)) :
    CodeAt P (o + 1) l := fun i hi => by
  have := h (i + 1) (by simp; omega)
  rw [← Nat.add_assoc, Nat.add_right_comm] at this
  simpa using this

theorem step_const {P : List Instr} {w : World d} {t : State d} {dst c : ℤ} (h : P[t.pc]? = some (.const dst c)) :
    step P w t = { t with pc := t.pc + 1, mem := Function.update t.mem dst c, cost := t.cost + (1 + len dst + len c) } := by
  simp [step, h]

theorem step_add {P : List Instr} {w : World d} {t : State d} {dst a b : ℤ} (h : P[t.pc]? = some (.add dst a b)) :
    step P w t = { t with pc := t.pc + 1, mem := Function.update t.mem dst (t.mem a + t.mem b),
                            cost := t.cost + (1 + len dst + len a + len b + len (t.mem a) + len (t.mem b)) } := by
  simp [step, h]

theorem step_sub {P : List Instr} {w : World d} {t : State d} {dst a b : ℤ} (h : P[t.pc]? = some (.sub dst a b)) :
    step P w t = { t with pc := t.pc + 1, mem := Function.update t.mem dst (t.mem a - t.mem b),
                            cost := t.cost + (1 + len dst + len a + len b + len (t.mem a) + len (t.mem b)) } := by
  simp [step, h]

theorem step_load {P : List Instr} {w : World d} {t : State d} {dst src : ℤ} (h : P[t.pc]? = some (.load dst src)) :
    step P w t = { t with pc := t.pc + 1, mem := Function.update t.mem dst (t.mem (t.mem src)),
                            cost := t.cost + (1 + len dst + len src + len (t.mem src) + len (t.mem (t.mem src))) } := by
  simp [step, h]

theorem step_store {P : List Instr} {w : World d} {t : State d} {dst src : ℤ} (h : P[t.pc]? = some (.store dst src)) :
    step P w t = { t with pc := t.pc + 1, mem := Function.update t.mem (t.mem dst) (t.mem src),
                            cost := t.cost + (1 + len dst + len src + len (t.mem dst) + len (t.mem src)) } := by
  simp [step, h]

theorem step_jlt {P : List Instr} {w : World d} {t : State d} {a b : ℤ} {tg : ℕ} (h : P[t.pc]? = some (.jlt a b tg)) :
    step P w t = { t with pc := if t.mem a < t.mem b then tg else t.pc + 1,
                            cost := t.cost + (1 + len a + len b + len (t.mem a) + len (t.mem b)) } := by
  simp [step, h]

theorem step_jmp {P : List Instr} {w : World d} {t : State d} {tg : ℕ} (h : P[t.pc]? = some (.jmp tg)) :
    step P w t = { t with pc := tg, cost := t.cost + 1 } := by
  simp [step, h]

end B

/-! ## The cells and the arithmetic instructions -/

/-- The cell of natural register `i`. -/
def rg (i : ℕ) : ℤ := -((i : ℤ) + 4)

/-- The first scratch cell. -/
def T1 : ℤ := -1

/-- The second scratch cell. -/
def T2 : ℤ := -2

/-- The arithmetic instruction of a binary operation. -/
def opI : RealRAM.Op2 → ℤ → ℤ → ℤ → BitRAM.Instr
  | .add, x, a, b => .add x a b
  | .sub, x, a, b => .sub x a b
  | .mul, x, a, b => .mul x a b
  | .div, x, a, b => .div x a b

/-- The value of a binary operation on integers. -/
def opZ : RealRAM.Op2 → ℤ → ℤ → ℤ
  | .add, x, y => x + y
  | .sub, x, y => x - y
  | .mul, x, y => x * y
  | .div, x, y => x / y

/-! ## The bounded fragment -/

/-- Register `i` has an address of at most `ℓa` bits and holds a natural of at most `ℓa` bits. -/
def RegOK (ℓa : ℕ) (s : RealRAM.State d) (i : ℕ) : Prop := i + 4 < 2 ^ ℓa ∧ s.nreg i < 2 ^ ℓa

/-- A primitive of the fragment, with its registers within `ℓa` bits and the reals it reads and writes within `ℓ`
bits. -/
def PrimOK (ℓa ℓ : ℕ) (s : RealRAM.State d) : Prim → Prop
  | .rconst dst q => RegOK ℓa s dst ∧ q.den = 1 ∧ |(q : ℝ)| < 2 ^ ℓ
  | .op2 o dst a b => o ≠ .div ∧ RegOK ℓa s dst ∧ RegOK ℓa s a ∧ RegOK ℓa s b ∧ |s.mem (s.nreg a)| < 2 ^ ℓ ∧
      |s.mem (s.nreg b)| < 2 ^ ℓ ∧ |o.eval (s.mem (s.nreg a)) (s.mem (s.nreg b))| < 2 ^ ℓ
  | .nconst dst c => dst + 4 < 2 ^ ℓa ∧ c < 2 ^ ℓa
  | .nadd dst a b => dst + 4 < 2 ^ ℓa ∧ RegOK ℓa s a ∧ RegOK ℓa s b
  | .nsub dst a b => dst + 4 < 2 ^ ℓa ∧ RegOK ℓa s a ∧ RegOK ℓa s b ∧ s.nreg b ≤ s.nreg a
  | .ncast dst a => RegOK ℓa s dst ∧ RegOK ℓa s a
  | _ => False

/-- The test of `ifR`, `whileR` within the bounds. -/
def TestR (ℓa ℓ : ℕ) (s : RealRAM.State d) (a b : ℕ) : Prop :=
  RegOK ℓa s a ∧ RegOK ℓa s b ∧ |s.mem (s.nreg a)| < 2 ^ ℓ ∧ |s.mem (s.nreg b)| < 2 ^ ℓ

/-- The test of `ifN`, `whileN` within the bounds. -/
def TestN (ℓa : ℕ) (s : RealRAM.State d) (a b : ℕ) : Prop := RegOK ℓa s a ∧ RegOK ℓa s b

/-- `Exec` on the integer fragment within the bounds `ℓa`, `ℓ`: the same rules, each primitive and test carrying its
bound. -/
inductive ExecB (ℓa ℓ : ℕ) (w : RealRAM.World d) : Cmd → RealRAM.State d → ℕ → RealRAM.State d → Prop
  | skip (s : RealRAM.State d) : ExecB ℓa ℓ w .skip s 0 s
  | prim (p : Prim) (s : RealRAM.State d) : PrimOK ℓa ℓ s p → ExecB ℓa ℓ w (.prim p) s 1 (p.exec w s)
  | seq {c₁ c₂ : Cmd} {s s₁ s₂ : RealRAM.State d} {k₁ k₂ : ℕ} :
      ExecB ℓa ℓ w c₁ s k₁ s₁ → ExecB ℓa ℓ w c₂ s₁ k₂ s₂ → ExecB ℓa ℓ w (.seq c₁ c₂) s (k₁ + k₂) s₂
  | ifR_t {a b : ℕ} {c₁ c₂ : Cmd} {s s' : RealRAM.State d} {k : ℕ} :
      TestR ℓa ℓ s a b → condR s a b → ExecB ℓa ℓ w c₁ s k s' → ExecB ℓa ℓ w (.ifR a b c₁ c₂) s (k + 1) s'
  | ifR_f {a b : ℕ} {c₁ c₂ : Cmd} {s s' : RealRAM.State d} {k : ℕ} :
      TestR ℓa ℓ s a b → ¬ condR s a b → ExecB ℓa ℓ w c₂ s k s' → ExecB ℓa ℓ w (.ifR a b c₁ c₂) s (k + 2) s'
  | ifN_t {a b : ℕ} {c₁ c₂ : Cmd} {s s' : RealRAM.State d} {k : ℕ} :
      TestN ℓa s a b → condN s a b → ExecB ℓa ℓ w c₁ s k s' → ExecB ℓa ℓ w (.ifN a b c₁ c₂) s (k + 1) s'
  | ifN_f {a b : ℕ} {c₁ c₂ : Cmd} {s s' : RealRAM.State d} {k : ℕ} :
      TestN ℓa s a b → ¬ condN s a b → ExecB ℓa ℓ w c₂ s k s' → ExecB ℓa ℓ w (.ifN a b c₁ c₂) s (k + 2) s'
  | whileR_t {a b : ℕ} {c : Cmd} {s s₁ s₂ : RealRAM.State d} {k k' : ℕ} :
      TestR ℓa ℓ s a b → condR s a b → ExecB ℓa ℓ w c s k s₁ → ExecB ℓa ℓ w (.whileR a b c) s₁ k' s₂ →
        ExecB ℓa ℓ w (.whileR a b c) s (k + 2 + k') s₂
  | whileR_f {a b : ℕ} {c : Cmd} {s : RealRAM.State d} :
      TestR ℓa ℓ s a b → ¬ condR s a b → ExecB ℓa ℓ w (.whileR a b c) s 2 s
  | whileN_t {a b : ℕ} {c : Cmd} {s s₁ s₂ : RealRAM.State d} {k k' : ℕ} :
      TestN ℓa s a b → condN s a b → ExecB ℓa ℓ w c s k s₁ → ExecB ℓa ℓ w (.whileN a b c) s₁ k' s₂ →
        ExecB ℓa ℓ w (.whileN a b c) s (k + 2 + k') s₂
  | whileN_f {a b : ℕ} {c : Cmd} {s : RealRAM.State d} :
      TestN ℓa s a b → ¬ condN s a b → ExecB ℓa ℓ w (.whileN a b c) s 2 s

/-! ## Cells, lengths, values -/

@[simp] theorem rg_ne_T1 (i : ℕ) : rg i ≠ T1 := by unfold rg T1; omega
@[simp] theorem rg_ne_T2 (i : ℕ) : rg i ≠ T2 := by unfold rg T2; omega
@[simp] theorem nat_ne_T1 (j : ℕ) : (j : ℤ) ≠ T1 := by unfold T1; omega
@[simp] theorem nat_ne_T2 (j : ℕ) : (j : ℤ) ≠ T2 := by unfold T2; omega
@[simp] theorem T2_ne_T1 : T2 ≠ T1 := by unfold T1 T2; omega
@[simp] theorem T1_ne_T2 : T1 ≠ T2 := by unfold T1 T2; omega
@[simp] theorem rg_inj (i j : ℕ) : rg i = rg j ↔ i = j := by unfold rg; omega

theorem len_T1 : BitRAM.len T1 = 1 := rfl
theorem len_T2 : BitRAM.len T2 = 2 := rfl

theorem len_rg {ℓa i : ℕ} (h : i + 4 < 2 ^ ℓa) : BitRAM.len (rg i) ≤ ℓa := size_rg i ℓa h

theorem len_nat {ℓa n : ℕ} (h : n < 2 ^ ℓa) : BitRAM.len (n : ℤ) ≤ ℓa := size_natCast_le n ℓa h

theorem len_val {ℓ : ℕ} {z : ℤ} {x : ℝ} (hz : (z : ℝ) = x) (h : |x| < 2 ^ ℓ) : BitRAM.len z ≤ ℓ :=
  size_le_of_abs_lt z ℓ (hz ▸ h)

/-- The cost of the arithmetic instruction on operands of lengths `u`, `v`. -/
def opC : RealRAM.Op2 → ℕ → ℕ → ℕ
  | .mul, u, v => (u + 1) * (v + 1)
  | .div, u, v => (u + 1) * (v + 1)
  | _, u, v => u + v

theorem opC_le (o : RealRAM.Op2) (u v : ℕ) : opC o u v ≤ (u + 1) * (v + 1) := by
  cases o <;> simp only [opC] <;> nlinarith

theorem opZ_cast (o : RealRAM.Op2) (ho : o ≠ .div) (x y : ℤ) : ((opZ o x y : ℤ) : ℝ) = o.eval x y := by
  cases o <;> simp [opZ, RealRAM.Op2.eval] at ho ⊢

/-! ## One instruction at a time -/

namespace B

open BitRAM Function

variable {P : List Instr} {w : World d} {t : State d} {q : ℕ}

/-- The fields of a state that the fragment never changes. -/
def Same (t t' : State d) : Prop := t'.coins = t.coins ∧ t'.rounds = t.rounds ∧ t'.pts = t.pts

theorem Same.refl (t : State d) : Same t t := ⟨rfl, rfl, rfl⟩

theorem Same.trans {t t' t'' : State d} (h : Same t t') (h' : Same t' t'') : Same t t'' :=
  ⟨h'.1.trans h.1, h'.2.1.trans h.2.1, h'.2.2.trans h.2.2⟩

theorem const_spec {dst c : ℤ} (h : P[q]? = some (.const dst c)) (hpc : t.pc = q) :
    ∃ t', step P w t = t' ∧ t'.pc = q + 1 ∧ t'.mem = update t.mem dst c ∧
      t'.cost = t.cost + (1 + len dst + len c) ∧ Same t t' :=
  ⟨_, step_const (hpc ▸ h), by simp [hpc], rfl, rfl, Same.refl t⟩

theorem add_spec {dst a b : ℤ} (h : P[q]? = some (.add dst a b)) (hpc : t.pc = q) :
    ∃ t', step P w t = t' ∧ t'.pc = q + 1 ∧ t'.mem = update t.mem dst (t.mem a + t.mem b) ∧
      t'.cost = t.cost + (1 + len dst + len a + len b + len (t.mem a) + len (t.mem b)) ∧ Same t t' :=
  ⟨_, step_add (hpc ▸ h), by simp [hpc], rfl, rfl, Same.refl t⟩

theorem sub_spec {dst a b : ℤ} (h : P[q]? = some (.sub dst a b)) (hpc : t.pc = q) :
    ∃ t', step P w t = t' ∧ t'.pc = q + 1 ∧ t'.mem = update t.mem dst (t.mem a - t.mem b) ∧
      t'.cost = t.cost + (1 + len dst + len a + len b + len (t.mem a) + len (t.mem b)) ∧ Same t t' :=
  ⟨_, step_sub (hpc ▸ h), by simp [hpc], rfl, rfl, Same.refl t⟩

theorem load_spec {dst src : ℤ} (h : P[q]? = some (.load dst src)) (hpc : t.pc = q) :
    ∃ t', step P w t = t' ∧ t'.pc = q + 1 ∧ t'.mem = update t.mem dst (t.mem (t.mem src)) ∧
      t'.cost = t.cost + (1 + len dst + len src + len (t.mem src) + len (t.mem (t.mem src))) ∧ Same t t' :=
  ⟨_, step_load (hpc ▸ h), by simp [hpc], rfl, rfl, Same.refl t⟩

theorem store_spec {dst src : ℤ} (h : P[q]? = some (.store dst src)) (hpc : t.pc = q) :
    ∃ t', step P w t = t' ∧ t'.pc = q + 1 ∧ t'.mem = update t.mem (t.mem dst) (t.mem src) ∧
      t'.cost = t.cost + (1 + len dst + len src + len (t.mem dst) + len (t.mem src)) ∧ Same t t' :=
  ⟨_, step_store (hpc ▸ h), by simp [hpc], rfl, rfl, Same.refl t⟩

theorem jlt_spec {a b : ℤ} {tg : ℕ} (h : P[q]? = some (.jlt a b tg)) (hpc : t.pc = q) :
    ∃ t', step P w t = t' ∧ t'.pc = (if t.mem a < t.mem b then tg else q + 1) ∧ t'.mem = t.mem ∧
      t'.cost = t.cost + (1 + len a + len b + len (t.mem a) + len (t.mem b)) ∧ Same t t' :=
  ⟨_, step_jlt (hpc ▸ h), by simp [hpc], rfl, rfl, Same.refl t⟩

theorem jmp_spec {tg : ℕ} (h : P[q]? = some (.jmp tg)) (hpc : t.pc = q) :
    ∃ t', step P w t = t' ∧ t'.pc = tg ∧ t'.mem = t.mem ∧ t'.cost = t.cost + 1 ∧ Same t t' :=
  ⟨_, step_jmp (hpc ▸ h), rfl, rfl, rfl, Same.refl t⟩

end B

section Prims

open Function

variable {P : List BitRAM.Instr} {wb : BitRAM.World d} {w : RealRAM.World d} {ℓa ℓ : ℕ}

/-! ## Tests and jumps -/

/-- The cost of the test of `ifN`, `whileN`. -/
def testNCost (ℓa : ℕ) : ℕ := 1 + 4 * ℓa

end Prims

theorem B.CodeAt.cast {P : List BitRAM.Instr} {o o' : ℕ} {l : List BitRAM.Instr} (h : B.CodeAt P o l) (e : o = o') :
    B.CodeAt P o' l := e ▸ h

/-! ## Code at an address -/

section Transfer

variable {P : List BitRAM.Instr} {wb : BitRAM.World d}

theorem B.CodeAt.head_at {o o' : ℕ} {x : BitRAM.Instr} {l : List BitRAM.Instr} (h : B.CodeAt P o (x :: l))
    (e : o = o') : P[o']? = some x := e ▸ h.cons_head

end Transfer

end AdversarialBco.Bit.Transfer
