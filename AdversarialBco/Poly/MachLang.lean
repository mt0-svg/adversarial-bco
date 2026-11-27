/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.StatementPoly

@[expose] public section

/-!
# A structured command language for the frozen real RAM

A small structured language over the instructions of the frozen machine (`AdversarialBco/StatementPoly.lean`):
sequence, conditionals and loops in place of program counters.

* `Prim`: the instructions with no jump; `Prim.exec` is their effect on a state, the program counter unchanged.
* `Cmd`: `skip`, a primitive, the sequence, the two conditionals (`ifR` on `M (N a) < M (N b)`, `ifN` on
  `N a < N b`) and the two loops (`whileR`, `whileN`, same tests).
* `Exec w c s k s'`: from the state `s`, `c` terminates in the state `s'` after exactly `k` machine steps (a jump
  counts as a step). The program counter is not read: `Exec` relates states up to it.
-/

namespace AdversarialBco.Poly.Mach

open AdversarialBco AdversarialBco.RealRAM

variable {d : ℕ}

/-- The instructions with no jump. -/
inductive Prim
  | rconst (dst : ℕ) (q : ℚ)
  | op2 (o : Op2) (dst a b : ℕ)
  | op1 (o : Op1) (dst a : ℕ)
  | nconst (dst c : ℕ)
  | nadd (dst a b : ℕ)
  | nsub (dst a b : ℕ)
  | ncast (dst a : ℕ)
  | spec (s : Spec) (dst src a b : ℕ)
  | query (dst src : ℕ)
  | gauss (dst : ℕ)
  | play (dst src : ℕ)

/-- The instruction of a primitive. -/
def Prim.toInstr : Prim → Instr
  | .rconst dst q => .rconst dst q
  | .op2 o dst a b => .op2 o dst a b
  | .op1 o dst a => .op1 o dst a
  | .nconst dst c => .nconst dst c
  | .nadd dst a b => .nadd dst a b
  | .nsub dst a b => .nsub dst a b
  | .ncast dst a => .ncast dst a
  | .spec s dst src a b => .spec s dst src a b
  | .query dst src => .query dst src
  | .gauss dst => .gauss dst
  | .play dst src => .play dst src

open Classical in
/-- The effect of a primitive, the program counter unchanged (as in `step`). -/
noncomputable def Prim.exec (w : World d) (s : State d) : Prim → State d
  | .rconst dst q => { s with mem := Function.update s.mem (s.nreg dst) q }
  | .op2 o dst a b => { s with mem := Function.update s.mem (s.nreg dst) (o.eval (s.mem (s.nreg a)) (s.mem (s.nreg b))) }
  | .op1 o dst a => { s with mem := Function.update s.mem (s.nreg dst) (o.eval (s.mem (s.nreg a))) }
  | .nconst dst c => { s with nreg := Function.update s.nreg dst c }
  | .nadd dst a b => { s with nreg := Function.update s.nreg dst (s.nreg a + s.nreg b) }
  | .nsub dst a b => { s with nreg := Function.update s.nreg dst (s.nreg a - s.nreg b) }
  | .ncast dst a => { s with mem := Function.update s.mem (s.nreg dst) (s.nreg a : ℝ) }
  | .spec sp dst src a b =>
    { s with
      mem := writeMat s.mem (s.nreg dst)
        (cfc (sp.fn (s.mem (s.nreg a)) (s.mem (s.nreg b))) (symPart (matAt d s.mem (s.nreg src)))) }
  | .query dst src =>
    { s with mem := Function.update s.mem (s.nreg dst) (if vecAt s.mem (s.nreg src) ∈ w.K then 1 else 0) }
  | .gauss dst => { s with mem := Function.update s.mem (s.nreg dst) (w.gs s.draws), draws := s.draws + 1 }
  | .play dst src =>
    { s with mem := Function.update s.mem (s.nreg dst) (w.f s.rounds (vecAt s.mem (s.nreg src)) + w.noise s.rounds),
             rounds := s.rounds + 1,
             pts := Function.update s.pts s.rounds (vecAt s.mem (s.nreg src)) }

/-- A state with its program counter set. -/
def atPc (s : State d) (q : ℕ) : State d := { s with pc := q }

/-- A primitive does not read the program counter. -/
theorem Prim.exec_setPc (w : World d) (s : State d) (p : Prim) (q : ℕ) :
    p.exec w (atPc s q) = atPc (p.exec w s) q := by
  cases p <;> rfl

/-- One step of the machine on a primitive. -/
theorem step_prim (P : List Instr) (w : World d) (s : State d) (p : Prim) (h : P[s.pc]? = some p.toInstr) :
    step P w s = atPc (p.exec w s) (s.pc + 1) := by
  cases p <;> simp [step, h, Prim.toInstr, Prim.exec, atPc]

/-- Structured commands. -/
inductive Cmd
  | skip
  | prim (p : Prim)
  | seq (c₁ c₂ : Cmd)
  /-- `if M (N a) < M (N b) then c₁ else c₂`. -/
  | ifR (a b : ℕ) (c₁ c₂ : Cmd)
  /-- `if N a < N b then c₁ else c₂`. -/
  | ifN (a b : ℕ) (c₁ c₂ : Cmd)
  /-- `while M (N a) < M (N b) do c`. -/
  | whileR (a b : ℕ) (c : Cmd)
  /-- `while N a < N b do c`. -/
  | whileN (a b : ℕ) (c : Cmd)

/-- The length of the code of a command. -/
def Cmd.len : Cmd → ℕ
  | .skip => 0
  | .prim _ => 1
  | .seq c₁ c₂ => c₁.len + c₂.len
  | .ifR _ _ c₁ c₂ => c₁.len + c₂.len + 2
  | .ifN _ _ c₁ c₂ => c₁.len + c₂.len + 2
  | .whileR _ _ c => c.len + 3
  | .whileN _ _ c => c.len + 3

/-- The code of a command placed at address `o`. A conditional is the test jumping to `c₁`, then `c₂`, `jmp end`, `c₁`;
a loop is the test jumping to the body, `jmp end`, the body, `jmp` back to the test. -/
def Cmd.compile : Cmd → ℕ → List Instr
  | .skip, _ => []
  | .prim p, _ => [p.toInstr]
  | .seq c₁ c₂, o => c₁.compile o ++ c₂.compile (o + c₁.len)
  | .ifR a b c₁ c₂, o =>
    .rjlt a b (o + c₂.len + 2) :: (c₂.compile (o + 1) ++ .jmp (o + c₂.len + 2 + c₁.len) :: c₁.compile (o + c₂.len + 2))
  | .ifN a b c₁ c₂, o =>
    .njlt a b (o + c₂.len + 2) :: (c₂.compile (o + 1) ++ .jmp (o + c₂.len + 2 + c₁.len) :: c₁.compile (o + c₂.len + 2))
  | .whileR a b c, o => .rjlt a b (o + 2) :: .jmp (o + c.len + 3) :: (c.compile (o + 2) ++ [.jmp o])
  | .whileN a b c, o => .njlt a b (o + 2) :: .jmp (o + c.len + 3) :: (c.compile (o + 2) ++ [.jmp o])

@[simp] theorem Cmd.length_compile (c : Cmd) (o : ℕ) : (c.compile o).length = c.len := by
  induction c generalizing o <;> simp [Cmd.compile, Cmd.len, *] <;> omega

/-- The test of `ifR` and `whileR`. -/
abbrev condR (s : State d) (a b : ℕ) : Prop := s.mem (s.nreg a) < s.mem (s.nreg b)

/-- The test of `ifN` and `whileN`. -/
abbrev condN (s : State d) (a b : ℕ) : Prop := s.nreg a < s.nreg b

/-- Big-step semantics with the exact number of machine steps. -/
inductive Exec (w : World d) : Cmd → State d → ℕ → State d → Prop
  | skip (s : State d) : Exec w .skip s 0 s
  | prim (p : Prim) (s : State d) : Exec w (.prim p) s 1 (p.exec w s)
  | seq {c₁ c₂ : Cmd} {s s₁ s₂ : State d} {k₁ k₂ : ℕ} :
      Exec w c₁ s k₁ s₁ → Exec w c₂ s₁ k₂ s₂ → Exec w (.seq c₁ c₂) s (k₁ + k₂) s₂
  | ifR_t {a b : ℕ} {c₁ c₂ : Cmd} {s s' : State d} {k : ℕ} :
      condR s a b → Exec w c₁ s k s' → Exec w (.ifR a b c₁ c₂) s (k + 1) s'
  | ifR_f {a b : ℕ} {c₁ c₂ : Cmd} {s s' : State d} {k : ℕ} :
      ¬ condR s a b → Exec w c₂ s k s' → Exec w (.ifR a b c₁ c₂) s (k + 2) s'
  | ifN_t {a b : ℕ} {c₁ c₂ : Cmd} {s s' : State d} {k : ℕ} :
      condN s a b → Exec w c₁ s k s' → Exec w (.ifN a b c₁ c₂) s (k + 1) s'
  | ifN_f {a b : ℕ} {c₁ c₂ : Cmd} {s s' : State d} {k : ℕ} :
      ¬ condN s a b → Exec w c₂ s k s' → Exec w (.ifN a b c₁ c₂) s (k + 2) s'
  | whileR_t {a b : ℕ} {c : Cmd} {s s₁ s₂ : State d} {k k' : ℕ} :
      condR s a b → Exec w c s k s₁ → Exec w (.whileR a b c) s₁ k' s₂ → Exec w (.whileR a b c) s (k + 2 + k') s₂
  | whileR_f {a b : ℕ} {c : Cmd} {s : State d} : ¬ condR s a b → Exec w (.whileR a b c) s 2 s
  | whileN_t {a b : ℕ} {c : Cmd} {s s₁ s₂ : State d} {k k' : ℕ} :
      condN s a b → Exec w c s k s₁ → Exec w (.whileN a b c) s₁ k' s₂ → Exec w (.whileN a b c) s (k + 2 + k') s₂
  | whileN_f {a b : ℕ} {c : Cmd} {s : State d} : ¬ condN s a b → Exec w (.whileN a b c) s 2 s

/-! ## Simulation -/

/-- `k` steps then `j` steps. -/
theorem run_add (P : List Instr) (w : World d) (s : State d) (k j : ℕ) :
    run P w s (k + j) = run P w (run P w s k) j := by
  simp only [run]; rw [add_comm, Function.iterate_add_apply]

theorem run_one (P : List Instr) (w : World d) (s : State d) : run P w s 1 = step P w s := rfl

/-- The code of `c` sits at address `o` of `P`. -/
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

@[simp] theorem atPc_atPc (s : State d) (q q' : ℕ) : atPc (atPc s q) q' = atPc s q' := rfl

@[simp] theorem atPc_pc (s : State d) (q : ℕ) : (atPc s q).pc = q := rfl

@[simp] theorem atPc_rounds (s : State d) (q : ℕ) : (atPc s q).rounds = s.rounds := rfl
@[simp] theorem atPc_pts (s : State d) (q : ℕ) : (atPc s q).pts = s.pts := rfl

theorem step_jmp (P : List Instr) (w : World d) (s : State d) (t : ℕ) (h : P[s.pc]? = some (.jmp t)) :
    step P w s = atPc s t := by
  simp [step, h, atPc]

theorem step_rjlt (P : List Instr) (w : World d) (s : State d) (a b t : ℕ) (h : P[s.pc]? = some (.rjlt a b t)) :
    step P w s = if condR s a b then atPc s t else atPc s (s.pc + 1) := by
  simp [step, h, atPc]

theorem step_njlt (P : List Instr) (w : World d) (s : State d) (a b t : ℕ) (h : P[s.pc]? = some (.njlt a b t)) :
    step P w s = if condN s a b then atPc s t else atPc s (s.pc + 1) := by
  simp [step, h, atPc]

theorem step_rjlt_t (P : List Instr) (w : World d) (s : State d) (a b t : ℕ) (h : P[s.pc]? = some (.rjlt a b t))
    (hc : condR s a b) : step P w s = atPc s t := by
  rw [step_rjlt P w s a b t h]; simp [hc]

theorem step_rjlt_f (P : List Instr) (w : World d) (s : State d) (a b t : ℕ) (h : P[s.pc]? = some (.rjlt a b t))
    (hc : ¬ condR s a b) : step P w s = atPc s (s.pc + 1) := by
  rw [step_rjlt P w s a b t h]; simp [hc]

theorem step_njlt_t (P : List Instr) (w : World d) (s : State d) (a b t : ℕ) (h : P[s.pc]? = some (.njlt a b t))
    (hc : condN s a b) : step P w s = atPc s t := by
  rw [step_njlt P w s a b t h]; simp [hc]

theorem step_njlt_f (P : List Instr) (w : World d) (s : State d) (a b t : ℕ) (h : P[s.pc]? = some (.njlt a b t))
    (hc : ¬ condN s a b) : step P w s = atPc s (s.pc + 1) := by
  rw [step_njlt P w s a b t h]; simp [hc]

/-- The simulation theorem: the compiled code runs the command in exactly the counted number of steps. -/
theorem exec_sim {P : List Instr} {w : World d} {c : Cmd} {s s' : State d} {k : ℕ} (h : Exec w c s k s') :
    ∀ o, CodeAt P o (c.compile o) → run P w (atPc s o) k = atPc s' (o + c.len) := by
  induction h with
  | skip s => intro o _; rfl
  | prim p s =>
    intro o hc
    have h0 : P[(atPc s o).pc]? = some p.toInstr := hc.cons_head
    rw [run_one, step_prim P w _ p h0, Prim.exec_setPc]
    rfl
  | @seq c₁ c₂ s s₁ s₂ k₁ k₂ _ _ ih₁ ih₂ =>
    intro o hc
    simp only [Cmd.compile] at hc
    rw [run_add, ih₁ o hc.append_left]
    have := ih₂ (o + c₁.len) (by simpa using hc.append_right)
    rw [this]; simp [Cmd.len, Nat.add_assoc]
  | @ifR_t a b c₁ c₂ s s' k hcond _ ih =>
    intro o hc
    simp only [Cmd.compile] at hc
    rw [add_comm, run_add, run_one, step_rjlt_t P w (atPc s o) a b _ hc.cons_head hcond]
    have hc' := hc.cons_tail
    have h2 : CodeAt P (o + 1 + (c₂.compile (o + 1)).length + 1) (c₁.compile (o + c₂.len + 2)) :=
      (hc'.append_right).cons_tail
    simp only [Cmd.length_compile] at h2
    rw [show o + 1 + c₂.len + 1 = o + c₂.len + 2 by omega] at h2
    rw [atPc_atPc, ih _ h2]; congr 1; simp [Cmd.len]; omega
  | @ifR_f a b c₁ c₂ s s' k hcond _ ih =>
    intro o hc
    simp only [Cmd.compile] at hc
    rw [show k + 2 = 1 + (k + 1) by omega, run_add, run_one, step_rjlt_f P w (atPc s o) a b _ hc.cons_head hcond, run_add]
    have hc' := hc.cons_tail
    rw [atPc_pc, atPc_atPc, ih _ hc'.append_left, run_one]
    have hj := (hc'.append_right).cons_head
    simp only [Cmd.length_compile] at hj
    rw [step_jmp P w _ _ (by simpa using hj)]
    rw [atPc_atPc]; congr 1; simp [Cmd.len]; omega
  | @ifN_t a b c₁ c₂ s s' k hcond _ ih =>
    intro o hc
    simp only [Cmd.compile] at hc
    rw [add_comm, run_add, run_one, step_njlt_t P w (atPc s o) a b _ hc.cons_head hcond]
    have hc' := hc.cons_tail
    have h2 : CodeAt P (o + 1 + (c₂.compile (o + 1)).length + 1) (c₁.compile (o + c₂.len + 2)) :=
      (hc'.append_right).cons_tail
    simp only [Cmd.length_compile] at h2
    rw [show o + 1 + c₂.len + 1 = o + c₂.len + 2 by omega] at h2
    rw [atPc_atPc, ih _ h2]; congr 1; simp [Cmd.len]; omega
  | @ifN_f a b c₁ c₂ s s' k hcond _ ih =>
    intro o hc
    simp only [Cmd.compile] at hc
    rw [show k + 2 = 1 + (k + 1) by omega, run_add, run_one, step_njlt_f P w (atPc s o) a b _ hc.cons_head hcond, run_add]
    have hc' := hc.cons_tail
    rw [atPc_pc, atPc_atPc, ih _ hc'.append_left, run_one]
    have hj := (hc'.append_right).cons_head
    simp only [Cmd.length_compile] at hj
    rw [step_jmp P w _ _ (by simpa using hj)]
    rw [atPc_atPc]; congr 1; simp [Cmd.len]; omega
  | @whileR_t a b c s s₁ s₂ k k' hcond _ _ ih₁ ih₂ =>
    intro o hc
    have hc0 := hc
    simp only [Cmd.compile] at hc
    rw [show k + 2 + k' = 1 + (k + (1 + k')) by omega, run_add, run_one, step_rjlt_t P w (atPc s o) a b _ hc.cons_head hcond,
      run_add, atPc_atPc]
    have hb := hc.cons_tail.cons_tail
    rw [show o + 1 + 1 = o + 2 by omega] at hb
    rw [ih₁ _ hb.append_left, run_add, run_one]
    have hj := hb.append_right.cons_head
    simp only [Cmd.length_compile] at hj
    rw [step_jmp P w _ _ (by simpa using hj), atPc_atPc, ih₂ o hc0]
  | @whileR_f a b c s hcond =>
    intro o hc
    simp only [Cmd.compile] at hc
    rw [show (2 : ℕ) = 1 + 1 by rfl, run_add, run_one, run_one,
      step_rjlt_f P w (atPc s o) a b _ hc.cons_head hcond, step_jmp P w _ _ (by simpa using hc.cons_tail.cons_head)]
    simp [Cmd.len, Nat.add_assoc]
  | @whileN_t a b c s s₁ s₂ k k' hcond _ _ ih₁ ih₂ =>
    intro o hc
    have hc0 := hc
    simp only [Cmd.compile] at hc
    rw [show k + 2 + k' = 1 + (k + (1 + k')) by omega, run_add, run_one, step_njlt_t P w (atPc s o) a b _ hc.cons_head hcond,
      run_add, atPc_atPc]
    have hb := hc.cons_tail.cons_tail
    rw [show o + 1 + 1 = o + 2 by omega] at hb
    rw [ih₁ _ hb.append_left, run_add, run_one]
    have hj := hb.append_right.cons_head
    simp only [Cmd.length_compile] at hj
    rw [step_jmp P w _ _ (by simpa using hj), atPc_atPc, ih₂ o hc0]
  | @whileN_f a b c s hcond =>
    intro o hc
    simp only [Cmd.compile] at hc
    rw [show (2 : ℕ) = 1 + 1 by rfl, run_add, run_one, run_one,
      step_njlt_f P w (atPc s o) a b _ hc.cons_head hcond, step_jmp P w _ _ (by simpa using hc.cons_tail.cons_head)]
    simp [Cmd.len, Nat.add_assoc]

/-! ## Rounds, points played, the cost clause -/

theorem step_rounds (P : List Instr) (w : World d) (s : State d) :
    s.rounds ≤ (step P w s).rounds ∧ (step P w s).rounds ≤ s.rounds + 1 := by
  unfold step
  rcases P[s.pc]? with _ | ins
  · simp
  · cases ins <;> simp <;> split_ifs <;> simp

/-- A step keeps the points of the rounds already played. -/
theorem step_pts (P : List Instr) (w : World d) (s : State d) (t : ℕ) (ht : t < s.rounds) :
    (step P w s).pts t = s.pts t := by
  unfold step
  rcases P[s.pc]? with _ | ins
  · simp
  · cases ins <;> simp <;> (try split_ifs) <;> simp [Function.update_of_ne ht.ne]

theorem run_rounds_mono (P : List Instr) (w : World d) (s : State d) {k k' : ℕ} (h : k ≤ k') :
    (run P w s k).rounds ≤ (run P w s k').rounds := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [← Nat.add_assoc, run_add _ _ _ (k + j) 1, run_one]
    exact (ih (by omega)).trans (step_rounds P w _).1

theorem run_pts_stable (P : List Instr) (w : World d) (s : State d) {k k' : ℕ} (h : k ≤ k') (t : ℕ)
    (ht : t < (run P w s k).rounds) : (run P w s k').pts t = (run P w s k).pts t := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [← Nat.add_assoc, run_add _ _ _ (k + j) 1, run_one,
      step_pts P w _ t (ht.trans_le (run_rounds_mono P w s (by omega))), ih (by omega)]

/-- The point played in round `t`, read off any step after that round. -/
theorem played_eq (P : List Instr) (w : World d) (s : State d) (k t : ℕ) (ht : t < (run P w s k).rounds) :
    played P w s t = (run P w s k).pts t := by
  have h : ∃ k, t < (run P w s k).rounds := ⟨k, ht⟩
  rw [played, dite_eq_left_of_eq_true (eq_true h)]
  rcases le_total (Nat.find h) k with hk | hk
  · exact (run_pts_stable P w s hk t (Nat.find_spec h)).symm
  · exact run_pts_stable P w s hk t ht

/-! ## Loops with explicit states -/

/-- `Exec` with the cost rewritten. -/
theorem Exec.cost {w : World d} {c : Cmd} {s s' : State d} {k k' : ℕ} (h : Exec w c s k s') (hk : k = k') :
    Exec w c s k' s' := hk ▸ h

/-! ## Runs through the turns of a loop -/

theorem CodeAt.whileN_body {P : List Instr} {o a b : ℕ} {c : Cmd} (h : CodeAt P o ((Cmd.whileN a b c).compile o)) :
    CodeAt P (o + 2) (c.compile (o + 2)) := by
  simp only [Cmd.compile] at h
  simpa [Nat.add_assoc] using h.cons_tail.cons_tail.append_left

/-- Entering the body of a `whileN` loop. -/
theorem run_whileN_enter {P : List Instr} {w : World d} {o a b : ℕ} {c : Cmd}
    (h : CodeAt P o ((Cmd.whileN a b c).compile o)) {s : State d} (hcond : condN s a b) :
    run P w (atPc s o) 1 = atPc s (o + 2) := by
  simp only [Cmd.compile] at h
  rw [run_one, step_njlt_t P w (atPc s o) a b _ h.cons_head hcond, atPc_atPc]

/-- One turn of a `whileN` loop, from the test back to the test. -/
theorem run_whileN_turn {P : List Instr} {w : World d} {o a b : ℕ} {c : Cmd}
    (h : CodeAt P o ((Cmd.whileN a b c).compile o)) {s s' : State d} {k : ℕ} (hcond : condN s a b)
    (hb : Exec w c s k s') : run P w (atPc s o) (1 + (k + 1)) = atPc s' o := by
  have h0 := h
  simp only [Cmd.compile] at h
  rw [run_add, run_whileN_enter h0 hcond, run_add, exec_sim hb _ h0.whileN_body, run_one]
  have hj := h.cons_tail.cons_tail.append_right.cons_head
  simp only [Cmd.length_compile] at hj
  rw [step_jmp P w _ _ (by simpa [Nat.add_assoc] using hj), atPc_atPc]

/-! ## The code of the parts of a command -/

theorem CodeAt.seq_left {P : List Instr} {o : ℕ} {c₁ c₂ : Cmd} (h : CodeAt P o ((Cmd.seq c₁ c₂).compile o)) :
    CodeAt P o (c₁.compile o) := by
  simp only [Cmd.compile] at h
  exact h.append_left

theorem CodeAt.seq_right {P : List Instr} {o : ℕ} {c₁ c₂ : Cmd} (h : CodeAt P o ((Cmd.seq c₁ c₂).compile o)) :
    CodeAt P (o + c₁.len) (c₂.compile (o + c₁.len)) := by
  simp only [Cmd.compile] at h
  simpa using h.append_right

end AdversarialBco.Poly.Mach
