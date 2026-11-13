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

end AdversarialBco.Poly.Mach
