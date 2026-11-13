/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.Trans

@[expose] public section

/-!
# The compiler, part 1: the fragment with leaves, and its bounded semantics on the real state

The integer fragment of `Cmd` (Trans.lean) lacks the operations of the bit machine that have no counterpart on the
real machine, and the input of the bit statement. They are added here as leaves (the paper's sections
on the program and on the code):

* `idiv dst a b`: `M (N dst) := M (N a) / M (N b)`, the Euclidean quotient of the integers in the two cells;
* `coins dst cnt`: `M (N dst) :=` the integer read from the next `N cnt` coins (the instruction `coins`);
* `obs dst prec`: `M (N dst) := ⌊2^(N prec) o⌋`, `o` the feedback of the last round played (the instruction `obs`);
* `play src`: play the point `(M (N src + 1 + i) / M (N src))_{i < d}` (the instruction `play`);
* `rtoN dst a`: `N dst := M (N a)`, a nonnegative integer of a cell moved to a natural register;
* `nmul dst a b`: `N dst := N a * N b`;
* `rdIn dst e`: `M (N dst) :=` the cell `N e` of the input.

`XCmd` has the control of `Cmd` over the fragment primitives and the leaves; `toX` embeds `Cmd`. `XExecB X ℓa ℓ` is
the bounded big-step semantics on real states (`ExecB` with the leaves), in the context `X` (the bit world, the input
cells and the offset of the real cells, `XCtx`). The real state counts the coins used in `draws`; the points played
are those of the bit machine read in `E d`.
-/

namespace AdversarialBco.Bit.Transfer

open AdversarialBco
open AdversarialBco.Poly.Mach (Prim Cmd condR condN)

variable {d : ℕ}

/-- The leaves: operations of the bit machine outside the integer fragment of the real machine. -/
inductive Leaf
  /-- `M (N dst) := M (N a) / M (N b)`, the Euclidean quotient. -/
  | idiv (dst a b : ℕ)
  /-- `M (N dst) :=` the integer whose binary digits are the next `N cnt` coins. -/
  | coins (dst cnt : ℕ)
  /-- `M (N dst) := ⌊2^(N prec) o⌋`, `o` the feedback of the last round played. -/
  | obs (dst prec : ℕ)
  /-- Play the point `(M (N src + 1 + i) / M (N src))_{i < d}`. -/
  | play (src : ℕ)
  /-- `N dst := M (N a)` for a nonnegative integer `M (N a)`. -/
  | rtoN (dst a : ℕ)
  /-- `N dst := N a * N b`. -/
  | nmul (dst a b : ℕ)
  /-- `M (N dst) :=` the input cell `N e`. -/
  | rdIn (dst e : ℕ)

/-- A primitive: one of the real machine (the fragment) or a leaf. -/
inductive XPrim
  | frag (p : Prim)
  | leaf (l : Leaf)

/-- Structured commands over the fragment primitives and the leaves, with the control of `Cmd`. -/
inductive XCmd
  | skip
  | prim (p : XPrim)
  | seq (c₁ c₂ : XCmd)
  /-- `if M (N a) < M (N b) then c₁ else c₂`. -/
  | ifR (a b : ℕ) (c₁ c₂ : XCmd)
  /-- `if N a < N b then c₁ else c₂`. -/
  | ifN (a b : ℕ) (c₁ c₂ : XCmd)
  /-- `while M (N a) < M (N b) do c`. -/
  | whileR (a b : ℕ) (c : XCmd)
  /-- `while N a < N b do c`. -/
  | whileN (a b : ℕ) (c : XCmd)

/-- A command of the real machine as an extended command. -/
def toX : Cmd → XCmd
  | .skip => .skip
  | .prim p => .prim (.frag p)
  | .seq c₁ c₂ => .seq (toX c₁) (toX c₂)
  | .ifR a b c₁ c₂ => .ifR a b (toX c₁) (toX c₂)
  | .ifN a b c₁ c₂ => .ifN a b (toX c₁) (toX c₂)
  | .whileR a b c => .whileR a b (toX c)
  | .whileN a b c => .whileN a b (toX c)

/-- The context of a run: the world of the bit machine (losses and coins), the input cells, and the offset `off` of
the real cells in the bit memory (the input occupies the bit cells `0, ..., off - 1`). -/
structure XCtx (d : ℕ) where
  wb : BitRAM.World d
  inp : ℕ → ℤ
  off : ℕ

/-- The real world in which the fragment primitives are run (they read no world). -/
noncomputable def XCtx.rw (X : XCtx d) : RealRAM.World d := ⟨∅, X.wb.f, fun _ => 0, fun _ => 0⟩

/-- The point with denominator in the cell `a` and numerators in the cells `a + 1, ..., a + d`. -/
noncomputable def ptR (d : ℕ) (m : ℕ → ℝ) (a : ℕ) : E d :=
  WithLp.toLp 2 fun i : Fin d => m (a + 1 + (i : ℕ)) / m a

/-- The feedback of the last round played, read on the real state (`0` before the first play). -/
noncomputable def fbR (X : XCtx d) (s : RealRAM.State d) : ℝ :=
  if s.rounds = 0 then 0 else X.wb.f (s.rounds - 1) (s.pts (s.rounds - 1))

/-- The effect of a leaf on the real state. -/
noncomputable def Leaf.exec (X : XCtx d) (s : RealRAM.State d) : Leaf → RealRAM.State d
  | .idiv dst a b =>
    { s with mem := Function.update s.mem (s.nreg dst) ((⌊s.mem (s.nreg a)⌋ / ⌊s.mem (s.nreg b)⌋ : ℤ) : ℝ) }
  | .coins dst cnt =>
    { s with mem := Function.update s.mem (s.nreg dst) (BitRAM.readCoins X.wb.cs s.draws (s.nreg cnt) : ℝ),
             draws := s.draws + s.nreg cnt }
  | .obs dst prec =>
    { s with mem := Function.update s.mem (s.nreg dst) (⌊(2 : ℝ) ^ (s.nreg prec) * fbR X s⌋ : ℝ) }
  | .play src =>
    { s with rounds := s.rounds + 1, pts := Function.update s.pts s.rounds (ptR d s.mem (s.nreg src)) }
  | .rtoN dst a => { s with nreg := Function.update s.nreg dst (⌊s.mem (s.nreg a)⌋).toNat }
  | .nmul dst a b => { s with nreg := Function.update s.nreg dst (s.nreg a * s.nreg b) }
  | .rdIn dst e => { s with mem := Function.update s.mem (s.nreg dst) (X.inp (s.nreg e) : ℝ) }

/-- A leaf within the bounds: registers within `ℓa` bits, the values read and written within `ℓ` bits, at most `ℓ`
coins or digits, the point of a play within the addresses of `ℓa` bits, the natural read by `rtoN` and the product of
`nmul` below `2 ^ ℓa`, the input cell read by `rdIn` inside the input. -/
def LeafOK (X : XCtx d) (ℓa ℓ : ℕ) (s : RealRAM.State d) : Leaf → Prop
  | .idiv dst a b => RegOK ℓa s dst ∧ RegOK ℓa s a ∧ RegOK ℓa s b ∧ |s.mem (s.nreg a)| < 2 ^ ℓ ∧
      |s.mem (s.nreg b)| < 2 ^ ℓ
  | .coins dst cnt => RegOK ℓa s dst ∧ RegOK ℓa s cnt ∧ s.nreg cnt ≤ ℓ
  | .obs dst prec => RegOK ℓa s dst ∧ RegOK ℓa s prec ∧ s.nreg prec ≤ ℓ ∧
      |((⌊(2 : ℝ) ^ (s.nreg prec) * fbR X s⌋ : ℤ) : ℝ)| < 2 ^ ℓ
  | .play src => RegOK ℓa s src ∧ s.nreg src + d < 2 ^ ℓa ∧ ∀ i ≤ d, |s.mem (s.nreg src + i)| < 2 ^ ℓ
  | .rtoN dst a => dst + 4 < 2 ^ ℓa ∧ RegOK ℓa s a ∧ 0 ≤ s.mem (s.nreg a) ∧ s.mem (s.nreg a) < 2 ^ ℓa ∧
      |s.mem (s.nreg a)| < 2 ^ ℓ
  | .nmul dst a b => dst + 4 < 2 ^ ℓa ∧ RegOK ℓa s a ∧ RegOK ℓa s b ∧ s.nreg a * s.nreg b < 2 ^ ℓa
  | .rdIn dst e => RegOK ℓa s dst ∧ RegOK ℓa s e ∧ s.nreg e < X.off ∧ |(X.inp (s.nreg e) : ℝ)| < 2 ^ ℓ

/-- The units of cost of a leaf: a play reads `d + 1` cells, the others are one unit. -/
def leafUnits (d : ℕ) : Leaf → ℕ
  | .play _ => d + 2
  | _ => 1

/-- `ExecB` with the leaves: the bounded big-step semantics of `XCmd` on real states, the count in units of cost (one
per primitive, test or jump of the real machine, `d + 2` per play). -/
inductive XExecB (X : XCtx d) (ℓa ℓ : ℕ) : XCmd → RealRAM.State d → ℕ → RealRAM.State d → Prop
  | skip (s : RealRAM.State d) : XExecB X ℓa ℓ .skip s 0 s
  | frag (p : Prim) (s : RealRAM.State d) : PrimOK ℓa ℓ s p → XExecB X ℓa ℓ (.prim (.frag p)) s 1 (p.exec X.rw s)
  | leaf (l : Leaf) (s : RealRAM.State d) : LeafOK X ℓa ℓ s l →
      XExecB X ℓa ℓ (.prim (.leaf l)) s (leafUnits d l) (l.exec X s)
  | seq {c₁ c₂ : XCmd} {s s₁ s₂ : RealRAM.State d} {k₁ k₂ : ℕ} :
      XExecB X ℓa ℓ c₁ s k₁ s₁ → XExecB X ℓa ℓ c₂ s₁ k₂ s₂ → XExecB X ℓa ℓ (.seq c₁ c₂) s (k₁ + k₂) s₂
  | ifR_t {a b : ℕ} {c₁ c₂ : XCmd} {s s' : RealRAM.State d} {k : ℕ} :
      TestR ℓa ℓ s a b → condR s a b → XExecB X ℓa ℓ c₁ s k s' → XExecB X ℓa ℓ (.ifR a b c₁ c₂) s (k + 1) s'
  | ifR_f {a b : ℕ} {c₁ c₂ : XCmd} {s s' : RealRAM.State d} {k : ℕ} :
      TestR ℓa ℓ s a b → ¬ condR s a b → XExecB X ℓa ℓ c₂ s k s' → XExecB X ℓa ℓ (.ifR a b c₁ c₂) s (k + 2) s'
  | ifN_t {a b : ℕ} {c₁ c₂ : XCmd} {s s' : RealRAM.State d} {k : ℕ} :
      TestN ℓa s a b → condN s a b → XExecB X ℓa ℓ c₁ s k s' → XExecB X ℓa ℓ (.ifN a b c₁ c₂) s (k + 1) s'
  | ifN_f {a b : ℕ} {c₁ c₂ : XCmd} {s s' : RealRAM.State d} {k : ℕ} :
      TestN ℓa s a b → ¬ condN s a b → XExecB X ℓa ℓ c₂ s k s' → XExecB X ℓa ℓ (.ifN a b c₁ c₂) s (k + 2) s'
  | whileR_t {a b : ℕ} {c : XCmd} {s s₁ s₂ : RealRAM.State d} {k k' : ℕ} :
      TestR ℓa ℓ s a b → condR s a b → XExecB X ℓa ℓ c s k s₁ → XExecB X ℓa ℓ (.whileR a b c) s₁ k' s₂ →
        XExecB X ℓa ℓ (.whileR a b c) s (k + 2 + k') s₂
  | whileR_f {a b : ℕ} {c : XCmd} {s : RealRAM.State d} :
      TestR ℓa ℓ s a b → ¬ condR s a b → XExecB X ℓa ℓ (.whileR a b c) s 2 s
  | whileN_t {a b : ℕ} {c : XCmd} {s s₁ s₂ : RealRAM.State d} {k k' : ℕ} :
      TestN ℓa s a b → condN s a b → XExecB X ℓa ℓ c s k s₁ → XExecB X ℓa ℓ (.whileN a b c) s₁ k' s₂ →
        XExecB X ℓa ℓ (.whileN a b c) s (k + 2 + k') s₂
  | whileN_f {a b : ℕ} {c : XCmd} {s : RealRAM.State d} :
      TestN ℓa s a b → ¬ condN s a b → XExecB X ℓa ℓ (.whileN a b c) s 2 s

/-- A fragment primitive reads no world. -/
theorem prim_exec_world {ℓa ℓ : ℕ} {p : Prim} {s : RealRAM.State d} (hok : PrimOK ℓa ℓ s p)
    (w w' : RealRAM.World d) : p.exec w s = p.exec w' s := by
  cases p <;> first | rfl | exact hok.elim

/-- A bounded run of the fragment is a bounded run of the extended language, in every context. -/
theorem ExecB.toX {ℓa ℓ : ℕ} {w : RealRAM.World d} {c : Cmd} {s s' : RealRAM.State d} {k : ℕ}
    (h : ExecB ℓa ℓ w c s k s') (X : XCtx d) : XExecB X ℓa ℓ (toX c) s k s' := by
  induction h with
  | skip s => exact .skip s
  | prim p s hok => rw [prim_exec_world hok w X.rw]; exact .frag p s hok
  | seq _ _ ih₁ ih₂ => exact .seq ih₁ ih₂
  | ifR_t ht hc _ ih => exact .ifR_t ht hc ih
  | ifR_f ht hc _ ih => exact .ifR_f ht hc ih
  | ifN_t ht hc _ ih => exact .ifN_t ht hc ih
  | ifN_f ht hc _ ih => exact .ifN_f ht hc ih
  | whileR_t ht hc _ _ ih₁ ih₂ => exact .whileR_t ht hc ih₁ ih₂
  | whileR_f ht hc => exact .whileR_f ht hc
  | whileN_t ht hc _ _ ih₁ ih₂ => exact .whileN_t ht hc ih₁ ih₂
  | whileN_f ht hc => exact .whileN_f ht hc

end AdversarialBco.Bit.Transfer
