/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.MachVec

@[expose] public section

/-! # Straight-line scalar code

A list of scalar instructions (`SI`), its code `sprog`, and its value `sEval` on the scalars (a left fold of
`Function.update`): one rule `runs_sprog` for the whole list, and values read block by block through
`sEval_append` and `sEval_frame`, so that no proof unfolds the whole list at once. -/

namespace AdversarialBco.Poly.Mach.VL

open AdversarialBco AdversarialBco.RealRAM

variable {d : ℕ} {L : Layout} {w : World d}

/-- A straight-line scalar instruction. -/
inductive SI
  /-- `x := q`. -/
  | const (x : ℕ) (q : ℚ)
  /-- `x := a ∘ b`. -/
  | op2 (o : Op2) (x a b : ℕ)
  /-- `x := o a`. -/
  | op1 (o : Op1) (x a : ℕ)
  /-- `x :=` the natural `i`. -/
  | cast (x i : ℕ)
  /-- `z := min x y`. -/
  | smin (z x y : ℕ)
  /-- `z := max x y`. -/
  | smax (z x y : ℕ)

namespace SI

/-- The code of an instruction. -/
def cmd (L : Layout) : SI → Cmd
  | const x q => sconst L x q
  | op2 o x a b => sop2 L o x a b
  | op1 o x a => sop1 L o x a
  | cast x i => ncast L x i
  | smin z x y => VL.smin L z x y
  | smax z x y => VL.smax L z x y

/-- The cost of an instruction. -/
def cost : SI → ℕ
  | smin .. => 3
  | smax .. => 3
  | _ => 1

/-- The scalar written. -/
def dst : SI → ℕ
  | const x _ => x
  | op2 _ x _ _ => x
  | op1 _ x _ => x
  | cast x _ => x
  | smin z _ _ => z
  | smax z _ _ => z

/-- The value written, from the naturals `n` and the scalars `f`. -/
noncomputable def val (n : ℕ → ℕ) (f : ℕ → ℝ) : SI → ℝ
  | const _ q => q
  | op2 o _ a b => o.eval (f a) (f b)
  | op1 o _ a => o.eval (f a)
  | cast _ i => n i
  | smin _ x y => min (f x) (f y)
  | smax _ x y => max (f x) (f y)

/-- The registers of an instruction are in the layout. -/
def ok (L : Layout) : SI → Bool
  | const x _ => decide (x < L.NS)
  | op2 _ x a b => decide (x < L.NS ∧ a < L.NS ∧ b < L.NS)
  | op1 _ x a => decide (x < L.NS ∧ a < L.NS)
  | cast x i => decide (x < L.NS ∧ i < L.NN)
  | smin z x y => decide (z < L.NS ∧ x < L.NS ∧ y < L.NS)
  | smax z x y => decide (z < L.NS ∧ x < L.NS ∧ y < L.NS)

/-- The scalars after an instruction. -/
noncomputable def step (n : ℕ → ℕ) (f : ℕ → ℝ) (c : SI) : ℕ → ℝ := Function.update f c.dst (c.val n f)

theorem runs_cmd (c : SI) (hc : c.ok L = true) (σ : Env d) :
    Runs L w (c.cmd L) σ c.cost (· = { σ with sc := c.step σ.nat σ.sc }) := by
  cases c with
  | const x q => simp only [ok, decide_eq_true_eq] at hc; exact runs_sconst hc q
  | op2 o x a b =>
    simp only [ok, decide_eq_true_eq] at hc; exact runs_sop2 hc.1 hc.2.1 hc.2.2 o
  | op1 o x a => simp only [ok, decide_eq_true_eq] at hc; exact runs_sop1 hc.1 hc.2 o
  | cast x i => simp only [ok, decide_eq_true_eq] at hc; exact runs_ncast hc.1 hc.2
  | smin z x y => simp only [ok, decide_eq_true_eq] at hc; exact runs_smin hc.1 hc.2.1 hc.2.2
  | smax z x y => simp only [ok, decide_eq_true_eq] at hc; exact runs_smax hc.1 hc.2.1 hc.2.2

end SI

/-- The code of a list of scalar instructions. -/
def sprog (L : Layout) : List SI → Cmd
  | [] => .skip
  | c :: cs => .seq (c.cmd L) (sprog L cs)

/-- The scalars after a list of scalar instructions, from the naturals `n` and the scalars `f`. -/
noncomputable def sEval (n : ℕ → ℕ) (l : List SI) (f : ℕ → ℝ) : ℕ → ℝ := l.foldl (SI.step n) f

/-- The cost of a list of scalar instructions. -/
def sCost (l : List SI) : ℕ := (l.map SI.cost).sum

theorem runs_sprog (l : List SI) (hl : l.all (SI.ok L) = true) (σ : Env d) :
    Runs L w (sprog L l) σ (sCost l) (· = { σ with sc := sEval σ.nat l σ.sc }) := by
  induction l generalizing σ with
  | nil => exact runs_mono (runs_skip σ) le_rfl (fun σ' e => by subst e; rfl)
  | cons c cs ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hl
    refine runs_mono (runs_seq_eq (c.runs_cmd hl.1 σ) (ih hl.2 _)) (by simp [sCost]) (fun σ' e => ?_)
    rw [e]; rfl

theorem sEval_nil (n : ℕ → ℕ) (f : ℕ → ℝ) : sEval n [] f = f := rfl

theorem sEval_cons (n : ℕ → ℕ) (c : SI) (l : List SI) (f : ℕ → ℝ) :
    sEval n (c :: l) f = sEval n l (c.step n f) := rfl

theorem sEval_append (n : ℕ → ℕ) (l₁ l₂ : List SI) (f : ℕ → ℝ) :
    sEval n (l₁ ++ l₂) f = sEval n l₂ (sEval n l₁ f) := List.foldl_append

/-- A scalar no instruction writes keeps its value. -/
theorem sEval_frame (n : ℕ → ℕ) (l : List SI) (f : ℕ → ℝ) {x : ℕ} (hx : x ∉ l.map SI.dst) :
    sEval n l f x = f x := by
  induction l generalizing f with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at hx
    rw [sEval_cons, ih _ hx.2, SI.step, Function.update_of_ne hx.1]

/-- Two scalar states that agree on the scalars read keep agreeing after a list. -/
theorem sEval_congr (n : ℕ → ℕ) (l : List SI) {f g : ℕ → ℝ} (h : ∀ x, f x = g x) : sEval n l f = sEval n l g :=
  congrArg _ (funext h)

theorem sCost_append (l₁ l₂ : List SI) : sCost (l₁ ++ l₂) = sCost l₁ + sCost l₂ := by
  simp [sCost]

end AdversarialBco.Poly.Mach.VL
