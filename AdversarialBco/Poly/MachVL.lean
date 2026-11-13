/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.MachLang

@[expose] public section

/-!
# Typed variables over the real RAM

Typed variables in the registers and the memory of the frozen machine: naturals, real scalars and arrays of reals (a
vector of `ℝ^d` or a `d × d` matrix, row-major), with a Hoare rule and its number of steps for each primitive on
variables (a macro of one or two machine instructions), so that a command is proved on an abstract environment `Env`
and never on cells.

* `Layout`: `NN` natural variables, `NS` scalars, `NA` arrays. Natural variable `i` is register `i` (so variable `0`
  starts as `d` and variable `1` as `n`); scalar `x` is cell `x` (so scalars `0, 1, 2` start as `r₀, R₀, δ`); cell
  `NS` holds `0`; array `a` is the block of `asz d = d² + d` cells at `base a = NS + 1 + a asz d`. Registers
  `NN, ..., NN + 3` are the zero register, the pointer and two registers of the setup; registers `rS x` and `rA a`
  hold the addresses of scalar `x` and of array `a`.
* `Rep L σ s`: the machine state `s` represents the environment `σ`; it survives the writes to a variable (`setSc`,
  `setNat`, `setScratch`, `setArr`).
* `Runs L w c σ K Q`: from every state that represents `σ`, the command `c` terminates within `K` steps in a state
  that represents an environment satisfying `Q`.
* The tests of the control constructs on variables (`condR_iff`, `condN_iff`).
* The primitives on variables (`VL.sconst`, `VL.sop2`, `VL.ncast`, `VL.nconst`, `VL.nadd`, `VL.nsub`, `VL.aget`,
  `VL.aset`) and their rules `VL.runs_*`.
-/

namespace AdversarialBco.Poly.Mach

open AdversarialBco AdversarialBco.RealRAM

variable {d : ℕ}

/-- The room of every array: a vector (`d` cells) or a matrix (`d²` cells, row-major). -/
def asz (d : ℕ) : ℕ := d * d + d

/-- The numbers of natural variables, scalars and arrays of a program. -/
structure Layout where
  NN : ℕ
  NS : ℕ
  NA : ℕ

namespace Layout

/-- The register holding the address `NS` of the zero cell. -/
def rZ (L : Layout) : ℕ := L.NN
/-- The pointer register. -/
def rP (L : Layout) : ℕ := L.NN + 1
/-- The loop counter of the setup. -/
def rT (L : Layout) : ℕ := L.NN + 2
/-- The register of the setup holding `asz d`. -/
def rSZ (L : Layout) : ℕ := L.NN + 3
/-- The register holding the address `x` of scalar `x`. -/
def rS (L : Layout) (x : ℕ) : ℕ := L.NN + 4 + x
/-- The register holding the address of array `a`. -/
def rA (L : Layout) (a : ℕ) : ℕ := L.NN + 4 + L.NS + a
/-- The address of array `a`. -/
def base (L : Layout) (d a : ℕ) : ℕ := L.NS + 1 + a * asz d

theorem rZ_ne_rP (L : Layout) : L.rZ ≠ L.rP := by unfold rZ rP; omega

theorem rS_ne_rP (L : Layout) (x : ℕ) : L.rS x ≠ L.rP := by unfold rS rP; omega

theorem base_ge (L : Layout) (d a : ℕ) : L.NS + 1 ≤ L.base d a := by
  unfold base; omega

/-- Two cells of arrays are equal only for the same array and index. -/
theorem cell_inj (L : Layout) {a a' k k' : ℕ} (hk : k < asz d) (hk' : k' < asz d)
    (h : L.base d a + k = L.base d a' + k') : a = a' ∧ k = k' := by
  have hS : 0 < asz d := by omega
  have e : k + a * asz d = k' + a' * asz d := by unfold base at h; omega
  have ha : a = a' := by
    have h2 : (k + a * asz d) / asz d = (k' + a' * asz d) / asz d := by rw [e]
    rwa [Nat.add_mul_div_right _ _ hS, Nat.add_mul_div_right _ _ hS, Nat.div_eq_of_lt hk,
      Nat.div_eq_of_lt hk', Nat.zero_add, Nat.zero_add] at h2
  subst ha
  exact ⟨rfl, by omega⟩

end Layout

/-- The values of the variables, and the draws, rounds and points played. -/
structure Env (d : ℕ) where
  nat : ℕ → ℕ
  sc : ℕ → ℝ
  arr : ℕ → ℕ → ℝ
  draws : ℕ
  rounds : ℕ
  pts : ℕ → E d

namespace Env

/-- Natural variable `i` set to `v`. -/
def setNat (σ : Env d) (i v : ℕ) : Env d := { σ with nat := Function.update σ.nat i v }

/-- Scalar `x` set to `v`. -/
def setSc (σ : Env d) (x : ℕ) (v : ℝ) : Env d := { σ with sc := Function.update σ.sc x v }

/-- Entry `k` of array `a` set to `v`. -/
def setArr (σ : Env d) (a k : ℕ) (v : ℝ) : Env d :=
  { σ with arr := Function.update σ.arr a (Function.update (σ.arr a) k v) }


@[simp] theorem setNat_nat (σ : Env d) (i v j : ℕ) : (σ.setNat i v).nat j = if j = i then v else σ.nat j :=
  Function.update_apply _ _ _ _
@[simp] theorem setNat_sc (σ : Env d) (i v : ℕ) : (σ.setNat i v).sc = σ.sc := rfl
@[simp] theorem setNat_arr (σ : Env d) (i v : ℕ) : (σ.setNat i v).arr = σ.arr := rfl
@[simp] theorem setNat_draws (σ : Env d) (i v : ℕ) : (σ.setNat i v).draws = σ.draws := rfl
@[simp] theorem setNat_rounds (σ : Env d) (i v : ℕ) : (σ.setNat i v).rounds = σ.rounds := rfl
@[simp] theorem setNat_pts (σ : Env d) (i v : ℕ) : (σ.setNat i v).pts = σ.pts := rfl

@[simp] theorem setSc_sc (σ : Env d) (x : ℕ) (v : ℝ) (y : ℕ) : (σ.setSc x v).sc y = if y = x then v else σ.sc y :=
  Function.update_apply _ _ _ _
@[simp] theorem setSc_nat (σ : Env d) (x : ℕ) (v : ℝ) : (σ.setSc x v).nat = σ.nat := rfl
@[simp] theorem setSc_arr (σ : Env d) (x : ℕ) (v : ℝ) : (σ.setSc x v).arr = σ.arr := rfl
@[simp] theorem setSc_draws (σ : Env d) (x : ℕ) (v : ℝ) : (σ.setSc x v).draws = σ.draws := rfl
@[simp] theorem setSc_rounds (σ : Env d) (x : ℕ) (v : ℝ) : (σ.setSc x v).rounds = σ.rounds := rfl
@[simp] theorem setSc_pts (σ : Env d) (x : ℕ) (v : ℝ) : (σ.setSc x v).pts = σ.pts := rfl

@[simp] theorem setArr_arr (σ : Env d) (a k : ℕ) (v : ℝ) (b j : ℕ) :
    (σ.setArr a k v).arr b j = if b = a ∧ j = k then v else σ.arr b j := by
  unfold setArr
  by_cases hb : b = a
  · subst hb; by_cases hj : j = k <;> simp [hj]
  · simp [hb]
@[simp] theorem setArr_nat (σ : Env d) (a k : ℕ) (v : ℝ) : (σ.setArr a k v).nat = σ.nat := rfl
@[simp] theorem setArr_sc (σ : Env d) (a k : ℕ) (v : ℝ) : (σ.setArr a k v).sc = σ.sc := rfl
@[simp] theorem setArr_draws (σ : Env d) (a k : ℕ) (v : ℝ) : (σ.setArr a k v).draws = σ.draws := rfl
@[simp] theorem setArr_rounds (σ : Env d) (a k : ℕ) (v : ℝ) : (σ.setArr a k v).rounds = σ.rounds := rfl
@[simp] theorem setArr_pts (σ : Env d) (a k : ℕ) (v : ℝ) : (σ.setArr a k v).pts = σ.pts := rfl


end Env

/-- The machine state `s` represents the environment `σ` in the layout `L`. -/
structure Rep (L : Layout) (σ : Env d) (s : State d) : Prop where
  nat : ∀ i < L.NN, s.nreg i = σ.nat i
  rZ : s.nreg L.rZ = L.NS
  rS : ∀ x < L.NS, s.nreg (L.rS x) = x
  rA : ∀ a < L.NA, s.nreg (L.rA a) = L.base d a
  sc : ∀ x < L.NS, s.mem x = σ.sc x
  zero : s.mem L.NS = 0
  arr : ∀ a < L.NA, ∀ k < asz d, s.mem (L.base d a + k) = σ.arr a k
  draws : s.draws = σ.draws
  rounds : s.rounds = σ.rounds
  pts : s.pts = σ.pts

/-- From every state representing `σ`, `c` terminates within `K` steps in a state representing an environment that
satisfies `Q`. -/
def Runs (L : Layout) (w : World d) (c : Cmd) (σ : Env d) (K : ℕ) (Q : Env d → Prop) : Prop :=
  ∀ s, Rep L σ s → ∃ k s' σ', k ≤ K ∧ Exec w c s k s' ∧ Rep L σ' s' ∧ Q σ'

namespace Rep

variable {L : Layout} {σ : Env d} {s : State d}

theorem setSc (h : Rep L σ s) {x : ℕ} (hx : x < L.NS) (v : ℝ) :
    Rep L (σ.setSc x v) { s with mem := Function.update s.mem x v } where
  nat := h.nat
  rZ := h.rZ
  rS := h.rS
  rA := h.rA
  sc := fun y hy => by
    by_cases hyx : y = x
    · subst hyx; simp [Env.setSc]
    · simp [Env.setSc, Function.update_of_ne hyx, h.sc y hy]
  zero := by
    show Function.update s.mem x v L.NS = 0
    rw [Function.update_of_ne (by omega)]; exact h.zero
  arr := fun a ha k hk => by
    show Function.update s.mem x v (L.base d a + k) = σ.arr a k
    rw [Function.update_of_ne (by have := L.base_ge d a; omega)]; exact h.arr a ha k hk
  draws := h.draws
  rounds := h.rounds
  pts := h.pts

theorem setNat (h : Rep L σ s) {i : ℕ} (hi : i < L.NN) (v : ℕ) :
    Rep L (σ.setNat i v) { s with nreg := Function.update s.nreg i v } where
  nat := fun j hj => by
    by_cases hji : j = i
    · subst hji; simp [Env.setNat]
    · simp [Env.setNat, Function.update_of_ne hji, h.nat j hj]
  rZ := by
    show Function.update s.nreg i v L.rZ = L.NS
    rw [Function.update_of_ne (by unfold Layout.rZ; omega)]; exact h.rZ
  rS := fun x hx => by
    show Function.update s.nreg i v (L.rS x) = x
    rw [Function.update_of_ne (by unfold Layout.rS; omega)]; exact h.rS x hx
  rA := fun a ha => by
    show Function.update s.nreg i v (L.rA a) = L.base d a
    rw [Function.update_of_ne (by unfold Layout.rA; omega)]; exact h.rA a ha
  sc := h.sc
  zero := h.zero
  arr := h.arr
  draws := h.draws
  rounds := h.rounds
  pts := h.pts

/-- The registers `NN + 1, NN + 2, NN + 3` are free. -/
theorem setScratch (h : Rep L σ s) {r : ℕ} (hr : L.NN + 1 ≤ r ∧ r ≤ L.NN + 3) (v : ℕ) :
    Rep L σ { s with nreg := Function.update s.nreg r v } where
  nat := fun j hj => by
    show Function.update s.nreg r v j = σ.nat j
    rw [Function.update_of_ne (by omega)]; exact h.nat j hj
  rZ := by
    show Function.update s.nreg r v L.rZ = L.NS
    rw [Function.update_of_ne (by unfold Layout.rZ; omega)]; exact h.rZ
  rS := fun x hx => by
    show Function.update s.nreg r v (L.rS x) = x
    rw [Function.update_of_ne (by unfold Layout.rS; omega)]; exact h.rS x hx
  rA := fun a ha => by
    show Function.update s.nreg r v (L.rA a) = L.base d a
    rw [Function.update_of_ne (by unfold Layout.rA; omega)]; exact h.rA a ha
  sc := h.sc
  zero := h.zero
  arr := h.arr
  draws := h.draws
  rounds := h.rounds
  pts := h.pts

theorem setArr (h : Rep L σ s) {a k : ℕ} (ha : a < L.NA) (hk : k < asz d) (v : ℝ) :
    Rep L (σ.setArr a k v) { s with mem := Function.update s.mem (L.base d a + k) v } where
  nat := h.nat
  rZ := h.rZ
  rS := h.rS
  rA := h.rA
  sc := fun y hy => by
    show Function.update s.mem (L.base d a + k) v y = σ.sc y
    rw [Function.update_of_ne (by have := L.base_ge d a; omega)]; exact h.sc y hy
  zero := by
    show Function.update s.mem (L.base d a + k) v L.NS = 0
    rw [Function.update_of_ne (by have := L.base_ge d a; omega)]; exact h.zero
  arr := fun b hb j hj => by
    show Function.update s.mem (L.base d a + k) v (L.base d b + j) =
      Function.update σ.arr a (Function.update (σ.arr a) k v) b j
    by_cases hba : b = a
    · subst hba
      by_cases hjk : j = k
      · subst hjk; simp
      · rw [Function.update_of_ne (by omega), Function.update_self, Function.update_of_ne hjk]
        exact h.arr b hb j hj
    · rw [Function.update_of_ne (fun e => hba (L.cell_inj hj hk e).1), Function.update_of_ne hba]
      exact h.arr b hb j hj
  draws := h.draws
  rounds := h.rounds
  pts := h.pts

end Rep

/-! ## The tests of the control constructs -/

namespace VL

variable {L : Layout} {w : World d}


theorem condR_iff {σ : Env d} {s : State d} (hs : Rep L σ s) {x y : ℕ} (hx : x < L.NS) (hy : y < L.NS) :
    condR s (L.rS x) (L.rS y) ↔ σ.sc x < σ.sc y := by
  simp only [condR, hs.rS x hx, hs.rS y hy, hs.sc x hx, hs.sc y hy]

theorem condN_iff {σ : Env d} {s : State d} (hs : Rep L σ s) {i j : ℕ} (hi : i < L.NN) (hj : j < L.NN) :
    condN s i j ↔ σ.nat i < σ.nat j := by
  simp only [condN, hs.nat i hi, hs.nat j hj]

/-! ## The primitives on variables -/

/-- `x := q`. -/
def sconst (L : Layout) (x : ℕ) (q : ℚ) : Cmd := .prim (.rconst (L.rS x) q)
/-- `x := a ∘ b` for `∘` one of `+ - × /`. -/
def sop2 (L : Layout) (o : Op2) (x a b : ℕ) : Cmd := .prim (.op2 o (L.rS x) (L.rS a) (L.rS b))
/-- `x := (i : ℝ)`. -/
def ncast (L : Layout) (x i : ℕ) : Cmd := .prim (.ncast (L.rS x) i)
/-- `i := c` on naturals. -/
def nconst (i c : ℕ) : Cmd := .prim (.nconst i c)
/-- `i := a + b` on naturals. -/
def nadd (i a b : ℕ) : Cmd := .prim (.nadd i a b)
/-- `i := a - b` on naturals (truncated). -/
def nsub (i a b : ℕ) : Cmd := .prim (.nsub i a b)
/-- `x := a[i]`. -/
def aget (L : Layout) (x a i : ℕ) : Cmd :=
  .seq (.prim (.nadd L.rP (L.rA a) i)) (.prim (.op2 .add (L.rS x) L.rP L.rZ))
/-- `a[i] := x`. -/
def aset (L : Layout) (a i x : ℕ) : Cmd :=
  .seq (.prim (.nadd L.rP (L.rA a) i)) (.prim (.op2 .add L.rP (L.rS x) L.rZ))

variable {σ : Env d}

theorem runs_sconst {x : ℕ} (hx : x < L.NS) (q : ℚ) : Runs L w (sconst L x q) σ 1 (· = σ.setSc x q) :=
  fun s hs => ⟨1, _, _, le_rfl, Exec.prim _ s, by
    show Rep L _ { s with mem := Function.update s.mem (s.nreg (L.rS x)) q }
    rw [hs.rS x hx]; exact hs.setSc hx _, rfl⟩

theorem runs_sop2 {x a b : ℕ} (hx : x < L.NS) (ha : a < L.NS) (hb : b < L.NS) (o : Op2) :
    Runs L w (sop2 L o x a b) σ 1 (· = σ.setSc x (o.eval (σ.sc a) (σ.sc b))) :=
  fun s hs => ⟨1, _, _, le_rfl, Exec.prim _ s, by
    show Rep L _
      { s with
        mem := Function.update s.mem (s.nreg (L.rS x))
          (o.eval (s.mem (s.nreg (L.rS a))) (s.mem (s.nreg (L.rS b)))) }
    rw [hs.rS x hx, hs.rS a ha, hs.rS b hb, hs.sc a ha, hs.sc b hb]; exact hs.setSc hx _, rfl⟩

theorem runs_ncast {x i : ℕ} (hx : x < L.NS) (hi : i < L.NN) :
    Runs L w (ncast L x i) σ 1 (· = σ.setSc x (σ.nat i)) :=
  fun s hs => ⟨1, _, _, le_rfl, Exec.prim _ s, by
    show Rep L _ { s with mem := Function.update s.mem (s.nreg (L.rS x)) (s.nreg i : ℝ) }
    rw [hs.rS x hx, hs.nat i hi]; exact hs.setSc hx _, rfl⟩

theorem runs_nconst {i : ℕ} (hi : i < L.NN) (c : ℕ) : Runs L w (nconst i c) σ 1 (· = σ.setNat i c) :=
  fun s hs => ⟨1, _, _, le_rfl, Exec.prim _ s, hs.setNat hi c, rfl⟩

theorem runs_nadd {i a b : ℕ} (hi : i < L.NN) (ha : a < L.NN) (hb : b < L.NN) :
    Runs L w (nadd i a b) σ 1 (· = σ.setNat i (σ.nat a + σ.nat b)) :=
  fun s hs => ⟨1, _, _, le_rfl, Exec.prim _ s, by
    show Rep L _ { s with nreg := Function.update s.nreg i (s.nreg a + s.nreg b) }
    rw [hs.nat a ha, hs.nat b hb]; exact hs.setNat hi _, rfl⟩

theorem runs_nsub {i a b : ℕ} (hi : i < L.NN) (ha : a < L.NN) (hb : b < L.NN) :
    Runs L w (nsub i a b) σ 1 (· = σ.setNat i (σ.nat a - σ.nat b)) :=
  fun s hs => ⟨1, _, _, le_rfl, Exec.prim _ s, by
    show Rep L _ { s with nreg := Function.update s.nreg i (s.nreg a - s.nreg b) }
    rw [hs.nat a ha, hs.nat b hb]; exact hs.setNat hi _, rfl⟩

/-- The pointer to entry `σ.nat i` of array `a`, in two steps with the second primitive. -/
theorem exec_ptr {s : State d} (hs : Rep L σ s) {a i : ℕ} (ha : a < L.NA) (hi : i < L.NN) (p : Prim) :
    Exec w (.seq (.prim (.nadd L.rP (L.rA a) i)) (.prim p)) s 2
      (p.exec w { s with nreg := Function.update s.nreg L.rP (L.base d a + σ.nat i) }) := by
  have e : Prim.exec w s (.nadd L.rP (L.rA a) i) =
      { s with nreg := Function.update s.nreg L.rP (L.base d a + σ.nat i) } := by
    show { s with nreg := Function.update s.nreg L.rP (s.nreg (L.rA a) + s.nreg i) } = _
    rw [hs.rA a ha, hs.nat i hi]
  have h := Exec.seq (Exec.prim (w := w) (.nadd L.rP (L.rA a) i) s) (Exec.prim p _)
  rw [e] at h
  exact h

theorem runs_aget {x a i : ℕ} (hx : x < L.NS) (ha : a < L.NA) (hi : i < L.NN) (hk : σ.nat i < asz d) :
    Runs L w (aget L x a i) σ 2 (· = σ.setSc x (σ.arr a (σ.nat i))) := fun s hs => by
  have hs1 := hs.setScratch (r := L.rP) (by unfold Layout.rP; omega) (L.base d a + σ.nat i)
  refine ⟨2, _, _, le_rfl, exec_ptr hs ha hi _, ?_, rfl⟩
  show Rep L _
    { s with
      nreg := Function.update s.nreg L.rP (L.base d a + σ.nat i)
      mem := Function.update s.mem (Function.update s.nreg L.rP (L.base d a + σ.nat i) (L.rS x))
        (s.mem (Function.update s.nreg L.rP (L.base d a + σ.nat i) L.rP) +
          s.mem (Function.update s.nreg L.rP (L.base d a + σ.nat i) L.rZ)) }
  rw [Function.update_self, Function.update_of_ne L.rZ_ne_rP,
    Function.update_of_ne (L.rS_ne_rP x), hs.rS x hx, hs.rZ, hs.zero,
    hs.arr a ha _ hk, add_zero]
  exact hs1.setSc hx _

theorem runs_aset {a i x : ℕ} (ha : a < L.NA) (hi : i < L.NN) (hx : x < L.NS) (hk : σ.nat i < asz d) :
    Runs L w (aset L a i x) σ 2 (· = σ.setArr a (σ.nat i) (σ.sc x)) := fun s hs => by
  have hs1 := hs.setScratch (r := L.rP) (by unfold Layout.rP; omega) (L.base d a + σ.nat i)
  refine ⟨2, _, _, le_rfl, exec_ptr hs ha hi _, ?_, rfl⟩
  show Rep L _
    { s with
      nreg := Function.update s.nreg L.rP (L.base d a + σ.nat i)
      mem := Function.update s.mem (Function.update s.nreg L.rP (L.base d a + σ.nat i) L.rP)
        (s.mem (Function.update s.nreg L.rP (L.base d a + σ.nat i) (L.rS x)) +
          s.mem (Function.update s.nreg L.rP (L.base d a + σ.nat i) L.rZ)) }
  rw [Function.update_self, Function.update_of_ne L.rZ_ne_rP,
    Function.update_of_ne (L.rS_ne_rP x), hs.rS x hx, hs.rZ, hs.zero,
    hs.sc x hx, add_zero]
  exact hs1.setArr ha hk _


end VL


end AdversarialBco.Poly.Mach
