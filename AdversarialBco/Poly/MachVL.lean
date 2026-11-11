/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.MachLang

@[expose] public section

/-!
# The machine layer, part 2: typed variables over the real RAM

The learner's programs read and write typed variables: naturals, real scalars and arrays of reals (a vector of `ℝ^d`
or a `d × d` matrix, row-major). This file lays them out in the registers and the memory of the frozen machine and
gives each primitive on variables (a macro of one or two machine instructions) and each control construct a Hoare
rule with its exact or bounded number of steps, so that programs are proved on an abstract environment `Env` and
never on cells.

* `Layout`: `NN` natural variables, `NS` scalars, `NA` arrays. Natural variable `i` is register `i` (so variable `0`
  starts as `d` and variable `1` as `n`); scalar `x` is cell `x` (so scalars `0, 1, 2` start as `r₀, R₀, δ`); cell
  `NS` holds `0`; array `a` is the block of `asz d = d² + d` cells at `base a = NS + 1 + a asz d`. Registers
  `NN, ..., NN + 3` are the zero register, the pointer and two registers of the setup; registers `rS x` and `rA a`
  hold the addresses of scalar `x` and of array `a`.
* `Rep L σ s`: the machine state `s` represents the environment `σ`.
* `Runs L w c σ K Q`: from every state that represents `σ`, the command `c` terminates within `K` steps in a state
  that represents an environment satisfying `Q`.
* The primitives on variables (`VL.sconst`, `VL.sop2`, `VL.aget`, `VL.aset`, `VL.query`, `VL.play`, ...) and their
  rules `VL.runs_*`; the rules of sequence, conditionals and loops; `VL.setup`, the code that fills the address
  registers from the initial state, and `VL.setup_rep`.
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

/-- Array `a` read as a vector. -/
def vec (σ : Env d) (a : ℕ) : Fin d → ℝ := fun i => σ.arr a i

/-- Array `a` read as a matrix, row-major. -/
def mat (σ : Env d) (a : ℕ) : Matrix (Fin d) (Fin d) ℝ := fun i j => σ.arr a (d * i + j)

/-- Array `a` overwritten by the matrix `M` in its first `d²` entries. -/
def setMat (σ : Env d) (a : ℕ) (M : Matrix (Fin d) (Fin d) ℝ) : Env d :=
  { σ with arr := Function.update σ.arr a (fun k => if k < d * d then matEntry M (k / d) (k % d) else σ.arr a k) }

/-- The initial environment on the inputs `d, n, r₀, R₀, δ`. -/
noncomputable def init (d n : ℕ) (r0 R0 δ : ℝ) : Env d where
  nat := fun i => if i = 0 then d else if i = 1 then n else 0
  sc := fun i => if i = 0 then r0 else if i = 1 then R0 else if i = 2 then δ else 0
  arr := fun _ _ => 0
  draws := 0
  rounds := 0
  pts := fun _ => 0


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

@[simp] theorem setMat_arr (σ : Env d) (a : ℕ) (M : Matrix (Fin d) (Fin d) ℝ) (b k : ℕ) :
    (σ.setMat a M).arr b k = if b = a ∧ k < d * d then matEntry M (k / d) (k % d) else σ.arr b k := by
  unfold setMat
  by_cases hb : b = a
  · subst hb; by_cases hk : k < d * d <;> simp [hk]
  · simp [hb]
@[simp] theorem setMat_nat (σ : Env d) (a : ℕ) (M : Matrix (Fin d) (Fin d) ℝ) : (σ.setMat a M).nat = σ.nat := rfl
@[simp] theorem setMat_sc (σ : Env d) (a : ℕ) (M : Matrix (Fin d) (Fin d) ℝ) : (σ.setMat a M).sc = σ.sc := rfl
@[simp] theorem setMat_draws (σ : Env d) (a : ℕ) (M : Matrix (Fin d) (Fin d) ℝ) :
    (σ.setMat a M).draws = σ.draws := rfl
@[simp] theorem setMat_rounds (σ : Env d) (a : ℕ) (M : Matrix (Fin d) (Fin d) ℝ) :
    (σ.setMat a M).rounds = σ.rounds := rfl
@[simp] theorem setMat_pts (σ : Env d) (a : ℕ) (M : Matrix (Fin d) (Fin d) ℝ) : (σ.setMat a M).pts = σ.pts := rfl

/-- `σ'` agrees with `σ` outside the natural variables `ns`, the scalars `ss` and the arrays `as`, and has the same
draws, rounds and points played. -/
def Frame (σ σ' : Env d) (ns ss as : List ℕ) : Prop :=
  (∀ i, i ∉ ns → σ'.nat i = σ.nat i) ∧ (∀ x, x ∉ ss → σ'.sc x = σ.sc x) ∧ (∀ a, a ∉ as → σ'.arr a = σ.arr a) ∧
    σ'.draws = σ.draws ∧ σ'.rounds = σ.rounds ∧ σ'.pts = σ.pts
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

/-- The vector stored in array `a`. -/
theorem vecAt_eq (h : Rep L σ s) {a : ℕ} (ha : a < L.NA) :
    vecAt (d := d) s.mem (L.base d a) = WithLp.toLp 2 (σ.vec a) := by
  unfold vecAt Env.vec
  congr 1
  funext i
  exact h.arr a ha i (by unfold asz; have := i.2; nlinarith)

theorem mat_lt {i j : Fin d} : d * (i : ℕ) + j < d * d := by
  have hi := i.2; have hj := j.2
  calc d * (i : ℕ) + j < d * i + d := by omega
    _ = d * (i + 1) := by ring
    _ ≤ d * d := Nat.mul_le_mul_left _ hi

/-- The matrix stored in array `a`. -/
theorem matAt_eq (h : Rep L σ s) {a : ℕ} (ha : a < L.NA) :
    matAt d s.mem (L.base d a) = σ.mat a := by
  funext i j
  unfold matAt Env.mat
  rw [Nat.add_assoc]
  exact h.arr a ha _ (by unfold asz; have := mat_lt (i := i) (j := j); omega)

theorem setMat (h : Rep L σ s) {a : ℕ} (ha : a < L.NA) (M : Matrix (Fin d) (Fin d) ℝ) :
    Rep L (σ.setMat a M) { s with mem := writeMat s.mem (L.base d a) M } where
  nat := h.nat
  rZ := h.rZ
  rS := h.rS
  rA := h.rA
  sc := fun y hy => by
    show writeMat s.mem (L.base d a) M y = σ.sc y
    unfold writeMat
    rw [ite_eq_right_of_eq_false _ _ (eq_false (by have := L.base_ge d a; omega))]; exact h.sc y hy
  zero := by
    show writeMat s.mem (L.base d a) M L.NS = 0
    unfold writeMat
    rw [ite_eq_right_of_eq_false _ _ (eq_false (by have := L.base_ge d a; omega))]; exact h.zero
  arr := fun b hb j hj => by
    show writeMat s.mem (L.base d a) M (L.base d b + j) = Function.update σ.arr a _ b j
    unfold writeMat
    by_cases hba : b = a
    · subst hba
      rw [Function.update_self]
      by_cases hjd : j < d * d
      · rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by omega, by omega⟩), ite_eq_left_of_eq_true _ _ (eq_true hjd),
          Nat.add_sub_cancel_left]
      · rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)), ite_eq_right_of_eq_false _ _ (eq_false hjd)]
        exact h.arr b hb j hj
    · rw [Function.update_of_ne hba]
      by_cases hin : L.base d a ≤ L.base d b + j ∧ L.base d b + j < L.base d a + d * d
      · exfalso
        obtain ⟨k, hk⟩ : ∃ k, L.base d b + j = L.base d a + k := ⟨_, (Nat.add_sub_cancel' hin.1).symm⟩
        exact hba (L.cell_inj hj (by unfold asz; omega) hk).1
      · rw [ite_eq_right_of_eq_false _ _ (eq_false hin)]; exact h.arr b hb j hj
  draws := h.draws
  rounds := h.rounds
  pts := h.pts

end Rep

theorem Env.mat_setMat (σ : Env d) (a : ℕ) (M : Matrix (Fin d) (Fin d) ℝ) : (σ.setMat a M).mat a = M := by
  funext i j
  have hlt := Rep.mat_lt (i := i) (j := j)
  have hi := i.2
  have hj := j.2
  have hd : 0 < d := by omega
  simp only [Env.mat, Env.setMat, Function.update_self, ite_eq_left_of_eq_true _ _ (eq_true hlt), matEntry]
  have e1 : (d * (i : ℕ) + j) / d = i := by
    rw [Nat.add_comm, Nat.add_mul_div_left _ _ hd, Nat.div_eq_of_lt hj, Nat.zero_add]
  have e2 : (d * (i : ℕ) + j) % d = j := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]
  split_ifs with hc
  · congr 1 <;> ext <;> simp [e1, e2]
  · exact absurd ⟨by rw [e1]; exact hi, by rw [e2]; exact hj⟩ hc

/-! ## The rules of control -/

namespace VL

variable {L : Layout} {w : World d}

theorem runs_mono {c : Cmd} {σ : Env d} {K K' : ℕ} {Q Q' : Env d → Prop} (h : Runs L w c σ K Q) (hK : K ≤ K')
    (hQ : ∀ σ', Q σ' → Q' σ') : Runs L w c σ K' Q' := fun s hs => by
  obtain ⟨k, s', σ', hk, he, hr, hq⟩ := h s hs
  exact ⟨k, s', σ', hk.trans hK, he, hr, hQ σ' hq⟩

theorem runs_skip (σ : Env d) : Runs L w .skip σ 0 (· = σ) := fun s hs =>
  ⟨0, s, σ, le_rfl, Exec.skip s, hs, rfl⟩

theorem runs_seq {c₁ c₂ : Cmd} {σ : Env d} {K₁ K₂ : ℕ} {Q₁ Q : Env d → Prop} (h₁ : Runs L w c₁ σ K₁ Q₁)
    (h₂ : ∀ σ₁, Q₁ σ₁ → Runs L w c₂ σ₁ K₂ Q) : Runs L w (.seq c₁ c₂) σ (K₁ + K₂) Q := fun s hs => by
  obtain ⟨k₁, s₁, σ₁, hk₁, he₁, hr₁, hq₁⟩ := h₁ s hs
  obtain ⟨k₂, s₂, σ₂, hk₂, he₂, hr₂, hq₂⟩ := h₂ σ₁ hq₁ s₁ hr₁
  exact ⟨k₁ + k₂, s₂, σ₂, by omega, Exec.seq he₁ he₂, hr₂, hq₂⟩


/-- Sequence after a command with a determined result. -/
theorem runs_seq_eq {c₁ c₂ : Cmd} {σ σ₁ : Env d} {K₁ K₂ : ℕ} {Q : Env d → Prop} (h₁ : Runs L w c₁ σ K₁ (· = σ₁))
    (h₂ : Runs L w c₂ σ₁ K₂ Q) : Runs L w (.seq c₁ c₂) σ (K₁ + K₂) Q :=
  runs_seq h₁ fun _ e => e ▸ h₂

/-- `if` on scalars: `if x < y then c₁ else c₂`. -/
def ifS (L : Layout) (x y : ℕ) (c₁ c₂ : Cmd) : Cmd := .ifR (L.rS x) (L.rS y) c₁ c₂

/-- `while x < y do c` on scalars. -/
def whileS (L : Layout) (x y : ℕ) (c : Cmd) : Cmd := .whileR (L.rS x) (L.rS y) c

theorem condR_iff {σ : Env d} {s : State d} (hs : Rep L σ s) {x y : ℕ} (hx : x < L.NS) (hy : y < L.NS) :
    condR s (L.rS x) (L.rS y) ↔ σ.sc x < σ.sc y := by
  simp only [condR, hs.rS x hx, hs.rS y hy, hs.sc x hx, hs.sc y hy]

theorem condN_iff {σ : Env d} {s : State d} (hs : Rep L σ s) {i j : ℕ} (hi : i < L.NN) (hj : j < L.NN) :
    condN s i j ↔ σ.nat i < σ.nat j := by
  simp only [condN, hs.nat i hi, hs.nat j hj]

theorem runs_ifS_t {x y : ℕ} {c₁ c₂ : Cmd} {σ : Env d} {K : ℕ} {Q : Env d → Prop} (hx : x < L.NS)
    (hy : y < L.NS) (hc : σ.sc x < σ.sc y) (h : Runs L w c₁ σ K Q) : Runs L w (ifS L x y c₁ c₂) σ (K + 1) Q :=
  fun s hs => by
    obtain ⟨k, s', σ', hk, he, hr, hq⟩ := h s hs
    exact ⟨k + 1, s', σ', by omega, Exec.ifR_t ((condR_iff hs hx hy).2 hc) he, hr, hq⟩

theorem runs_ifS_f {x y : ℕ} {c₁ c₂ : Cmd} {σ : Env d} {K : ℕ} {Q : Env d → Prop} (hx : x < L.NS)
    (hy : y < L.NS) (hc : ¬ σ.sc x < σ.sc y) (h : Runs L w c₂ σ K Q) : Runs L w (ifS L x y c₁ c₂) σ (K + 2) Q :=
  fun s hs => by
    obtain ⟨k, s', σ', hk, he, hr, hq⟩ := h s hs
    exact ⟨k + 2, s', σ', by omega, Exec.ifR_f (fun h' => hc ((condR_iff hs hx hy).1 h')) he, hr, hq⟩

theorem runs_ifN_t {i j : ℕ} {c₁ c₂ : Cmd} {σ : Env d} {K : ℕ} {Q : Env d → Prop} (hi : i < L.NN)
    (hj : j < L.NN) (hc : σ.nat i < σ.nat j) (h : Runs L w c₁ σ K Q) : Runs L w (.ifN i j c₁ c₂) σ (K + 1) Q :=
  fun s hs => by
    obtain ⟨k, s', σ', hk, he, hr, hq⟩ := h s hs
    exact ⟨k + 1, s', σ', by omega, Exec.ifN_t ((condN_iff hs hi hj).2 hc) he, hr, hq⟩

theorem runs_ifN_f {i j : ℕ} {c₁ c₂ : Cmd} {σ : Env d} {K : ℕ} {Q : Env d → Prop} (hi : i < L.NN)
    (hj : j < L.NN) (hc : ¬ σ.nat i < σ.nat j) (h : Runs L w c₂ σ K Q) : Runs L w (.ifN i j c₁ c₂) σ (K + 2) Q :=
  fun s hs => by
    obtain ⟨k, s', σ', hk, he, hr, hq⟩ := h s hs
    exact ⟨k + 2, s', σ', by omega, Exec.ifN_f (fun h' => hc ((condN_iff hs hi hj).1 h')) he, hr, hq⟩

/-- A `whileN` loop with an invariant `I t` after `t` turns, at most `N` turns, each within `Kb` steps. -/
theorem runs_whileN {i j : ℕ} {c : Cmd} (hi : i < L.NN) (hj : j < L.NN) (I : ℕ → Env d → Prop) (N Kb : ℕ)
    (hlt : ∀ t σ, I t σ → σ.nat i < σ.nat j → t < N)
    (hbody : ∀ t σ, I t σ → σ.nat i < σ.nat j → Runs L w c σ Kb (I (t + 1))) :
    ∀ t σ, I t σ → Runs L w (.whileN i j c) σ ((N - t) * (Kb + 2) + 2)
      (fun σ' => ∃ t', I t' σ' ∧ ¬ σ'.nat i < σ'.nat j) := by
  suffices H : ∀ m t σ, N - t = m → I t σ → Runs L w (.whileN i j c) σ ((N - t) * (Kb + 2) + 2)
      (fun σ' => ∃ t', I t' σ' ∧ ¬ σ'.nat i < σ'.nat j) from fun t σ hI => H _ t σ rfl hI
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro t σ hm hI s hs
    by_cases hc : σ.nat i < σ.nat j
    · have htN := hlt t σ hI hc
      obtain ⟨k₁, s₁, σ₁, hk₁, he₁, hr₁, hq₁⟩ := hbody t σ hI hc s hs
      obtain ⟨k₂, s₂, σ₂, hk₂, he₂, hr₂, hq₂⟩ := ih (N - (t + 1)) (by omega) (t + 1) σ₁ rfl hq₁ s₁ hr₁
      refine ⟨k₁ + 2 + k₂, s₂, σ₂, ?_, Exec.whileN_t ((condN_iff hs hi hj).2 hc) he₁ he₂, hr₂, hq₂⟩
      have e : N - t = (N - (t + 1)) + 1 := by omega
      rw [e, Nat.succ_mul]
      omega
    · exact ⟨2, s, σ, by omega, Exec.whileN_f (fun h' => hc ((condN_iff hs hi hj).1 h')), hs, t, hI, hc⟩

/-- A `whileS` loop with an invariant `I t` after `t` turns, at most `N` turns, each within `Kb` steps. -/
theorem runs_whileS {x y : ℕ} {c : Cmd} (hx : x < L.NS) (hy : y < L.NS) (I : ℕ → Env d → Prop) (N Kb : ℕ)
    (hlt : ∀ t σ, I t σ → σ.sc x < σ.sc y → t < N)
    (hbody : ∀ t σ, I t σ → σ.sc x < σ.sc y → Runs L w c σ Kb (I (t + 1))) :
    ∀ t σ, I t σ → Runs L w (whileS L x y c) σ ((N - t) * (Kb + 2) + 2)
      (fun σ' => ∃ t', I t' σ' ∧ ¬ σ'.sc x < σ'.sc y) := by
  suffices H : ∀ m t σ, N - t = m → I t σ → Runs L w (whileS L x y c) σ ((N - t) * (Kb + 2) + 2)
      (fun σ' => ∃ t', I t' σ' ∧ ¬ σ'.sc x < σ'.sc y) from fun t σ hI => H _ t σ rfl hI
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro t σ hm hI s hs
    by_cases hc : σ.sc x < σ.sc y
    · have htN := hlt t σ hI hc
      obtain ⟨k₁, s₁, σ₁, hk₁, he₁, hr₁, hq₁⟩ := hbody t σ hI hc s hs
      obtain ⟨k₂, s₂, σ₂, hk₂, he₂, hr₂, hq₂⟩ := ih (N - (t + 1)) (by omega) (t + 1) σ₁ rfl hq₁ s₁ hr₁
      refine ⟨k₁ + 2 + k₂, s₂, σ₂, ?_, Exec.whileR_t ((condR_iff hs hx hy).2 hc) he₁ he₂, hr₂, hq₂⟩
      have e : N - t = (N - (t + 1)) + 1 := by omega
      rw [e, Nat.succ_mul]
      omega
    · exact ⟨2, s, σ, by omega, Exec.whileR_f (fun h' => hc ((condR_iff hs hx hy).1 h')), hs, t, hI, hc⟩

/-! ## The primitives on variables -/

/-- `x := q`. -/
def sconst (L : Layout) (x : ℕ) (q : ℚ) : Cmd := .prim (.rconst (L.rS x) q)
/-- `x := a ∘ b` for `∘` one of `+ - × /`. -/
def sop2 (L : Layout) (o : Op2) (x a b : ℕ) : Cmd := .prim (.op2 o (L.rS x) (L.rS a) (L.rS b))
/-- `x := f a` for `f` one of `sqrt`, `exp`, `log`. -/
def sop1 (L : Layout) (o : Op1) (x a : ℕ) : Cmd := .prim (.op1 o (L.rS x) (L.rS a))
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
/-- `a := φ(sym(src))` on matrices, `φ` the spectral function `sp` with the parameters `x, y`. -/
def mspec (L : Layout) (sp : Spec) (a src x y : ℕ) : Cmd := .prim (.spec sp (L.rA a) (L.rA src) (L.rS x) (L.rS y))
/-- `x := 1` if the vector `v` is in the body, else `0`. -/
def query (L : Layout) (x v : ℕ) : Cmd := .prim (.query (L.rS x) (L.rA v))
/-- `x :=` the next Gaussian draw. -/
def gauss (L : Layout) (x : ℕ) : Cmd := .prim (.gauss (L.rS x))
/-- Play the vector `v`; `x :=` the observation. -/
def play (L : Layout) (x v : ℕ) : Cmd := .prim (.play (L.rS x) (L.rA v))

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

theorem runs_sop1 {x a : ℕ} (hx : x < L.NS) (ha : a < L.NS) (o : Op1) :
    Runs L w (sop1 L o x a) σ 1 (· = σ.setSc x (o.eval (σ.sc a))) :=
  fun s hs => ⟨1, _, _, le_rfl, Exec.prim _ s, by
    show Rep L _ { s with mem := Function.update s.mem (s.nreg (L.rS x)) (o.eval (s.mem (s.nreg (L.rS a)))) }
    rw [hs.rS x hx, hs.rS a ha, hs.sc a ha]; exact hs.setSc hx _, rfl⟩

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

theorem runs_mspec {a src x y : ℕ} (ha : a < L.NA) (hsrc : src < L.NA) (hx : x < L.NS) (hy : y < L.NS)
    (sp : Spec) :
    Runs L w (mspec L sp a src x y) σ 1
      (· = σ.setMat a (cfc (sp.fn (σ.sc x) (σ.sc y)) (symPart (σ.mat src)))) :=
  fun s hs => ⟨1, _, _, le_rfl, Exec.prim _ s, by
    show Rep L _
      { s with
        mem := writeMat s.mem (s.nreg (L.rA a))
          (cfc (sp.fn (s.mem (s.nreg (L.rS x))) (s.mem (s.nreg (L.rS y))))
            (symPart (matAt d s.mem (s.nreg (L.rA src))))) }
    rw [hs.rA a ha, hs.rA src hsrc, hs.rS x hx, hs.rS y hy, hs.sc x hx, hs.sc y hy, hs.matAt_eq hsrc]
    exact hs.setMat ha _, rfl⟩

open Classical in
theorem runs_query {x v : ℕ} (hx : x < L.NS) (hv : v < L.NA) :
    Runs L w (query L x v) σ 1 (· = σ.setSc x (if WithLp.toLp 2 (σ.vec v) ∈ w.K then 1 else 0)) :=
  fun s hs => ⟨1, _, _, le_rfl, Exec.prim _ s, by
    show Rep L _
      { s with
        mem := Function.update s.mem (s.nreg (L.rS x))
          (if vecAt s.mem (s.nreg (L.rA v)) ∈ w.K then 1 else 0) }
    rw [hs.rS x hx, hs.rA v hv, hs.vecAt_eq hv]; exact hs.setSc hx _, rfl⟩

theorem runs_gauss {x : ℕ} (hx : x < L.NS) :
    Runs L w (gauss L x) σ 1 (· = { σ.setSc x (w.gs σ.draws) with draws := σ.draws + 1 }) :=
  fun s hs => ⟨1, _, _, le_rfl, Exec.prim _ s, by
    show Rep L _
      { s with
        mem := Function.update s.mem (s.nreg (L.rS x)) (w.gs s.draws)
        draws := s.draws + 1 }
    rw [hs.rS x hx, hs.draws]
    have h := hs.setSc hx (w.gs σ.draws)
    exact { h with draws := by simp }, rfl⟩

theorem runs_play {x v : ℕ} (hx : x < L.NS) (hv : v < L.NA) :
    Runs L w (play L x v) σ 1 (· =
      { σ.setSc x (w.f σ.rounds (WithLp.toLp 2 (σ.vec v)) + w.noise σ.rounds) with
        rounds := σ.rounds + 1
        pts := Function.update σ.pts σ.rounds (WithLp.toLp 2 (σ.vec v)) }) :=
  fun s hs => ⟨1, _, _, le_rfl, Exec.prim _ s, by
    show Rep L _
      { s with
        mem := Function.update s.mem (s.nreg (L.rS x))
          (w.f s.rounds (vecAt s.mem (s.nreg (L.rA v))) + w.noise s.rounds)
        rounds := s.rounds + 1
        pts := Function.update s.pts s.rounds (vecAt s.mem (s.nreg (L.rA v))) }
    rw [hs.rS x hx, hs.rA v hv, hs.vecAt_eq hv, hs.rounds, hs.pts]
    have h := hs.setSc hx (w.f σ.rounds (WithLp.toLp 2 (σ.vec v)) + w.noise σ.rounds)
    exact { h with rounds := by simp, pts := by simp }, rfl⟩


/-! ## Counted loops -/

/-- `for i := 0; i < n; i := i + one do body`, `one` a natural variable holding `1`. -/
def forN (i n one : ℕ) (body : Cmd) : Cmd := .seq (nconst i 0) (.whileN i n (.seq body (nadd i i one)))

/-- The rule of `forN`: `J t` holds before the turn `t` (with `i = t`); the body keeps `i`, `n`, `one` and
makes `J (t + 1)` hold once `i` is set to `t + 1`. -/
theorem runs_forN {i n one : ℕ} {body : Cmd} (hi : i < L.NN) (hn : n < L.NN) (ho : one < L.NN) (hin : i ≠ n)
    (hio : i ≠ one) (N Kb : ℕ) (J : ℕ → Env d → Prop) (σ : Env d) (hN : σ.nat n = N) (h1 : σ.nat one = 1)
    (h0 : J 0 (σ.setNat i 0))
    (hbody : ∀ t < N, ∀ σ', J t σ' → σ'.nat i = t → σ'.nat n = N → σ'.nat one = 1 →
      Runs L w body σ' Kb (fun σ'' => σ''.nat i = t ∧ σ''.nat n = N ∧ σ''.nat one = 1 ∧
        J (t + 1) (σ''.setNat i (t + 1)))) :
    Runs L w (forN i n one body) σ (N * (Kb + 3) + 3)
      (fun σ' => J N σ' ∧ σ'.nat i = N ∧ σ'.nat n = N ∧ σ'.nat one = 1) := by
  let I : ℕ → Env d → Prop := fun t σ' => J t σ' ∧ σ'.nat i = t ∧ σ'.nat n = N ∧ σ'.nat one = 1 ∧ t ≤ N
  have hloop := runs_whileN (L := L) (w := w) (c := .seq body (nadd i i one)) hi hn I N (Kb + 1)
    (fun t σ' hI hc => by obtain ⟨-, h2, h3, -, h5⟩ := hI; omega)
    (fun t σ' hI hc => by
      obtain ⟨hJ, h2, h3, h4, h5⟩ := hI
      have ht : t < N := by omega
      refine runs_seq (hbody t ht σ' hJ h2 h3 h4) (fun σ'' h => ?_)
      obtain ⟨g2, g3, g4, g5⟩ := h
      refine runs_mono (runs_nadd hi hi ho) le_rfl (fun σ3 e => ?_)
      subst e
      rw [g2, g4]
      exact ⟨g5, by simp, by simp [Ne.symm hin, g3], by simp [Ne.symm hio, g4], by omega⟩)
  have hs := runs_seq (runs_nconst (L := L) (w := w) (σ := σ) hi 0)
    (fun σ1 e => e ▸ hloop 0 (σ.setNat i 0) ⟨h0, by simp, by simp [Ne.symm hin, hN], by simp [Ne.symm hio, h1],
      Nat.zero_le _⟩)
  refine runs_mono hs (by rw [Nat.sub_zero]; ring_nf; omega) (fun σ' h => ?_)
  obtain ⟨t', ⟨hJ, h2, h3, h4, h5⟩, hc⟩ := h
  have : t' = N := by omega
  subst this
  exact ⟨hJ, h2, h3, h4⟩

end VL


/-! ## The setup: the address registers from the initial state -/

/-- `rS x := x` for `x < k`. -/
def setRS (L : Layout) : ℕ → Cmd
  | 0 => .skip
  | k + 1 => .seq (setRS L k) (.prim (.nconst (L.rS k) k))

/-- `rA a := rT`, `rT := rT + rSZ`, for `a < k`. -/
def setRA (L : Layout) : ℕ → Cmd
  | 0 => .skip
  | k + 1 => .seq (setRA L k) (.seq (.prim (.nadd (L.rA k) L.rT (L.rS 0))) (.prim (.nadd L.rT L.rT L.rSZ)))

/-- The setup: `rZ := NS`; `rS x := x`; `rSZ := d² + d` by a loop on `rT` against natural variable `0` (`d` in
the initial state); `rA a := NS + 1 + a (d² + d)`. -/
def setup (L : Layout) : Cmd :=
  .seq (.prim (.nconst L.rZ L.NS)) (.seq (setRS L L.NS) (.seq (.prim (.nconst L.rSZ 0))
    (.seq (.prim (.nconst L.rT 0))
    (.seq (.whileN L.rT 0 (.seq (.prim (.nadd L.rSZ L.rSZ 0)) (.prim (.nadd L.rT L.rT (L.rS 1)))))
    (.seq (.prim (.nadd L.rSZ L.rSZ 0)) (.seq (.prim (.nconst L.rT (L.NS + 1))) (setRA L L.NA)))))))

end AdversarialBco.Poly.Mach
