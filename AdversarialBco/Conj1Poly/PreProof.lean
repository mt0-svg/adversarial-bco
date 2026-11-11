/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Conj1Poly.PreCut
public import AdversarialBco.Conj1Poly.Centre
public import AdversarialBco.Conj1Poly.Sanity

@[expose] public section

/-!
# Theorem 1.3, the runs of the parts of PRE^b

The layout of PreCode.lean as functions of `d` and `m` (`lW0`, ..., `lOFF`), the readers `rdMat`, `rdVec`, and
`PCtx`: what every state of the prefix keeps after the set-up (the registers below `r`, the frame registers, the
scalar addresses, the rows, the constants, the cells from `OFF` on). Each part of the code has its run: from a state
in `PCtx`, an `Exec` within a bound, what it computes, and what it leaves unchanged (`Fr`).

* `test_exec`: the test computes `firstFail Am bv (1/2) a`.
* `cut_exec`: the cut computes `cutUpdate E a (rowR Am i)`.
* `iter_exec`, `stageLoop_exec`, `stage_exec`: a stage computes `stageRes Am bv j`.
* `outer_exec`: the stages run until one returns.
* `setup_exec`, `frame_exec`: the first and the last part.
-/

open MeasureTheory Matrix

namespace AdversarialBco.Conj1Poly

open AdversarialBco.RealRAM AdversarialBco.Poly AdversarialBco.Poly.Mach

variable {d : ℕ}

/-! ## The layout -/

/-- The end of the rows, the first scalar. -/
def lW0 (d m : ℕ) : ℕ := 3 + (d + 1) * m
/-- The cells `b'_i`. -/
def lFb (d m : ℕ) : ℕ := lW0 d m + 24
/-- The centre. -/
def lFa (d m : ℕ) : ℕ := lFb d m + m
/-- The vector `v` of the cut, then the scratch cells of `S(P)`. -/
def lFs (d m : ℕ) : ℕ := lFa d m + d
/-- The matrix of the ellipsoid. -/
def lFE (d m : ℕ) : ℕ := lFs d m + d + 2
/-- The offset of the memory of `P`. -/
def lOFF (d m : ℕ) : ℕ := lFE d m + d * d

/-- The matrix stored row-major from the cell `b`. -/
def rdMat (s : State d) (b : ℕ) : Matrix (Fin d) (Fin d) ℝ := fun i j => s.mem (b + d * i + j)

/-- The vector stored from the cell `b`. -/
def rdVec (s : State d) (b : ℕ) : Fin d → ℝ := fun j => s.mem (b + j)

/-- What every state of the prefix keeps after the set-up. -/
structure PCtx (r n m : ℕ) (δ : ℝ) (Am : Matrix (Fin m) (Fin d) ℚ) (bv : Fin m → ℚ) (s : State d) : Prop where
  n0 : s.nreg 0 = d
  n1 : s.nreg 1 = n
  n2 : s.nreg 2 = m
  low : ∀ i, 3 ≤ i → i < r → s.nreg i = 0
  off : s.nreg r = lOFF d m
  dd : s.nreg (r + 1) = d
  mm : s.nreg (r + 2) = m
  rows : s.nreg (r + 3) = 3
  fb : s.nreg (r + 4) = lFb d m
  fa : s.nreg (r + 5) = lFa d m
  fs : s.nreg (r + 6) = lFs d m
  acc : s.nreg (r + 7) = lFs d m + d
  tmp : s.nreg (r + 8) = lFs d m + d + 1
  one : s.nreg (r + 9) = 1
  zero : s.nreg (r + 10) = 0
  sc : ∀ x < 24, s.nreg (r + 21 + x) = lW0 d m + x
  fE : s.nreg (r + 45) = lFE d m
  d1 : s.nreg (r + 47) = d + 1
  d2 : s.nreg (r + 58) = d * d
  two : s.nreg (r + 60) = 2
  cδ : s.mem 2 = δ
  cellA : ∀ (i : Fin m) (j : Fin d), s.mem (3 + (d + 1) * i + j) = (Am i j : ℝ)
  cellB : ∀ i : Fin m, s.mem (3 + (d + 1) * i + d) = (bv i : ℝ)
  high : ∀ c, lOFF d m ≤ c → s.mem c = 0
  k0 : s.mem (lW0 d m) = 0
  k1 : s.mem (lW0 d m + 1) = 1 / 2
  k2 : s.mem (lW0 d m + 2) = 1
  k3 : s.mem (lW0 d m + 3) = 2
  k4 : s.mem (lW0 d m + 4) = 1 / 4
  k5 : s.mem (lW0 d m + 5) = d
  k6 : s.mem (lW0 d m + 6) = (d : ℝ) ^ 2 / ((d : ℝ) ^ 2 - 1)
  k7 : s.mem (lW0 d m + 7) = 2 / ((d : ℝ) + 1)
  k8 : s.mem (lW0 d m + 8) = ((d : ℝ) + 1)⁻¹
  draws : s.draws = 0
  rounds : s.rounds = 0
  pts : s.pts = fun _ => 0

/-- The registers that the prefix changes after the set-up. -/
def MutR (r i : ℕ) : Prop := i = r + 46 ∨ (r + 48 ≤ i ∧ i ≤ r + 57) ∨ i = r + 59 ∨ r + 61 ≤ i

/-- The cells that the prefix changes after the set-up. -/
def MutC (d m c : ℕ) : Prop := lW0 d m + 9 ≤ c ∧ c < lOFF d m

theorem pctx_of_fr {r n m : ℕ} {δ : ℝ} {Am : Matrix (Fin m) (Fin d) ℚ} {bv : Fin m → ℚ} {s s' : State d}
    (h : PCtx r n m δ Am bv s) (hf : Fr s s' (MutR r) (MutC d m)) : PCtx r n m δ Am bv s' := by
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35⟩
  rcases hf with ⟨hnreg, hmem, hdraws, hrounds, hpts⟩
  have h_not_mutR : ∀ i, ¬ MutR r i → s'.nreg i = s.nreg i := hnreg
  have h_not_mutC : ∀ c, ¬ MutC d m c → s'.mem c = s.mem c := hmem
  refine
    { n0 := ?_
      n1 := ?_
      n2 := ?_
      low := ?_
      off := ?_
      dd := ?_
      mm := ?_
      rows := ?_
      fb := ?_
      fa := ?_
      fs := ?_
      acc := ?_
      tmp := ?_
      one := ?_
      zero := ?_
      sc := ?_
      fE := ?_
      d1 := ?_
      d2 := ?_
      two := ?_
      cδ := ?_
      cellA := ?_
      cellB := ?_
      high := ?_
      k0 := ?_
      k1 := ?_
      k2 := ?_
      k3 := ?_
      k4 := ?_
      k5 := ?_
      k6 := ?_
      k7 := ?_
      k8 := ?_
      draws := ?_
      rounds := ?_
      pts := ?_ }
  · -- n0: s'.nreg 0 = d
    rw [h_not_mutR 0 (by unfold MutR; omega), h0]
  · -- n1: s'.nreg 1 = n
    rw [h_not_mutR 1 (by unfold MutR; omega), h1]
  · -- n2: s'.nreg 2 = m
    rw [h_not_mutR 2 (by unfold MutR; omega), h2]
  · -- low: ∀ i, 3 ≤ i → i < r → s'.nreg i = 0
    intro i hi3 hi_r
    rw [h_not_mutR i (by unfold MutR; omega), h3 i hi3 hi_r]
  · -- off: s'.nreg r = lOFF d m
    rw [h_not_mutR r (by unfold MutR; omega), h4]
  · -- dd: s'.nreg (r+1) = d
    rw [h_not_mutR (r+1) (by unfold MutR; omega), h5]
  · -- mm: s'.nreg (r+2) = m
    rw [h_not_mutR (r+2) (by unfold MutR; omega), h6]
  · -- rows: s'.nreg (r+3) = 3
    rw [h_not_mutR (r+3) (by unfold MutR; omega), h7]
  · -- fb: s'.nreg (r+4) = lFb d m
    rw [h_not_mutR (r+4) (by unfold MutR; omega), h8]
  · -- fa: s'.nreg (r+5) = lFa d m
    rw [h_not_mutR (r+5) (by unfold MutR; omega), h9]
  · -- fs: s'.nreg (r+6) = lFs d m
    rw [h_not_mutR (r+6) (by unfold MutR; omega), h10]
  · -- acc: s'.nreg (r+7) = lFs d m + d
    rw [h_not_mutR (r+7) (by unfold MutR; omega), h11]
  · -- tmp: s'.nreg (r+8) = lFs d m + d + 1
    rw [h_not_mutR (r+8) (by unfold MutR; omega), h12]
  · -- one: s'.nreg (r+9) = 1
    rw [h_not_mutR (r+9) (by unfold MutR; omega), h13]
  · -- zero: s'.nreg (r+10) = 0
    rw [h_not_mutR (r+10) (by unfold MutR; omega), h14]
  · -- sc: ∀ x < 24, s'.nreg (r+21+x) = lW0 d m + x
    intro x hx
    rw [h_not_mutR (r+21+x) (by unfold MutR; omega), h15 x hx]
  · -- fE: s'.nreg (r+45) = lFE d m
    rw [h_not_mutR (r+45) (by unfold MutR; omega), h16]
  · -- d1: s'.nreg (r+47) = d+1
    rw [h_not_mutR (r+47) (by unfold MutR; omega), h17]
  · -- d2: s'.nreg (r+58) = d*d
    rw [h_not_mutR (r+58) (by unfold MutR; omega), h18]
  · -- two: s'.nreg (r+60) = 2
    rw [h_not_mutR (r+60) (by unfold MutR; omega), h19]
  · -- cδ: s'.mem 2 = δ
    rw [h_not_mutC 2 (by unfold MutC lW0; omega), h20]
  · -- cellA: ∀ i j, s'.mem (3 + (d+1)*i + j) = (Am i j : ℝ)
    intro i j
    have hi_val : (i : ℕ) < m := i.2
    have hj_val : (j : ℕ) < d := j.2
    have h_not_mutC_cellA : ¬ MutC d m (3 + (d+1)*i + j) := by
      unfold MutC lW0
      intro h_and
      rcases h_and with ⟨hle, hlt⟩
      have hm_pos : 0 < m := by
        by_contra! h
        have : (i : ℕ) < 0 := lt_of_lt_of_le hi_val (by omega)
        exact Nat.not_lt_zero _ this
      have h_last : (d+1)*(m-1) + d < (d+1)*m := by
        have h_eq : (d+1)*(m-1) + (d+1) = (d+1)*m := by
          calc
            (d+1)*(m-1) + (d+1) = (d+1)*(m-1) + (d+1)*1 := by rw [Nat.mul_one]
            _ = (d+1)*((m-1)+1) := by rw [← Nat.mul_add]
            _ = (d+1)*m := by rw [Nat.sub_add_cancel hm_pos]
        have h_lt' : (d+1)*(m-1) + d < (d+1)*(m-1) + (d+1) := by omega
        rw [h_eq] at h_lt'
        exact h_lt'
      have h_mul : (d+1)*(i:ℕ) ≤ (d+1)*(m-1) := Nat.mul_le_mul_left (d+1) (by omega)
      have h_bound : (d+1)*(i:ℕ) + (j:ℕ) < (d+1)*m := by
        have : (d+1)*(i:ℕ) + (j:ℕ) ≤ (d+1)*(m-1) + (j:ℕ) := by omega
        have : (d+1)*(m-1) + (j:ℕ) < (d+1)*(m-1) + d := by omega
        omega
      have h_lt : 3 + (d+1)*(i:ℕ) + (j:ℕ) < 3 + (d+1)*m := by omega
      have hle' : (3 + (d+1)*m + 9 : ℕ) ≤ 3 + (d+1)*(i:ℕ) + (j:ℕ) := by simpa using hle
      have : (3 + (d+1)*m + 9 : ℕ) < 3 + (d+1)*m :=
        lt_of_le_of_lt hle' h_lt
      omega
    have h_eq_mem : s'.mem (3 + (d+1)*i + j) = s.mem (3 + (d+1)*i + j) :=
      h_not_mutC (3 + (d+1)*i + j) h_not_mutC_cellA
    rw [h_eq_mem, h21 i j]
  · -- cellB: ∀ i, s'.mem (3 + (d+1)*i + d) = (bv i : ℝ)
    intro i
    have hi_val : (i : ℕ) < m := i.2
    have h_not_mutC_cellB : ¬ MutC d m (3 + (d+1)*i + d) := by
      unfold MutC lW0
      intro h_and
      rcases h_and with ⟨hle, hlt⟩
      have hm_pos : 0 < m := by
        by_contra! h
        have : (i : ℕ) < 0 := lt_of_lt_of_le hi_val (by omega)
        exact Nat.not_lt_zero _ this
      have h_last : (d+1)*(m-1) + d < (d+1)*m := by
        have h_eq : (d+1)*(m-1) + (d+1) = (d+1)*m := by
          calc
            (d+1)*(m-1) + (d+1) = (d+1)*(m-1) + (d+1)*1 := by rw [Nat.mul_one]
            _ = (d+1)*((m-1)+1) := by rw [← Nat.mul_add]
            _ = (d+1)*m := by rw [Nat.sub_add_cancel hm_pos]
        have h_lt' : (d+1)*(m-1) + d < (d+1)*(m-1) + (d+1) := by omega
        rw [h_eq] at h_lt'
        exact h_lt'
      have h_mul : (d+1)*(i:ℕ) ≤ (d+1)*(m-1) := Nat.mul_le_mul_left (d+1) (by omega)
      have h_bound : (d+1)*(i:ℕ) + d < (d+1)*m := by
        have : (d+1)*(i:ℕ) + d ≤ (d+1)*(m-1) + d := by omega
        omega
      have h_lt : 3 + (d+1)*(i:ℕ) + d < 3 + (d+1)*m := by omega
      have hle' : (3 + (d+1)*m + 9 : ℕ) ≤ 3 + (d+1)*(i:ℕ) + d := by simpa using hle
      have : (3 + (d+1)*m + 9 : ℕ) < 3 + (d+1)*m :=
        lt_of_le_of_lt hle' h_lt
      omega
    have h_eq_mem : s'.mem (3 + (d+1)*i + d) = s.mem (3 + (d+1)*i + d) :=
      h_not_mutC (3 + (d+1)*i + d) h_not_mutC_cellB
    rw [h_eq_mem, h22 i]
  · -- high: ∀ c, lOFF d m ≤ c → s'.mem c = 0
    intro c hc
    rw [h_not_mutC c (by unfold MutC; omega), h23 c hc]
  · -- k0: s'.mem (lW0 d m) = 0
    rw [h_not_mutC (lW0 d m) (by unfold MutC lW0; omega), h24]
  · -- k1: s'.mem (lW0 d m + 1) = 1/2
    rw [h_not_mutC (lW0 d m + 1) (by unfold MutC lW0; omega), h25]
  · -- k2: s'.mem (lW0 d m + 2) = 1
    rw [h_not_mutC (lW0 d m + 2) (by unfold MutC lW0; omega), h26]
  · -- k3: s'.mem (lW0 d m + 3) = 2
    rw [h_not_mutC (lW0 d m + 3) (by unfold MutC lW0; omega), h27]
  · -- k4: s'.mem (lW0 d m + 4) = 1/4
    rw [h_not_mutC (lW0 d m + 4) (by unfold MutC lW0; omega), h28]
  · -- k5: s'.mem (lW0 d m + 5) = d
    rw [h_not_mutC (lW0 d m + 5) (by unfold MutC lW0; omega), h29]
  · -- k6: s'.mem (lW0 d m + 6) = (d:ℝ)^2 / ((d:ℝ)^2 - 1)
    rw [h_not_mutC (lW0 d m + 6) (by unfold MutC lW0; omega), h30]
  · -- k7: s'.mem (lW0 d m + 7) = 2 / ((d:ℝ) + 1)
    rw [h_not_mutC (lW0 d m + 7) (by unfold MutC lW0; omega), h31]
  · -- k8: s'.mem (lW0 d m + 8) = ((d:ℝ) + 1)⁻¹
    rw [h_not_mutC (lW0 d m + 8) (by unfold MutC lW0; omega), h32]
  · -- draws: s'.draws = 0
    rw [hdraws, h33]
  · -- rounds: s'.rounds = 0
    rw [hrounds, h34]
  · -- pts: s'.pts = fun _ => 0
    rw [hpts, h35]

/-! ## The test -/

/-- The registers and cells of the test. -/
def testR (r i : ℕ) : Prop := (r + 48 ≤ i ∧ i ≤ r + 54) ∨ i = r + 61

def testC (d m c : ℕ) : Prop := lW0 d m + 13 ≤ c ∧ c ≤ lW0 d m + 18

/-- The end of one row of the test: the left side, then the comparison with `b_t`. -/
theorem testTail_exec {w : World d} {r m W row t : ℕ} {S : State d} {dot nn b : ℝ}
    (e1 : S.nreg (r + 1) = d) (e2 : S.nreg (r + 2) = m) (e9 : S.nreg (r + 9) = 1)
    (e10 : S.nreg (r + 10) = 0) (e47 : S.nreg (r + 47) = d + 1)
    (e21 : S.nreg (r + 21) = W) (e22 : S.nreg (r + 22) = W + 1) (e34 : S.nreg (r + 34) = W + 13)
    (e35 : S.nreg (r + 35) = W + 14) (e37 : S.nreg (r + 37) = W + 16) (e38 : S.nreg (r + 38) = W + 17)
    (e39 : S.nreg (r + 39) = W + 18) (e48 : S.nreg (r + 48) = t) (e50 : S.nreg (r + 50) = row)
    (hrow : row + d < W) (m0 : S.mem W = 0) (m1 : S.mem (W + 1) = 1 / 2) (m13 : S.mem (W + 13) = dot)
    (m14 : S.mem (W + 14) = nn) (mb : S.mem (row + d) = b) :
    ∃ k S', k ≤ 9 ∧ Exec w (.seq (prims [.op1 .sqrt (r + 38) (r + 35), .op2 .mul (r + 37) (r + 22) (r + 38),
        .op2 .add (r + 37) (r + 34) (r + 37), .nadd (r + 61) (r + 50) (r + 1)])
      (.ifR (r + 61) (r + 37)
        (prims [.nconst (r + 53) 0, .nadd (r + 54) (r + 50) (r + 10), .op2 .add (r + 39) (r + 38) (r + 21),
          .nadd (r + 48) (r + 2) (r + 10)])
        (prims [.nadd (r + 50) (r + 50) (r + 47), .nadd (r + 48) (r + 48) (r + 9)]))) S k S' ∧
      Fr S S' (testR r) (fun c => W + 16 ≤ c ∧ c ≤ W + 18) ∧
      (dot + 1 / 2 * Real.sqrt nn ≤ b → S'.nreg (r + 53) = S.nreg (r + 53) ∧ S'.nreg (r + 48) = t + 1 ∧
        S'.nreg (r + 50) = row + (d + 1)) ∧
      (¬ dot + 1 / 2 * Real.sqrt nn ≤ b → S'.nreg (r + 53) = 0 ∧ S'.nreg (r + 48) = m ∧
        S'.nreg (r + 54) = row ∧ S'.mem (W + 18) = Real.sqrt nn) := by
  obtain ⟨S3, hS3⟩ : ∃ S3, S3 = [Prim.op1 .sqrt (r + 38) (r + 35), .op2 .mul (r + 37) (r + 22) (r + 38),
      .op2 .add (r + 37) (r + 34) (r + 37), .nadd (r + 61) (r + 50) (r + 1)].foldl (fun s p => p.exec w s) S :=
    ⟨_, rfl⟩
  have x3 := exec_prims w [Prim.op1 .sqrt (r + 38) (r + 35), .op2 .mul (r + 37) (r + 22) (r + 38),
      .op2 .add (r + 37) (r + 34) (r + 37), .nadd (r + 61) (r + 50) (r + 1)] S
  rw [← hS3] at x3
  have n3 : ∀ x, S3.nreg x = if x = r + 61 then row + d else S.nreg x := fun x => by
    simp only [hS3, List.foldl, Prim.exec, Function.update_apply, e50, e1]
  have m3 : ∀ c, S3.mem c =
      if c = W + 16 then dot + 1 / 2 * Real.sqrt nn else if c = W + 17 then Real.sqrt nn else S.mem c := fun c => by
    have a1 : W + 1 ≠ W + 17 := by omega
    have a2 : W + 13 ≠ W + 17 := by omega
    have a3 : W + 16 ≠ W + 17 := by omega
    simp only [hS3, List.foldl, Prim.exec, Op1.eval, Op2.eval, Function.update_apply, e38, e35, e37, e22, e34,
      if_neg a1, if_neg a2, ↓reduceIte, m1, m13, m14]
    split_ifs <;> first | rfl | omega
  have d3 : S3.draws = S.draws ∧ S3.rounds = S.rounds ∧ S3.pts = S.pts := by
    subst hS3; exact ⟨rfl, rfl, rfl⟩
  have rb : S3.mem (S3.nreg (r + 61)) = b := by
    rw [n3, if_pos rfl, m3, if_neg (by omega), if_neg (by omega), mb]
  have rl : S3.mem (S3.nreg (r + 37)) = dot + 1 / 2 * Real.sqrt nn := by
    rw [n3, if_neg (by omega), e37, m3, if_pos rfl]
  have nR : ∀ x, ¬ testR r x → x ≠ r + 61 := fun x hx h => hx (Or.inr h)
  have q : ∀ x, x ≠ r + 61 → S3.nreg x = S.nreg x := fun x h => by rw [n3, if_neg h]
  by_cases hok : dot + 1 / 2 * Real.sqrt nn ≤ b
  · have hc : ¬ condR S3 (r + 61) (r + 37) := by simp only [condR, rb, rl]; exact not_lt.2 hok
    have x4 := exec_prims w [Prim.nadd (r + 50) (r + 50) (r + 47), .nadd (r + 48) (r + 48) (r + 9)] S3
    refine ⟨_, _, ?_, Exec.seq x3 (Exec.ifR_f hc x4), ⟨fun x hx => ?_, fun c hc => ?_, ?_, ?_, ?_⟩,
      fun _ => ⟨?_, ?_, ?_⟩, fun h => absurd hok h⟩
    · simp
    · have h50 : x ≠ r + 50 := fun h => hx (Or.inl ⟨by omega, by omega⟩)
      have h48 : x ≠ r + 48 := fun h => hx (Or.inl ⟨by omega, by omega⟩)
      simp only [List.foldl, Prim.exec, Function.update_apply, if_neg h50, if_neg h48, n3, if_neg (nR x hx)]
    · simp only [List.foldl, Prim.exec, m3]
      rw [if_neg (by omega), if_neg (by omega)]
    · simp only [List.foldl, Prim.exec, d3.1]
    · simp only [List.foldl, Prim.exec, d3.2.1]
    · simp only [List.foldl, Prim.exec, d3.2.2]
    · simp only [List.foldl, Prim.exec, Function.update_apply]
      rw [if_neg (by omega), if_neg (by omega), q _ (by omega)]
    · simp [List.foldl, Prim.exec, Function.update_apply, q (r + 48) (by omega), q (r + 9) (by omega), e48, e9]
    · simp [List.foldl, Prim.exec, Function.update_apply, q (r + 50) (by omega), q (r + 47) (by omega), e50, e47]
  · have hc : condR S3 (r + 61) (r + 37) := by simp only [condR, rb, rl]; exact not_le.1 hok
    have x4 := exec_prims w [Prim.nconst (r + 53) 0, .nadd (r + 54) (r + 50) (r + 10),
      .op2 .add (r + 39) (r + 38) (r + 21), .nadd (r + 48) (r + 2) (r + 10)] S3
    refine ⟨_, _, ?_, Exec.seq x3 (Exec.ifR_t hc x4), ⟨fun x hx => ?_, fun c hc => ?_, ?_, ?_, ?_⟩,
      fun h => absurd h hok, fun _ => ⟨?_, ?_, ?_, ?_⟩⟩
    · simp
    · have h53 : x ≠ r + 53 := fun h => hx (Or.inl ⟨by omega, by omega⟩)
      have h54 : x ≠ r + 54 := fun h => hx (Or.inl ⟨by omega, by omega⟩)
      have h48 : x ≠ r + 48 := fun h => hx (Or.inl ⟨by omega, by omega⟩)
      simp only [List.foldl, Prim.exec, Function.update_apply, if_neg h53, if_neg h54, if_neg h48, n3,
        if_neg (nR x hx)]
    · have h39 : S3.nreg (r + 39) = W + 18 := by rw [n3, if_neg (by omega), e39]
      have c16 : c ≠ W + 16 := fun h => hc ⟨by omega, by omega⟩
      have c17 : c ≠ W + 17 := fun h => hc ⟨by omega, by omega⟩
      have c18 : c ≠ W + 18 := fun h => hc ⟨by omega, by omega⟩
      simp [List.foldl, Prim.exec, Function.update_apply, h39, m3, c16, c17, c18]
    · simp only [List.foldl, Prim.exec, d3.1]
    · simp only [List.foldl, Prim.exec, d3.2.1]
    · simp only [List.foldl, Prim.exec, d3.2.2]
    · simp [List.foldl, Prim.exec, Function.update_apply]
    · simp [List.foldl, Prim.exec, Function.update_apply, q (r + 2) (by omega), q (r + 10) (by omega), e2, e10]
    · simp [List.foldl, Prim.exec, Function.update_apply, q (r + 50) (by omega), q (r + 10) (by omega), e50, e10]
    · have h39 : S3.nreg (r + 39) = W + 18 := by rw [n3, if_neg (by omega), e39]
      have h38 : S3.nreg (r + 38) = W + 17 := by rw [n3, if_neg (by omega), e38]
      have h21 : S3.nreg (r + 21) = W := by rw [n3, if_neg (by omega), e21]
      simp [List.foldl, Prim.exec, Op2.eval, h39, h38, h21, m3, m0]

/-- The last cell of a row sits below the next row. -/
theorem row_end_lt {d m t : ℕ} (ht : t < m) : (d + 1) * t + d < (d + 1) * m := by
  have := Nat.mul_le_mul_left (d + 1) (Nat.succ_le_of_lt ht)
  rw [Nat.mul_succ] at this
  omega

/-- The two dot products of one row of the test: `⟨a_t, a⟩` and `⟨a_t, a_t⟩`. -/
theorem testDots_exec {w : World d} {r W row Fa : ℕ} {S : State d}
    (e1 : S.nreg (r + 1) = d) (e5 : S.nreg (r + 5) = Fa) (e9 : S.nreg (r + 9) = 1)
    (e34 : S.nreg (r + 34) = W + 13) (e35 : S.nreg (r + 35) = W + 14) (e36 : S.nreg (r + 36) = W + 15)
    (e50 : S.nreg (r + 50) = row) (hrow : row + d ≤ W) (hFa : W + 16 ≤ Fa) :
    ∃ S1 S2, Exec w (dotCmd (r + 49) (r + 1) (r + 9) (r + 50) (r + 5) (r + 51) (r + 52) (r + 34) (r + 36))
        S (7 * d + 4) S1 ∧
      Exec w (dotCmd (r + 49) (r + 1) (r + 9) (r + 50) (r + 50) (r + 51) (r + 52) (r + 35) (r + 36))
        S1 (7 * d + 4) S2 ∧
      S2.mem (W + 13) = ∑ k ∈ Finset.range d, S.mem (row + k) * S.mem (Fa + k) ∧
      S2.mem (W + 14) = ∑ k ∈ Finset.range d, S.mem (row + k) * S.mem (row + k) ∧
      Fr S S2 (fun i => i = r + 49 ∨ i = r + 51 ∨ i = r + 52) (fun c => c = W + 13 ∨ c = W + 14 ∨ c = W + 15) := by
  obtain ⟨S1, x1, v1, f1⟩ := dot_exec (w := w) (j := r + 49) (dv := r + 1) (one := r + 9) (pA := r + 50)
    (pB := r + 5) (tA := r + 51) (tB := r + 52) (acc := r + 34) (prod := r + 36) S (by omega) (by omega)
    (by omega) e9 (by rw [e34, e36]; omega)
    (fun k hk => by rw [e1] at hk; rw [e50, e34, e36]; omega)
    (fun k hk => by rw [e5, e34, e36]; omega)
  have g1 : ∀ x, x ≠ r + 49 → x ≠ r + 51 → x ≠ r + 52 → S1.nreg x = S.nreg x := fun x a b c =>
    f1.1 x (by rintro (h | h | h) <;> contradiction)
  have q1 : S1.nreg (r + 1) = d := (g1 _ (by omega) (by omega) (by omega)).trans e1
  have q9 : S1.nreg (r + 9) = 1 := (g1 _ (by omega) (by omega) (by omega)).trans e9
  have q35 : S1.nreg (r + 35) = W + 14 := (g1 _ (by omega) (by omega) (by omega)).trans e35
  have q36 : S1.nreg (r + 36) = W + 15 := (g1 _ (by omega) (by omega) (by omega)).trans e36
  have q50 : S1.nreg (r + 50) = row := (g1 _ (by omega) (by omega) (by omega)).trans e50
  obtain ⟨S2, x2, v2, f2⟩ := dot_exec (w := w) (j := r + 49) (dv := r + 1) (one := r + 9) (pA := r + 50)
    (pB := r + 50) (tA := r + 51) (tB := r + 52) (acc := r + 35) (prod := r + 36) S1 (by omega) (by omega)
    (by omega) q9 (by rw [q35, q36]; omega)
    (fun k hk => by rw [q1] at hk; rw [q50, q35, q36]; omega)
    (fun k hk => by rw [q1] at hk; rw [q50, q35, q36]; omega)
  rw [q35, q1, q50] at v2
  rw [e1, e34, e50, e5] at v1
  rw [q1] at x2
  rw [e1] at x1
  have m1 : ∀ c, c ≠ W + 13 → c ≠ W + 15 → S1.mem c = S.mem c := fun c a b =>
    f1.2.1 c (by rw [e34, e36]; rintro (h | h) <;> contradiction)
  have m2 : ∀ c, c ≠ W + 14 → c ≠ W + 15 → S2.mem c = S1.mem c := fun c a b =>
    f2.2.1 c (by rw [q35, q36]; rintro (h | h) <;> contradiction)
  refine ⟨S1, S2, x1, x2, by rw [m2 _ (by omega) (by omega), v1], ?_, ?_⟩
  · rw [v2]
    exact Finset.sum_congr rfl (fun k hk => by
      have := Finset.mem_range.1 hk
      rw [m1 _ (by omega) (by omega)])
  · refine Fr.trans (f1.mono (fun x hx => hx) (fun c hc => ?_)) (f2.mono (fun x hx => hx) (fun c hc => ?_))
    · rw [e34, e36] at hc; rcases hc with h | h <;> simp [h]
    · rw [q35, q36] at hc; rcases hc with h | h <;> simp [h]

/-- A row of the data against a sequence: the sum over the cells is the sum over the row. -/
theorem rowSum_eq {r n m : ℕ} {δ : ℝ} {Am : Matrix (Fin m) (Fin d) ℚ} {bv : Fin m → ℚ} {s : State d}
    (hc : PCtx r n m δ Am bv s) (i : Fin m) (f : ℕ → ℝ) :
    ∑ k ∈ Finset.range d, s.mem (3 + (d + 1) * i + k) * f k = ∑ j : Fin d, (Am i j : ℝ) * f j := by
  rw [← Fin.sum_univ_eq_sum_range (fun k => s.mem (3 + (d + 1) * i + k) * f k) d]
  exact Finset.sum_congr rfl (fun j _ => by rw [hc.cellA i j])

/-- One row of the test. -/
theorem testBody_exec {w : World d} {r n m : ℕ} {δ : ℝ} {Am : Matrix (Fin m) (Fin d) ℚ} {bv : Fin m → ℚ}
    {s S : State d} (hc : PCtx r n m δ Am bv s) (hf : Fr s S (testR r) (testC d m)) {t : ℕ} (ht : t < m)
    (h48 : S.nreg (r + 48) = t) (h50 : S.nreg (r + 50) = 3 + (d + 1) * t) :
    ∃ k S', k ≤ 14 * d + 17 ∧ Exec w (testBody r) S k S' ∧ Fr s S' (testR r) (testC d m) ∧
      (RowOK Am bv (1 / 2) (rdVec s (lFa d m)) ⟨t, ht⟩ → S'.nreg (r + 53) = S.nreg (r + 53) ∧
        S'.nreg (r + 48) = t + 1 ∧ S'.nreg (r + 50) = 3 + (d + 1) * (t + 1)) ∧
      (¬ RowOK Am bv (1 / 2) (rdVec s (lFa d m)) ⟨t, ht⟩ → S'.nreg (r + 53) = 0 ∧ S'.nreg (r + 48) = m ∧
        S'.nreg (r + 54) = 3 + (d + 1) * t ∧ S'.mem (lW0 d m + 18) = rowNorm Am ⟨t, ht⟩) := by
  have nR : ∀ x, (x < r + 48 ∨ r + 54 < x) → x ≠ r + 61 → S.nreg x = s.nreg x := fun x h1 h2 =>
    hf.1 x (by unfold testR; omega)
  have nC : ∀ c, (c < lW0 d m + 13 ∨ lW0 d m + 18 < c) → S.mem c = s.mem c := fun c h =>
    hf.2.1 c (by unfold testC; omega)
  have hW : lW0 d m = 3 + (d + 1) * m := rfl
  have hFa : lFa d m = lW0 d m + 24 + m := rfl
  have esc : ∀ x < 24, S.nreg (r + 21 + x) = lW0 d m + x := fun x hx =>
    (nR _ (by omega) (by omega)).trans (hc.sc x hx)
  have hrow : 3 + (d + 1) * t + d < lW0 d m := by have := row_end_lt (d := d) ht; rw [hW]; omega
  obtain ⟨S1, S2, x1, x2, v1, v2, fD⟩ := testDots_exec (w := w) (r := r) (W := lW0 d m)
    (row := 3 + (d + 1) * t) (Fa := lFa d m) (S := S) ((nR _ (by omega) (by omega)).trans hc.dd)
    ((nR _ (by omega) (by omega)).trans hc.fa) ((nR _ (by omega) (by omega)).trans hc.one) (esc 13 (by norm_num))
    (esc 14 (by norm_num)) (esc 15 (by norm_num)) h50 (by omega) (by rw [hFa]; omega)
  have g : ∀ x, x ≠ r + 49 → x ≠ r + 51 → x ≠ r + 52 → S2.nreg x = S.nreg x := fun x a b c =>
    fD.1 x (by rintro (h | h | h) <;> contradiction)
  have gs : ∀ x, x < r + 48 ∨ r + 54 < x → x ≠ r + 61 → S2.nreg x = s.nreg x := fun x h1 h2 =>
    (g x (by omega) (by omega) (by omega)).trans (nR x h1 h2)
  have gm : ∀ c, c < lW0 d m + 13 ∨ lW0 d m + 18 < c → S2.mem c = s.mem c := fun c h =>
    (fD.2.1 c (by omega)).trans (nC c h)
  have hdot : ∑ k ∈ Finset.range d, S.mem (3 + (d + 1) * t + k) * S.mem (lFa d m + k) =
      ∑ j : Fin d, (Am ⟨t, ht⟩ j : ℝ) * rdVec s (lFa d m) j := by
    refine (Finset.sum_congr rfl (fun k hk => ?_)).trans (rowSum_eq hc ⟨t, ht⟩ (fun k => s.mem (lFa d m + k)))
    have := Finset.mem_range.1 hk
    rw [nC _ (by omega), nC (lFa d m + k) (by rw [hFa]; omega)]
  have hnn : ∑ k ∈ Finset.range d, S.mem (3 + (d + 1) * t + k) * S.mem (3 + (d + 1) * t + k) =
      ∑ j : Fin d, (Am ⟨t, ht⟩ j : ℝ) ^ 2 := by
    rw [Finset.sum_congr rfl (fun k hk => by rw [nC (3 + (d + 1) * t + k) (by have := Finset.mem_range.1 hk; omega)]),
      rowSum_eq hc ⟨t, ht⟩ (fun k => s.mem (3 + (d + 1) * t + k))]
    exact Finset.sum_congr rfl (fun j _ => by rw [sq]; congr 1; exact hc.cellA ⟨t, ht⟩ j)
  rw [hdot] at v1
  rw [hnn] at v2
  obtain ⟨kT, S', hkT, xT, fT, hok, hno⟩ := testTail_exec (w := w) (r := r) (m := m) (W := lW0 d m)
    (row := 3 + (d + 1) * t) (t := t) (S := S2) (b := (bv ⟨t, ht⟩ : ℝ))
    ((gs _ (by omega) (by omega)).trans hc.dd) ((gs _ (by omega) (by omega)).trans hc.mm)
    ((gs _ (by omega) (by omega)).trans hc.one) ((gs _ (by omega) (by omega)).trans hc.zero)
    ((gs _ (by omega) (by omega)).trans hc.d1)
    (by simpa using (gs _ (by omega) (by omega)).trans (hc.sc 0 (by norm_num)))
    ((gs _ (by omega) (by omega)).trans (hc.sc 1 (by norm_num)))
    ((gs _ (by omega) (by omega)).trans (hc.sc 13 (by norm_num)))
    ((gs _ (by omega) (by omega)).trans (hc.sc 14 (by norm_num)))
    ((gs _ (by omega) (by omega)).trans (hc.sc 16 (by norm_num)))
    ((gs _ (by omega) (by omega)).trans (hc.sc 17 (by norm_num)))
    ((gs _ (by omega) (by omega)).trans (hc.sc 18 (by norm_num)))
    ((g _ (by omega) (by omega) (by omega)).trans h48) ((g _ (by omega) (by omega) (by omega)).trans h50)
    hrow ((gm _ (by omega)).trans hc.k0) ((gm _ (by omega)).trans hc.k1) v1 v2
    ((gm _ (by omega)).trans (hc.cellB ⟨t, ht⟩))
  have h53 : S2.nreg (r + 53) = S.nreg (r + 53) := g _ (by omega) (by omega) (by omega)
  refine ⟨_, S', ?_, Exec.seq x1 (Exec.seq x2 xT), ?_, fun h => ?_, fun h => ?_⟩
  · omega
  · refine hf.trans (Fr.trans (fD.mono (fun x hx => ?_) (fun c hc => ?_)) (fT.mono (fun x hx => hx) (fun c hc => ?_)))
    · simp only [testR]; omega
    · simp only [testC]; omega
    · simp only [testC]; omega
  · obtain ⟨a1, a2, a3⟩ := hok h
    exact ⟨a1.trans h53, a2, by rw [a3]; ring⟩
  · obtain ⟨a1, a2, a3, a4⟩ := hno h
    exact ⟨a1, a2, a3, a4⟩

theorem firstFail_eq_some {m : ℕ} {Am : Matrix (Fin m) (Fin d) ℚ} {bv : Fin m → ℚ} {ρ : ℝ} {a : Fin d → ℝ}
    {i : Fin m} (h1 : ¬ RowOK Am bv ρ a i) (h2 : ∀ j < i, RowOK Am bv ρ a j) : firstFail Am bv ρ a = some i := by
  cases hf : firstFail Am bv ρ a with
  | none => exact absurd (firstFail_none hf i) h1
  | some i0 =>
    obtain ⟨n0, m0⟩ := firstFail_some hf
    rcases lt_trichotomy i0 i with h | h | h
    · exact absurd (h2 i0 h) n0
    · rw [h]
    · exact absurd (m0 i h) h1

theorem firstFail_eq_none {m : ℕ} {Am : Matrix (Fin m) (Fin d) ℚ} {bv : Fin m → ℚ} {ρ : ℝ} {a : Fin d → ℝ}
    (h : ∀ i, RowOK Am bv ρ a i) : firstFail Am bv ρ a = none := by
  cases hf : firstFail Am bv ρ a with
  | none => rfl
  | some i0 => exact absurd (h i0) (firstFail_some hf).1

theorem test_exec {w : World d} {r n m : ℕ} {δ : ℝ} {Am : Matrix (Fin m) (Fin d) ℚ} {bv : Fin m → ℚ}
    {s : State d} (hc : PCtx r n m δ Am bv s) :
    ∃ k s', k ≤ 20 * (d + 1) * (m + 1) ∧ Exec w (testCmd r) s k s' ∧ Fr s s' (testR r) (testC d m) ∧
      (firstFail Am bv (1 / 2) (rdVec s (lFa d m)) = none → s'.nreg (r + 53) = 1) ∧
      (∀ i, firstFail Am bv (1 / 2) (rdVec s (lFa d m)) = some i →
        s'.nreg (r + 53) = 0 ∧ s'.nreg (r + 54) = 3 + (d + 1) * i ∧ s'.mem (lW0 d m + 18) = rowNorm Am i) := by
  have hm2 : ∀ S : State d, Fr s S (testR r) (testC d m) → S.nreg (r + 2) = m := fun S h =>
    (h.1 _ (by unfold testR; omega)).trans hc.mm
  let I : ℕ → State d → Prop := fun t S => Fr s S (testR r) (testC d m) ∧
    ((t ≤ m ∧ S.nreg (r + 48) = t ∧ S.nreg (r + 53) = 1 ∧ S.nreg (r + 50) = 3 + (d + 1) * t ∧
        ∀ i : Fin m, (i : ℕ) < t → RowOK Am bv (1 / 2) (rdVec s (lFa d m)) i) ∨
      ∃ i : Fin m, firstFail Am bv (1 / 2) (rdVec s (lFa d m)) = some i ∧ S.nreg (r + 48) = m ∧
        S.nreg (r + 53) = 0 ∧ S.nreg (r + 54) = 3 + (d + 1) * i ∧ S.mem (lW0 d m + 18) = rowNorm Am i)
  have hbound : ∀ t S, I t S → condN S (r + 48) (r + 2) → t < m := by
    intro t S hI hcn
    obtain ⟨hF, ⟨-, h48, -⟩ | ⟨i, -, h48, -⟩⟩ := hI
    · simp only [condN, h48, hm2 S hF] at hcn; exact hcn
    · simp only [condN, h48, hm2 S hF] at hcn; exact absurd hcn (lt_irrefl m)
  have hbody : ∀ t S, I t S → condN S (r + 48) (r + 2) →
      ∃ k S', k ≤ 14 * d + 17 ∧ Exec w (testBody r) S k S' ∧ I (t + 1) S' := by
    intro t S hI hcn
    obtain ⟨hF, ⟨htm, h48, h53, h50, hok⟩ | ⟨i, -, h48, -⟩⟩ := hI
    · have ht : t < m := by simp only [condN, h48, hm2 S hF] at hcn; exact hcn
      obtain ⟨k, S', hk, x, hF', hY, hN⟩ := testBody_exec hc hF ht h48 h50
      refine ⟨k, S', hk, x, hF', ?_⟩
      by_cases hr : RowOK Am bv (1 / 2) (rdVec s (lFa d m)) ⟨t, ht⟩
      · obtain ⟨a1, a2, a3⟩ := hY hr
        refine Or.inl ⟨by omega, a2, a1.trans h53, a3, fun i hi => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | h
        · exact hok i h
        · have : i = ⟨t, ht⟩ := Fin.ext h
          rw [this]; exact hr
      · obtain ⟨a1, a2, a3, a4⟩ := hN hr
        exact Or.inr ⟨⟨t, ht⟩, firstFail_eq_some hr (fun j hj => hok j hj), a2, a1, a3, a4⟩
    · simp only [condN, h48, hm2 S hF] at hcn; exact absurd hcn (lt_irrefl m)
  obtain ⟨S0, hS0⟩ : ∃ S0, S0 = [Prim.nconst (r + 48) 0, .nconst (r + 53) 1, .nadd (r + 50) (r + 3) (r + 10)].foldl
      (fun s p => p.exec w s) s := ⟨_, rfl⟩
  have x0 := exec_prims w [Prim.nconst (r + 48) 0, .nconst (r + 53) 1, .nadd (r + 50) (r + 3) (r + 10)] s
  rw [← hS0] at x0
  have hI0 : I 0 S0 := by
    subst hS0
    refine ⟨⟨fun x hx => ?_, fun c _ => rfl, rfl, rfl, rfl⟩, Or.inl ⟨Nat.zero_le _, ?_, ?_, ?_, fun i hi => absurd hi (Nat.not_lt_zero _)⟩⟩
    · have h1 : x ≠ r + 48 := fun h => hx (Or.inl ⟨by omega, by omega⟩)
      have h2 : x ≠ r + 53 := fun h => hx (Or.inl ⟨by omega, by omega⟩)
      have h3 : x ≠ r + 50 := fun h => hx (Or.inl ⟨by omega, by omega⟩)
      simp [List.foldl, Prim.exec, Function.update_apply, h1, h2, h3]
    · simp [List.foldl, Prim.exec, Function.update_apply]
    · simp [List.foldl, Prim.exec, Function.update_apply]
    · simp [List.foldl, Prim.exec, Function.update_apply, hc.rows, hc.zero]
  obtain ⟨k, S', t', hk, xL, hI', hnc⟩ :=
    exec_whileN_inv (w := w) (a := r + 48) (b := r + 2) (c := testBody r) I m (14 * d + 17) hbound hbody 0 S0 hI0
  refine ⟨_, S', ?_, Exec.seq x0 xL, hI'.1, ?_⟩
  · simp only [List.length_cons, List.length_nil, Nat.sub_zero] at hk ⊢
    nlinarith [Nat.zero_le (d * m)]
  obtain ⟨hF', ⟨htm, h48, h53, -, hok⟩ | ⟨i0, hi0, -, h53, h54, h18⟩⟩ := hI'
  · have htm' : t' = m := by simp only [condN, h48, hm2 S' hF'] at hnc; omega
    have hnone : firstFail Am bv (1 / 2) (rdVec s (lFa d m)) = none :=
      firstFail_eq_none (fun i => hok i (htm' ▸ i.2))
    exact ⟨fun _ => h53, fun i hi => absurd (hnone.symm.trans hi) (by simp)⟩
  · refine ⟨fun h => absurd (h.symm.trans hi0) (by simp), fun i hi => ?_⟩
    have : i = i0 := Option.some_injective _ (hi.symm.trans hi0)
    subst this
    exact ⟨h53, h54, h18⟩

/-! ## The cut -/

/-- The registers and cells of the cut. -/
def cutR (r i : ℕ) : Prop := (r + 48 ≤ i ∧ i ≤ r + 52) ∨ i = r + 59 ∨ i = r + 61

def cutC (d m c : ℕ) : Prop :=
  c = lW0 d m + 13 ∨ c = lW0 d m + 15 ∨ (lW0 d m + 19 ≤ c ∧ c ≤ lW0 d m + 22) ∨ (lFa d m ≤ c ∧ c < lFs d m + d) ∨
    (lFE d m ≤ c ∧ c < lOFF d m)

/-- `v_t = ⟨E_t, g⟩` read from the cells of `s`, with `g` from the cell `gB`. -/
noncomputable def cutV (s : State d) (m gB t : ℕ) : ℝ :=
  ∑ l ∈ Finset.range d, s.mem (lFE d m + d * t + l) * s.mem (gB + l)

/-- `γ = ⟨g, E g⟩` read from the cells of `s`. -/
noncomputable def cutG (s : State d) (m gB : ℕ) : ℝ := ∑ t ∈ Finset.range d, s.mem (gB + t) * cutV s m gB t

/-- The cut, first part: `γ ← 0`, then the loop of `v = E g` and `γ`. -/
theorem cutA1_exec {w : World d} {r n m : ℕ} {δ : ℝ} {Am : Matrix (Fin m) (Fin d) ℚ} {bv : Fin m → ℚ}
    {s : State d} (hc : PCtx r n m δ Am bv s) {gB : ℕ} (hg : s.nreg (r + 54) = gB) (hgB : gB + d ≤ lW0 d m) :
    ∃ S1 S2 k, k ≤ d * (7 * d + 13) + 2 ∧
      Exec w (prims [.rconst (r + 40) 0, .nadd (r + 59) (r + 45) (r + 10), .nconst (r + 48) 0]) s 3 S1 ∧
      Exec w (.whileN (r + 48) (r + 1) (mvBody r)) S1 k S2 ∧
      (∀ t < d, S2.mem (lFs d m + t) = cutV s m gB t) ∧ S2.mem (lW0 d m + 19) = cutG s m gB ∧
      Fr s S2 (fun i => (r + 48 ≤ i ∧ i ≤ r + 52) ∨ i = r + 59)
        (fun c => c = lW0 d m + 13 ∨ c = lW0 d m + 15 ∨ c = lW0 d m + 19 ∨ (lFs d m ≤ c ∧ c < lFs d m + d)) := by
  have hW : lFs d m = lW0 d m + 24 + m + d := rfl
  have hE : lFE d m = lFs d m + d + 2 := rfl
  obtain ⟨S1, hS1⟩ : ∃ S1, S1 = [Prim.rconst (r + 40) 0, .nadd (r + 59) (r + 45) (r + 10), .nconst (r + 48) 0].foldl
      (fun s p => p.exec w s) s := ⟨_, rfl⟩
  have x1 := exec_prims w [Prim.rconst (r + 40) 0, .nadd (r + 59) (r + 45) (r + 10), .nconst (r + 48) 0] s
  rw [← hS1] at x1
  have e40 : s.nreg (r + 40) = lW0 d m + 19 := hc.sc 19 (by norm_num)
  have n1 : ∀ x, S1.nreg x = if x = r + 48 then 0 else if x = r + 59 then lFE d m else s.nreg x := fun x => by
    subst hS1
    simp only [List.foldl, Prim.exec, Function.update_apply, hc.fE, hc.zero, add_zero]
  have m1 : ∀ c, S1.mem c = if c = lW0 d m + 19 then 0 else s.mem c := fun c => by
    subst hS1
    simp only [List.foldl, Prim.exec, Function.update_apply, e40]
    split_ifs <;> simp_all
  have q : ∀ x, x ≠ r + 48 → x ≠ r + 59 → S1.nreg x = s.nreg x := fun x a b => by rw [n1, if_neg a, if_neg b]
  have mc : ∀ c, c ≠ lW0 d m + 19 → S1.mem c = s.mem c := fun c a => by rw [m1, if_neg a]
  have d1 : S1.draws = s.draws ∧ S1.rounds = s.rounds ∧ S1.pts = s.pts := by subst hS1; exact ⟨rfl, rfl, rfl⟩
  obtain ⟨k, S2, hk, x2, hv, hγ, f2⟩ := mvLoop_exec (w := w) (r := r) (W := lW0 d m) (Fs := lFs d m)
    (FE := lFE d m) (gB := gB) (S := S1)
    ((q _ (by omega) (by omega)).trans hc.dd) ((q _ (by omega) (by omega)).trans hc.fs)
    ((q _ (by omega) (by omega)).trans hc.one)
    (by simpa using (q _ (by omega) (by omega)).trans (hc.sc 0 (by norm_num)))
    ((q _ (by omega) (by omega)).trans (hc.sc 13 (by norm_num)))
    ((q _ (by omega) (by omega)).trans (hc.sc 15 (by norm_num)))
    ((q _ (by omega) (by omega)).trans e40) (by rw [n1]; simp)
    ((q _ (by omega) (by omega)).trans hg) (by rw [n1]; simp)
    ((mc _ (by omega)).trans hc.k0) (by rw [m1, if_pos rfl]) hgB (by rw [hW]; omega) (by rw [hE]; omega)
  refine ⟨S1, S2, k, hk, x1, x2, fun t ht => ?_, ?_, ?_⟩
  · rw [hv t ht]
    refine Finset.sum_congr rfl (fun l hl => ?_)
    have := Finset.mem_range.1 hl
    rw [mc _ (by rw [hE]; omega), mc _ (by omega)]
  · rw [hγ]
    refine Finset.sum_congr rfl (fun t ht => ?_)
    have := Finset.mem_range.1 ht
    rw [mc _ (by omega)]
    congr 1
    refine Finset.sum_congr rfl (fun l hl => ?_)
    have := Finset.mem_range.1 hl
    rw [mc _ (by rw [hE]; omega), mc _ (by omega)]
  · refine Fr.trans ⟨fun x hx => ?_, fun c hc' => ?_, d1.1, d1.2.1, d1.2.2⟩ f2
    · exact q x (fun h => hx (Or.inl ⟨by omega, by omega⟩)) (fun h => hx (Or.inr h))
    · exact mc c (fun h => hc' (Or.inr (Or.inr (Or.inl h))))

/-- The cut, second part: `inv = 1/√γ`, then the loop of `b` and `a'`. -/
theorem cutA2_exec {w : World d} {r n m : ℕ} {δ : ℝ} {Am : Matrix (Fin m) (Fin d) ℚ} {bv : Fin m → ℚ}
    {s S2 : State d} (hc : PCtx r n m δ Am bv s)
    (f2 : Fr s S2 (fun i => (r + 48 ≤ i ∧ i ≤ r + 52) ∨ i = r + 59)
      (fun c => c = lW0 d m + 13 ∨ c = lW0 d m + 15 ∨ c = lW0 d m + 19 ∨ (lFs d m ≤ c ∧ c < lFs d m + d))) :
    ∃ S3 S4 k, k ≤ d * 8 + 2 ∧
      Exec w (prims [.op1 .sqrt (r + 42) (r + 40), .op2 .div (r + 41) (r + 23) (r + 42), .nconst (r + 48) 0])
        S2 3 S3 ∧
      Exec w (.whileN (r + 48) (r + 1) (baBody r)) S3 k S4 ∧
      (∀ t < d, S4.mem (lFs d m + t) = 1 / Real.sqrt (S2.mem (lW0 d m + 19)) * S2.mem (lFs d m + t)) ∧
      (∀ t < d, S4.mem (lFa d m + t) = s.mem (lFa d m + t) -
        ((d : ℝ) + 1)⁻¹ * (1 / Real.sqrt (S2.mem (lW0 d m + 19)) * S2.mem (lFs d m + t))) ∧
      Fr S2 S4 (fun i => i = r + 48 ∨ i = r + 51 ∨ i = r + 52)
        (fun c => c = lW0 d m + 20 ∨ c = lW0 d m + 21 ∨ (lFa d m ≤ c ∧ c < lFs d m + d)) := by
  have hFa : lFa d m = lW0 d m + 24 + m := rfl
  have hFs : lFs d m = lFa d m + d := rfl
  have g2 : ∀ x, x < r + 48 ∨ (r + 52 < x ∧ x ≠ r + 59) → S2.nreg x = s.nreg x := fun x h =>
    f2.1 x (by omega)
  have c2 : ∀ c, c < lW0 d m + 13 ∨ (lW0 d m + 19 < c ∧ c < lFs d m) → S2.mem c = s.mem c := fun c h =>
    f2.2.1 c (by omega)
  have e : ∀ x < 24, S2.nreg (r + 21 + x) = lW0 d m + x := fun x hx =>
    (g2 _ (by omega)).trans (hc.sc x hx)
  have e19 : S2.nreg (r + 40) = lW0 d m + 19 := e 19 (by norm_num)
  have e20 : S2.nreg (r + 41) = lW0 d m + 20 := e 20 (by norm_num)
  have e21 : S2.nreg (r + 42) = lW0 d m + 21 := e 21 (by norm_num)
  have e2 : S2.nreg (r + 23) = lW0 d m + 2 := e 2 (by norm_num)
  have k2 : S2.mem (lW0 d m + 2) = 1 := (c2 _ (by omega)).trans hc.k2
  obtain ⟨S3, hS3⟩ : ∃ S3, S3 = [Prim.op1 .sqrt (r + 42) (r + 40), .op2 .div (r + 41) (r + 23) (r + 42),
      .nconst (r + 48) 0].foldl (fun s p => p.exec w s) S2 := ⟨_, rfl⟩
  have x3 := exec_prims w [Prim.op1 .sqrt (r + 42) (r + 40), .op2 .div (r + 41) (r + 23) (r + 42),
      .nconst (r + 48) 0] S2
  rw [← hS3] at x3
  have n3 : ∀ x, S3.nreg x = if x = r + 48 then 0 else S2.nreg x := fun x => by
    subst hS3
    simp only [List.foldl, Prim.exec, Function.update_apply]
  have m3 : ∀ c, S3.mem c = if c = lW0 d m + 20 then 1 / Real.sqrt (S2.mem (lW0 d m + 19))
      else if c = lW0 d m + 21 then Real.sqrt (S2.mem (lW0 d m + 19)) else S2.mem c := fun c => by
    have a1 : lW0 d m + 2 ≠ lW0 d m + 21 := by omega
    subst hS3
    simp only [List.foldl, Prim.exec, Function.update_apply, Op1.eval, Op2.eval, e19, e20, e21, e2, if_neg a1,
      ↓reduceIte, k2]
  have q : ∀ x, x ≠ r + 48 → S3.nreg x = S2.nreg x := fun x h => by rw [n3, if_neg h]
  have mq : ∀ c, c ≠ lW0 d m + 20 → c ≠ lW0 d m + 21 → S3.mem c = S2.mem c := fun c a b => by
    rw [m3, if_neg a, if_neg b]
  have d3 : S3.draws = S2.draws ∧ S3.rounds = S2.rounds ∧ S3.pts = S2.pts := by subst hS3; exact ⟨rfl, rfl, rfl⟩
  obtain ⟨k, S4, hk, x4, hb, ha, f4⟩ := baLoop_exec (w := w) (r := r) (W := lW0 d m) (Fa := lFa d m)
    (Fs := lFs d m) (S := S3)
    ((q _ (by omega)).trans ((g2 _ (by omega)).trans hc.dd)) ((q _ (by omega)).trans ((g2 _ (by omega)).trans hc.fa))
    ((q _ (by omega)).trans ((g2 _ (by omega)).trans hc.fs)) ((q _ (by omega)).trans ((g2 _ (by omega)).trans hc.one))
    ((q _ (by omega)).trans (e 8 (by norm_num))) ((q _ (by omega)).trans e20) ((q _ (by omega)).trans e21)
    (by rw [n3, if_pos rfl]) (by omega) (by omega)
  have h20 : S3.mem (lW0 d m + 20) = 1 / Real.sqrt (S2.mem (lW0 d m + 19)) := by rw [m3, if_pos rfl]
  refine ⟨S3, S4, k, hk, x3, x4, fun t ht => ?_, fun t ht => ?_, ?_⟩
  · rw [hb t ht, h20, mq (lFs d m + t) (by omega) (by omega)]
  · rw [ha t ht, h20, mq (lFs d m + t) (by omega) (by omega), mq (lFa d m + t) (by omega) (by omega),
      mq (lW0 d m + 8) (by omega) (by omega), c2 (lFa d m + t) (by omega), c2 (lW0 d m + 8) (by omega), hc.k8]
  · refine Fr.trans ⟨fun x hx => ?_, fun c hc' => ?_, d3.1, d3.2.1, d3.2.2⟩
      (f4.mono (fun x hx => hx) (fun c hc' => ?_))
    · exact q x (fun h => hx (Or.inl h))
    · exact mq c (fun h => hc' (Or.inl h)) (fun h => hc' (Or.inr (Or.inl h)))
    · rcases hc' with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)

/-- The cut, last part: `E/4` when `d < 2`, else the rank-one update. -/
theorem cutB_exec {w : World d} {r n m : ℕ} {δ : ℝ} {Am : Matrix (Fin m) (Fin d) ℚ} {bv : Fin m → ℚ}
    {s S4 : State d} (hc : PCtx r n m δ Am bv s)
    (f4 : Fr s S4 (cutR r) (fun c => c = lW0 d m + 13 ∨ c = lW0 d m + 15 ∨
      (lW0 d m + 19 ≤ c ∧ c ≤ lW0 d m + 21) ∨ (lFa d m ≤ c ∧ c < lFs d m + d))) :
    ∃ k S', k ≤ d * (9 * d + 8) + 8 ∧
      Exec w (.ifN (r + 1) (r + 60) (.prim (.op2 .mul (r + 45) (r + 25) (r + 45)))
        (.seq (prims [.nadd (r + 59) (r + 45) (r + 10), .nconst (r + 48) 0])
          (.whileN (r + 48) (r + 1) (r1Outer r)))) S4 k S' ∧
      Fr S4 S' (cutR r) (fun c => c = lW0 d m + 21 ∨ c = lW0 d m + 22 ∨ (lFE d m ≤ c ∧ c < lOFF d m)) ∧
      (∀ t < d, ∀ u < d, S'.mem (lFE d m + d * t + u) =
        if d = 1 then 1 / 4 * s.mem (lFE d m + d * t + u)
        else (d : ℝ) ^ 2 / ((d : ℝ) ^ 2 - 1) * (s.mem (lFE d m + d * t + u) -
          2 / ((d : ℝ) + 1) * (S4.mem (lFs d m + t) * S4.mem (lFs d m + u)))) := by
  have hFs : lFs d m = lW0 d m + 24 + m + d := rfl
  have hFa : lFa d m = lW0 d m + 24 + m := rfl
  have hFE : lFE d m = lFs d m + d + 2 := rfl
  have hOFF : lOFF d m = lFE d m + d * d := rfl
  have g4 : ∀ x, ¬ cutR r x → S4.nreg x = s.nreg x := fun x h => f4.1 x h
  have nR : ∀ x, x < r + 48 ∨ (r + 52 < x ∧ x ≠ r + 59 ∧ x ≠ r + 61) → ¬ cutR r x := fun x h => by
    unfold cutR; omega
  have c4 : ∀ c, c < lW0 d m + 13 ∨ (lW0 d m + 21 < c ∧ c < lFa d m) ∨ lFs d m + d ≤ c → S4.mem c = s.mem c :=
    fun c h => f4.2.1 c (fun h' => by rcases h' with h' | h' | h' | h' <;> omega)
  have e : ∀ x < 24, S4.nreg (r + 21 + x) = lW0 d m + x := fun x hx =>
    (g4 _ (nR _ (by omega))).trans (hc.sc x hx)
  have e1 : S4.nreg (r + 1) = d := (g4 _ (nR _ (by omega))).trans hc.dd
  have e60 : S4.nreg (r + 60) = 2 := (g4 _ (nR _ (by omega))).trans hc.two
  have e45 : S4.nreg (r + 45) = lFE d m := (g4 _ (nR _ (by omega))).trans hc.fE
  by_cases hd : d < 2
  · have hcn : condN S4 (r + 1) (r + 60) := by simp only [condN, e1, e60]; exact hd
    have e25 : S4.nreg (r + 25) = lW0 d m + 4 := e 4 (by norm_num)
    have hE0 : S4.mem (lFE d m) = s.mem (lFE d m) := c4 _ (by omega)
    have hx := Exec.ifN_t (c₂ := .seq (prims [.nadd (r + 59) (r + 45) (r + 10), .nconst (r + 48) 0])
      (.whileN (r + 48) (r + 1) (r1Outer r))) hcn (Exec.prim (w := w) (.op2 .mul (r + 45) (r + 25) (r + 45)) S4)
    refine ⟨_, _, by omega, hx, ⟨fun x _ => rfl, fun c hc' => ?_, rfl, rfl, rfl⟩, fun t ht u hu => ?_⟩
    · simp only [Prim.exec, Op2.eval, e45, e25, Function.update_apply]
      split_ifs with h
      · subst h
        have hd0 : d = 0 := by
          by_contra h0
          exact hc' (Or.inr (Or.inr ⟨le_refl _, by rw [hOFF]; have : 0 < d * d := Nat.mul_pos (by omega) (by omega); omega⟩))
        have hz : s.mem (lFE d m) = 0 := hc.high _ (by rw [hOFF, hd0]; simp)
        rw [hE0, hz, mul_zero]
      · rfl
    · have hd1 : d = 1 := by omega
      have ht0 : t = 0 := by omega
      have hu0 : u = 0 := by omega
      subst ht0 hu0
      rw [if_pos hd1]
      simp only [Prim.exec, Op2.eval, e45, e25, Function.update_apply, mul_zero, add_zero, if_true]
      rw [c4 _ (by omega), hc.k4, hE0]
  · have hcn : ¬ condN S4 (r + 1) (r + 60) := by simp only [condN, e1, e60]; exact hd
    obtain ⟨S5, hS5⟩ : ∃ S5, S5 = [Prim.nadd (r + 59) (r + 45) (r + 10), .nconst (r + 48) 0].foldl
        (fun s p => p.exec w s) S4 := ⟨_, rfl⟩
    have x5 := exec_prims w [Prim.nadd (r + 59) (r + 45) (r + 10), .nconst (r + 48) 0] S4
    rw [← hS5] at x5
    have e10 : S4.nreg (r + 10) = 0 := (g4 _ (nR _ (by omega))).trans hc.zero
    have n5 : ∀ x, S5.nreg x = if x = r + 48 then 0 else if x = r + 59 then lFE d m else S4.nreg x := fun x => by
      subst hS5
      simp only [List.foldl, Prim.exec, Function.update_apply, e45, e10, add_zero]
    have q : ∀ x, x ≠ r + 48 → x ≠ r + 59 → S5.nreg x = S4.nreg x := fun x a b => by rw [n5, if_neg a, if_neg b]
    have m5 : S5.mem = S4.mem := by subst hS5; rfl
    have d5 : S5.draws = S4.draws ∧ S5.rounds = S4.rounds ∧ S5.pts = S4.pts := by subst hS5; exact ⟨rfl, rfl, rfl⟩
    obtain ⟨k, S', hk, xL, hv, fL⟩ := r1Loop_exec (w := w) (r := r) (W := lW0 d m) (Fs := lFs d m)
      (FE := lFE d m) (S := S5) ((q _ (by omega) (by omega)).trans e1)
      ((q _ (by omega) (by omega)).trans ((g4 _ (nR _ (by omega))).trans hc.fs))
      ((q _ (by omega) (by omega)).trans ((g4 _ (nR _ (by omega))).trans hc.one))
      ((q _ (by omega) (by omega)).trans (e 6 (by norm_num))) ((q _ (by omega) (by omega)).trans (e 7 (by norm_num)))
      ((q _ (by omega) (by omega)).trans (e 21 (by norm_num))) ((q _ (by omega) (by omega)).trans (e 22 (by norm_num)))
      (by rw [n5]; simp) (by rw [n5]; simp) (by omega) (by omega)
    refine ⟨_, S', ?_, Exec.ifN_f hcn (Exec.seq x5 xL), ?_, fun t ht u hu => ?_⟩
    · simp only [List.length_cons, List.length_nil]; omega
    · refine Fr.trans ⟨fun x hx => q x (fun h => hx (Or.inl ⟨by omega, by omega⟩)) (fun h => hx (Or.inr (Or.inl h))),
        fun c _ => by rw [m5], d5.1, d5.2.1, d5.2.2⟩ (fL.mono (fun x hx => ?_) (fun c hc' => ?_))
      · unfold cutR; omega
      · rcases hc' with h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr ⟨h.1, by rw [hOFF]; exact h.2⟩)
    · have hd1 : d ≠ 1 := by omega
      have htu : d * t + u < d * d := by nlinarith
      rw [hv t ht u hu, if_neg hd1, m5, c4 (lW0 d m + 6) (by omega), c4 (lW0 d m + 7) (by omega), hc.k6, hc.k7,
        c4 (lFE d m + d * t + u) (by omega)]

/-- `E g` read from the cells: the row `i` of the data sits at `3 + (d + 1) i`. -/
theorem cut_mulVec {r n m : ℕ} {δ : ℝ} {Am : Matrix (Fin m) (Fin d) ℚ} {bv : Fin m → ℚ} {s : State d}
    (hc : PCtx r n m δ Am bv s) (i : Fin m) (t : Fin d) :
    (rdMat s (lFE d m) *ᵥ rowR Am i) t = cutV s m (3 + (d + 1) * i) t := by
  simp only [Matrix.mulVec, dotProduct, rdMat, rowR, cutV]
  rw [← Fin.sum_univ_eq_sum_range (fun l => s.mem (lFE d m + d * t + l) * s.mem (3 + (d + 1) * i + l)) d]
  exact Finset.sum_congr rfl (fun l _ => by rw [hc.cellA i l])

/-- `⟨g, E g⟩` read from the cells. -/
theorem cut_dot {r n m : ℕ} {δ : ℝ} {Am : Matrix (Fin m) (Fin d) ℚ} {bv : Fin m → ℚ} {s : State d}
    (hc : PCtx r n m δ Am bv s) (i : Fin m) :
    rowR Am i ⬝ᵥ (rdMat s (lFE d m) *ᵥ rowR Am i) = cutG s m (3 + (d + 1) * i) := by
  rw [cutG, ← Fin.sum_univ_eq_sum_range (fun t => s.mem (3 + (d + 1) * i + t) * cutV s m (3 + (d + 1) * i) t) d]
  simp only [dotProduct]
  exact Finset.sum_congr rfl (fun t _ => by rw [cut_mulVec hc i t, hc.cellA i t, rowR])

theorem cut_exec {w : World d} {r n m : ℕ} {δ : ℝ} {Am : Matrix (Fin m) (Fin d) ℚ} {bv : Fin m → ℚ}
    {s : State d} (hc : PCtx r n m δ Am bv s) (i : Fin m) (hg : s.nreg (r + 54) = 3 + (d + 1) * i) :
    ∃ k s', k ≤ 40 * (d + 1) * (d + 1) ∧ Exec w (cutCmd r) s k s' ∧ Fr s s' (cutR r) (cutC d m) ∧
      rdMat s' (lFE d m) = (cutUpdate (rdMat s (lFE d m)) (rdVec s (lFa d m)) (rowR Am i)).1 ∧
      rdVec s' (lFa d m) = (cutUpdate (rdMat s (lFE d m)) (rdVec s (lFa d m)) (rowR Am i)).2 := by
  have hFa : lFa d m = lW0 d m + 24 + m := rfl
  have hFs : lFs d m = lFa d m + d := rfl
  have hFE : lFE d m = lFs d m + d + 2 := rfl
  have hOFF : lOFF d m = lFE d m + d * d := rfl
  have hgW : 3 + (d + 1) * i + d ≤ lW0 d m := by have := row_end_lt (d := d) i.2; unfold lW0; omega
  obtain ⟨S1, S2, k2, hk2, x1, x2, hv, hγ, f2⟩ := cutA1_exec (w := w) hc hg hgW
  obtain ⟨S3, S4, k4, hk4, x3, x4, hb, ha, f4⟩ := cutA2_exec (w := w) hc f2
  have f4' : Fr s S4 (cutR r) (fun c => c = lW0 d m + 13 ∨ c = lW0 d m + 15 ∨
      (lW0 d m + 19 ≤ c ∧ c ≤ lW0 d m + 21) ∨ (lFa d m ≤ c ∧ c < lFs d m + d)) := by
    refine Fr.trans (f2.mono (fun x hx => ?_) (fun c hc' => ?_)) (f4.mono (fun x hx => ?_) (fun c hc' => ?_))
    · beta_reduce at hx ⊢; unfold cutR; omega
    · beta_reduce at hc' ⊢; omega
    · beta_reduce at hx ⊢; unfold cutR; omega
    · beta_reduce at hc' ⊢; omega
  obtain ⟨k5, S', hk5, x5, f5, hE⟩ := cutB_exec (w := w) hc f4'
  have hb' : ∀ t < d, S4.mem (lFs d m + t) =
      (Real.sqrt (cutG s m (3 + (d + 1) * i)))⁻¹ * cutV s m (3 + (d + 1) * i) t := fun t ht => by
    rw [hb t ht, hγ, hv t ht, one_div]
  refine ⟨_, S', ?_, Exec.seq x1 (Exec.seq x2 (Exec.seq x3 (Exec.seq x4 x5))), ?_, ?_, ?_⟩
  · nlinarith
  · refine Fr.trans (f4'.mono (fun x hx => hx) (fun c hc' => ?_)) (f5.mono (fun x hx => hx) (fun c hc' => ?_))
    · beta_reduce at hc'; unfold cutC; omega
    · beta_reduce at hc'; unfold cutC; omega
  · ext t u
    show S'.mem (lFE d m + d * t + u) = _
    rw [hE t t.2 u u.2]
    by_cases hd1 : d = 1
    · rw [if_pos hd1]
      unfold cutUpdate
      rw [if_pos hd1]
      simp only [Matrix.smul_apply, smul_eq_mul, rdMat]
    · rw [if_neg hd1]
      unfold cutUpdate
      rw [if_neg hd1]
      simp only [ccUpdate, Matrix.smul_apply, Matrix.sub_apply, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul,
        cut_dot hc i, cut_mulVec hc i, rdMat]
      rw [hb' t t.2, hb' u u.2]
  · ext t
    show S'.mem (lFa d m + t) = _
    have h2 : (cutUpdate (rdMat s (lFE d m)) (rdVec s (lFa d m)) (rowR Am i)).2 =
        (ccUpdate (rdMat s (lFE d m)) (rdVec s (lFa d m)) (rowR Am i)).2 := by
      unfold cutUpdate; split_ifs <;> rfl
    have ht := t.2
    rw [h2, f5.2.1 _ (by beta_reduce; omega), ha t t.2, hγ, hv t t.2]
    simp only [ccUpdate, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, cut_dot hc i, cut_mulVec hc i, rdVec, one_div]

/-! ## A stage -/

/-- The registers and cells of a test and its cut. -/
def iterR (r i : ℕ) : Prop := (r + 48 ≤ i ∧ i ≤ r + 54) ∨ i = r + 56 ∨ i = r + 57 ∨ i = r + 59 ∨ i = r + 61

def iterC (d m c : ℕ) : Prop :=
  (lW0 d m + 12 ≤ c ∧ c ≤ lW0 d m + 22) ∨ (lFa d m ≤ c ∧ c < lFs d m + d) ∨ (lFE d m ≤ c ∧ c < lOFF d m)

/-- A row has positive norm exactly when it is not zero. -/
theorem rowNorm_pos_iff {m : ℕ} (Am : Matrix (Fin m) (Fin d) ℚ) (i : Fin m) : 0 < rowNorm Am i ↔ rowR Am i ≠ 0 := by
  rw [rowNorm, Real.sqrt_pos]
  constructor
  · intro h hz
    have : ∑ j, (Am i j : ℝ) ^ 2 = 0 := Finset.sum_eq_zero (fun j _ => by
      have := congrFun hz j
      simp only [rowR, Pi.zero_apply] at this
      rw [this]; ring)
    linarith
  · intro h
    obtain ⟨j, hj⟩ := Function.ne_iff.1 h
    refine Finset.sum_pos' (fun j _ => sq_nonneg _) ⟨j, Finset.mem_univ _, ?_⟩
    simp only [rowR, Pi.zero_apply] at hj
    positivity

/-- The registers and scalar cells that a test keeps, read after it. -/
theorem iter_regs {r n m : ℕ} {δ : ℝ} {Am : Matrix (Fin m) (Fin d) ℚ} {bv : Fin m → ℚ} {s S1 : State d}
    (hc : PCtx r n m δ Am bv s) (f1 : Fr s S1 (testR r) (testC d m)) :
    S1.nreg (r + 9) = 1 ∧ S1.nreg (r + 10) = 0 ∧ S1.nreg (r + 21) = lW0 d m ∧ S1.nreg (r + 32) = lW0 d m + 11 ∧
      S1.nreg (r + 33) = lW0 d m + 12 ∧ S1.nreg (r + 39) = lW0 d m + 18 ∧ S1.nreg (r + 56) = s.nreg (r + 56) ∧
      S1.nreg (r + 57) = s.nreg (r + 57) ∧ S1.mem (lW0 d m) = 0 ∧
      S1.mem (lW0 d m + 11) = s.mem (lW0 d m + 11) := by
  have g1 : ∀ x, x < r + 48 ∨ (r + 54 < x ∧ x ≠ r + 61) → S1.nreg x = s.nreg x := fun x h =>
    f1.1 x (by unfold testR; omega)
  have c1 : ∀ c, c < lW0 d m + 13 → S1.mem c = s.mem c := fun c h => f1.2.1 c (by unfold testC; omega)
  have esc : ∀ x < 24, S1.nreg (r + 21 + x) = lW0 d m + x := fun x hx => (g1 _ (by omega)).trans (hc.sc x hx)
  exact ⟨(g1 _ (by omega)).trans hc.one, (g1 _ (by omega)).trans hc.zero, by simpa using esc 0 (by norm_num),
    esc 11 (by norm_num), esc 12 (by norm_num), esc 18 (by norm_num), g1 _ (by omega), g1 _ (by omega),
    (c1 _ (by omega)).trans hc.k0, c1 _ (by omega)⟩

/-- A test where every row passes: `status ← 1`, the count to `Y`. -/
theorem iter_none {w : World d} {r n m : ℕ} {δ : ℝ} {Am : Matrix (Fin m) (Fin d) ℚ} {bv : Fin m → ℚ}
    {s S1 : State d} {k1 : ℕ} (hc : PCtx r n m δ Am bv s) (x1 : Exec w (testCmd r) s k1 S1)
    (f1 : Fr s S1 (testR r) (testC d m)) (h53 : S1.nreg (r + 53) = 1) :
    ∃ S', Exec w (iterCmd r) s (k1 + 3) S' ∧ Fr S1 S' (fun x => x = r + 56) (fun c => c = lW0 d m + 12) ∧
      S'.nreg (r + 56) = 1 ∧ S'.mem (lW0 d m + 12) = s.mem (lW0 d m + 11) + 0 := by
  obtain ⟨-, e10, e21, e32, e33, -, -, -, m0, m11⟩ := iter_regs hc f1
  have hcn : condN S1 (r + 10) (r + 53) := by simp only [condN, e10, h53]; omega
  have x2 := exec_prims w [Prim.nconst (r + 56) 1, .op2 .add (r + 33) (r + 32) (r + 21)] S1
  refine ⟨_, Exec.seq x1 (Exec.ifN_t hcn x2), ⟨fun x hx => ?_, fun c hc' => ?_, rfl, rfl, rfl⟩, ?_, ?_⟩
  · simp only [List.foldl, Prim.exec, Function.update_apply, if_neg hx]
  · simp [List.foldl, Prim.exec, Function.update_apply, e33, hc']
  · simp [List.foldl, Prim.exec, Function.update_apply]
  · simp [List.foldl, Prim.exec, Op2.eval, Function.update_apply, e33, e32, e21, m0, m11]

/-- A test that fails on a zero row: the count to `Y`. -/
theorem iter_zero {w : World d} {r n m : ℕ} {δ : ℝ} {Am : Matrix (Fin m) (Fin d) ℚ} {bv : Fin m → ℚ}
    {s S1 : State d} {k1 : ℕ} (hc : PCtx r n m δ Am bv s) (x1 : Exec w (testCmd r) s k1 S1)
    (f1 : Fr s S1 (testR r) (testC d m)) (h53 : S1.nreg (r + 53) = 0) {i : Fin m}
    (h18 : S1.mem (lW0 d m + 18) = rowNorm Am i) (hz : rowR Am i = 0) :
    ∃ S', Exec w (iterCmd r) s (k1 + 5) S' ∧ Fr S1 S' (fun _ => False) (fun c => c = lW0 d m + 12) ∧
      S'.mem (lW0 d m + 12) = s.mem (lW0 d m + 11) + 0 := by
  obtain ⟨-, e10, e21, e32, e33, e39, -, -, m0, m11⟩ := iter_regs hc f1
  have hcn : ¬ condN S1 (r + 10) (r + 53) := by simp only [condN, e10, h53]; omega
  have hcr : ¬ condR S1 (r + 21) (r + 39) := by
    simp only [condR, e21, e39, m0, h18]
    exact fun h => (rowNorm_pos_iff Am i).1 h hz
  have x2 := Exec.prim (w := w) (.op2 .add (r + 33) (r + 32) (r + 21)) S1
  refine ⟨_, Exec.seq x1 (Exec.ifN_f hcn (Exec.ifR_f hcr x2)), ⟨fun x _ => rfl, fun c hc' => ?_, rfl, rfl, rfl⟩, ?_⟩
  · simp only [Prim.exec, Function.update_apply, e33, if_neg hc']
  · simp [Prim.exec, Op2.eval, Function.update_apply, e33, e32, e21, m0, m11]

/-- A test that fails on a row of positive norm: the cut, then the count `+1`. -/
theorem iter_cut {w : World d} {r n m : ℕ} {δ : ℝ} {Am : Matrix (Fin m) (Fin d) ℚ} {bv : Fin m → ℚ}
    {s S1 : State d} {k1 : ℕ} (hc : PCtx r n m δ Am bv s) (x1 : Exec w (testCmd r) s k1 S1)
    (f1 : Fr s S1 (testR r) (testC d m)) (h53 : S1.nreg (r + 53) = 0) {i : Fin m}
    (h54 : S1.nreg (r + 54) = 3 + (d + 1) * i) (h18 : S1.mem (lW0 d m + 18) = rowNorm Am i) (hz : rowR Am i ≠ 0) :
    ∃ k S', k ≤ 40 * (d + 1) * (d + 1) + 5 ∧ Exec w (iterCmd r) s (k1 + k) S' ∧
      Fr S1 S' (fun x => cutR r x ∨ x = r + 57) (fun c => cutC d m c ∨ c = lW0 d m + 12) ∧
      S'.nreg (r + 57) = s.nreg (r + 57) + 1 ∧ S'.mem (lW0 d m + 12) = ((s.nreg (r + 57) + 1 : ℕ) : ℝ) ∧
      rdMat S' (lFE d m) = (cutUpdate (rdMat S1 (lFE d m)) (rdVec S1 (lFa d m)) (rowR Am i)).1 ∧
      rdVec S' (lFa d m) = (cutUpdate (rdMat S1 (lFE d m)) (rdVec S1 (lFa d m)) (rowR Am i)).2 := by
  obtain ⟨e9, e10, e21, -, e33, e39, -, e57, m0, -⟩ := iter_regs hc f1
  have hFa : lFa d m = lW0 d m + 24 + m := rfl
  have hFs : lFs d m = lFa d m + d := rfl
  have hFE : lFE d m = lFs d m + d + 2 := rfl
  have hOFF : lOFF d m = lFE d m + d * d := rfl
  have hcn : ¬ condN S1 (r + 10) (r + 53) := by simp only [condN, e10, h53]; omega
  have hcr : condR S1 (r + 21) (r + 39) := by
    simp only [condR, e21, e39, m0, h18]
    exact (rowNorm_pos_iff Am i).2 hz
  have hc1 : PCtx r n m δ Am bv S1 := pctx_of_fr hc (f1.mono
    (fun x hx => by unfold testR at hx; unfold MutR; omega) (fun c hc' => by unfold testC at hc'; unfold MutC; omega))
  obtain ⟨k2, S2, hk2, x2, f2, hE, hA⟩ := cut_exec (w := w) hc1 i h54
  have g2 : ∀ x, ¬ cutR r x → S2.nreg x = S1.nreg x := fun x h => f2.1 x h
  have f9 : S2.nreg (r + 9) = 1 := (g2 _ (by unfold cutR; omega)).trans e9
  have f33 : S2.nreg (r + 33) = lW0 d m + 12 := (g2 _ (by unfold cutR; omega)).trans e33
  have f57 : S2.nreg (r + 57) = s.nreg (r + 57) := (g2 _ (by unfold cutR; omega)).trans e57
  obtain ⟨S3, hS3⟩ : ∃ S3, S3 = [Prim.nadd (r + 57) (r + 57) (r + 9), .ncast (r + 33) (r + 57)].foldl
      (fun s p => p.exec w s) S2 := ⟨_, rfl⟩
  have x3 := exec_prims w [Prim.nadd (r + 57) (r + 57) (r + 9), .ncast (r + 33) (r + 57)] S2
  rw [← hS3] at x3
  have n3 : ∀ x, S3.nreg x = if x = r + 57 then s.nreg (r + 57) + 1 else S2.nreg x := fun x => by
    subst hS3; simp only [List.foldl, Prim.exec, Function.update_apply, f57, f9]
  have m3 : ∀ c, S3.mem c = if c = lW0 d m + 12 then ((s.nreg (r + 57) + 1 : ℕ) : ℝ) else S2.mem c := fun c => by
    subst hS3
    simp only [List.foldl, Prim.exec, Function.update_apply, f57, f9, f33, show r + 33 ≠ r + 57 by omega, ↓reduceIte]
  have d3 : S3.draws = S2.draws ∧ S3.rounds = S2.rounds ∧ S3.pts = S2.pts := by subst hS3; exact ⟨rfl, rfl, rfl⟩
  refine ⟨k2 + 5, S3, by omega, (Exec.seq x1 (Exec.ifN_f hcn (Exec.ifR_t hcr (Exec.seq x2 x3)))).cost
    (by simp), ?_, ?_, ?_, ?_, ?_⟩
  · refine (f2.mono (fun x hx => Or.inl hx) (fun c hc' => Or.inl hc')).trans
      ⟨fun x hx => ?_, fun c hc' => ?_, d3.1, d3.2.1, d3.2.2⟩
    · rw [n3, if_neg (fun h => hx (Or.inr h))]
    · rw [m3, if_neg (fun h => hc' (Or.inr h))]
  · rw [n3, if_pos rfl]
  · rw [m3, if_pos rfl]
  · rw [← hE]; ext a b
    have := a.2; have := b.2
    show S3.mem _ = S2.mem _
    rw [m3, if_neg (by omega)]
  · rw [← hA]; funext j
    have := j.2
    show S3.mem _ = S2.mem _
    rw [m3, if_neg (by omega)]

/-- One turn of a stage: the test, then the exit with `status = 1` on success, the cut and the next count on a
failing row of positive norm, the exit on a failing zero row. -/
theorem iter_exec {w : World d} {r n m : ℕ} {δ : ℝ} {Am : Matrix (Fin m) (Fin d) ℚ} {bv : Fin m → ℚ}
    {s : State d} (hc : PCtx r n m δ Am bv s) :
    ∃ k s', k ≤ 70 * (d + 1) * (d + 1) * (m + 1) ∧ Exec w (iterCmd r) s k s' ∧ Fr s s' (iterR r) (iterC d m) ∧
      (firstFail Am bv (1 / 2) (rdVec s (lFa d m)) = none →
        s'.nreg (r + 56) = 1 ∧ s'.mem (lW0 d m + 12) = s.mem (lW0 d m + 11) + 0 ∧
          rdVec s' (lFa d m) = rdVec s (lFa d m)) ∧
      (∀ i, firstFail Am bv (1 / 2) (rdVec s (lFa d m)) = some i → rowR Am i ≠ 0 →
        s'.nreg (r + 56) = s.nreg (r + 56) ∧ s'.nreg (r + 57) = s.nreg (r + 57) + 1 ∧
          s'.mem (lW0 d m + 12) = ((s.nreg (r + 57) + 1 : ℕ) : ℝ) ∧
          rdMat s' (lFE d m) = (cutUpdate (rdMat s (lFE d m)) (rdVec s (lFa d m)) (rowR Am i)).1 ∧
          rdVec s' (lFa d m) = (cutUpdate (rdMat s (lFE d m)) (rdVec s (lFa d m)) (rowR Am i)).2) ∧
      (∀ i, firstFail Am bv (1 / 2) (rdVec s (lFa d m)) = some i → rowR Am i = 0 →
        s'.nreg (r + 56) = s.nreg (r + 56) ∧ s'.mem (lW0 d m + 12) = s.mem (lW0 d m + 11) + 0) := by
  have hFa : lFa d m = lW0 d m + 24 + m := rfl
  have hFs : lFs d m = lFa d m + d := rfl
  have hFE : lFE d m = lFs d m + d + 2 := rfl
  have hOFF : lOFF d m = lFE d m + d * d := rfl
  obtain ⟨k1, S1, hk1, x1, f1, hnone, hsome⟩ := test_exec (w := w) hc
  have c1 : ∀ c, c < lW0 d m + 13 ∨ lW0 d m + 18 < c → S1.mem c = s.mem c := fun c h =>
    f1.2.1 c (by unfold testC; omega)
  have vFa : rdVec S1 (lFa d m) = rdVec s (lFa d m) := funext fun j => c1 _ (by have := j.2; omega)
  have mFE : rdMat S1 (lFE d m) = rdMat s (lFE d m) := by ext a b; exact c1 _ (by omega)
  have e56 := (iter_regs hc f1).2.2.2.2.2.2.1
  have hbig : 20 * (d + 1) * (m + 1) + (40 * (d + 1) * (d + 1) + 5) ≤ 70 * (d + 1) * (d + 1) * (m + 1) := by
    nlinarith [Nat.zero_le (d * m), Nat.zero_le (d * d * m)]
  have fT : ∀ x, testR r x → iterR r x := fun x hx => by unfold testR at hx; unfold iterR; omega
  have cT : ∀ c, testC d m c → iterC d m c := fun c hc' => by unfold testC at hc'; unfold iterC; omega
  cases hF : firstFail Am bv (1 / 2) (rdVec s (lFa d m)) with
  | none =>
    obtain ⟨S', x, f, h56, h12⟩ := iter_none hc x1 f1 (hnone hF)
    refine ⟨_, S', by omega, x, (f1.mono fT cT).trans (f.mono (fun x hx => ?_) (fun c hc' => ?_)),
      fun _ => ⟨h56, h12, ?_⟩, fun i hi => by simp at hi, fun i hi => by simp at hi⟩
    · beta_reduce at hx; unfold iterR; omega
    · beta_reduce at hc'; unfold iterC; omega
    · rw [← vFa]; funext j; have := j.2; exact f.2.1 _ (by beta_reduce; omega)
  | some i =>
    obtain ⟨h53, h54, h18⟩ := hsome i hF
    by_cases hz : rowR Am i = 0
    · obtain ⟨S', x, f, h12⟩ := iter_zero hc x1 f1 h53 h18 hz
      refine ⟨_, S', by omega, x, (f1.mono fT cT).trans (f.mono (fun x hx => hx.elim) (fun c hc' => ?_)),
        fun h => by simp at h, fun i' hi' hne => absurd ((Option.some_injective _ hi') ▸ hz) hne,
        fun i' _ _ => ⟨(f.1 _ id).trans e56, h12⟩⟩
      beta_reduce at hc'; unfold iterC; omega
    · obtain ⟨k, S', hk, x, f, h57, h12, hE, hA⟩ := iter_cut hc x1 f1 h53 h54 h18 hz
      refine ⟨_, S', by omega, x, (f1.mono fT cT).trans (f.mono (fun x hx => ?_) (fun c hc' => ?_)),
        fun h => by simp at h, fun i' hi' _ => ?_, fun i' hi' h' => absurd ((Option.some_injective _ hi') ▸ h') hz⟩
      · beta_reduce at hx; unfold cutR at hx; unfold iterR; omega
      · beta_reduce at hc'; unfold cutC at hc'; unfold iterC; omega
      · obtain rfl : i = i' := Option.some_injective _ hi'
        refine ⟨(f.1 _ (fun h => by unfold cutR at h; omega)).trans e56, h57, h12, ?_, ?_⟩
        · rw [hE, mFE, vFa]
        · rw [hA, mFE, vFa]

/-- The loop of a stage: from the count `0` and `status = 0`, it returns `centreRun` with `⌈Y⌉` tests. -/
theorem stageLoop_exec {w : World d} {r n m : ℕ} {δ : ℝ} {Am : Matrix (Fin m) (Fin d) ℚ} {bv : Fin m → ℚ}
    {s : State d} (hc : PCtx r n m δ Am bv s) (h56 : s.nreg (r + 56) = 0) (h57 : s.nreg (r + 57) = 0)
    (h12 : s.mem (lW0 d m + 12) = 0) :
    ∃ k s', k ≤ ⌈s.mem (lW0 d m + 11)⌉₊ * (70 * (d + 1) * (d + 1) * (m + 1) + 2) + 2 ∧
      Exec w (.whileR (r + 33) (r + 32) (iterCmd r)) s k s' ∧ Fr s s' (iterR r) (iterC d m) ∧
      ((s'.nreg (r + 56) = 1 ∧ centreRun Am bv (1 / 2) ⌈s.mem (lW0 d m + 11)⌉₊ (rdMat s (lFE d m))
          (rdVec s (lFa d m)) = some (rdVec s' (lFa d m))) ∨
        (s'.nreg (r + 56) = 0 ∧ centreRun Am bv (1 / 2) ⌈s.mem (lW0 d m + 11)⌉₊ (rdMat s (lFE d m))
          (rdVec s (lFa d m)) = none)) := by
  have hFa : lFa d m = lW0 d m + 24 + m := rfl
  have hFs : lFs d m = lFa d m + d := rfl
  have hFE : lFE d m = lFs d m + d + 2 := rfl
  have hOFF : lOFF d m = lFE d m + d * d := rfl
  set Y := s.mem (lW0 d m + 11) with hY
  set N := ⌈Y⌉₊ with hN
  set C0 := centreRun Am bv (1 / 2) N (rdMat s (lFE d m)) (rdVec s (lFa d m)) with hC0
  have hRM : ∀ x, iterR r x → MutR r x := fun x hx => by unfold iterR at hx; unfold MutR; omega
  have hCM : ∀ c, iterC d m c → MutC d m c := fun c hc' => by unfold iterC at hc'; unfold MutC; omega
  let I : ℕ → State d → Prop := fun t S => Fr s S (iterR r) (iterC d m) ∧
    ((S.nreg (r + 56) = 0 ∧ S.nreg (r + 57) = t ∧ S.mem (lW0 d m + 12) = (t : ℝ) ∧
        C0 = centreRun Am bv (1 / 2) (N - t) (rdMat S (lFE d m)) (rdVec S (lFa d m))) ∨
      (S.nreg (r + 56) = 1 ∧ C0 = some (rdVec S (lFa d m)) ∧ S.mem (lW0 d m + 12) = Y + 0) ∨
      (S.nreg (r + 56) = 0 ∧ C0 = none ∧ S.mem (lW0 d m + 12) = Y + 0))
  have hctx : ∀ S, Fr s S (iterR r) (iterC d m) → PCtx r n m δ Am bv S := fun S f =>
    pctx_of_fr hc (f.mono hRM hCM)
  have hcond : ∀ S, Fr s S (iterR r) (iterC d m) →
      (condR S (r + 33) (r + 32) ↔ S.mem (lW0 d m + 12) < Y) := fun S f => by
    have hS := hctx S f
    have e12 : S.nreg (r + 33) = lW0 d m + 12 := hS.sc 12 (by norm_num)
    have e11 : S.nreg (r + 32) = lW0 d m + 11 := hS.sc 11 (by norm_num)
    have m11 : S.mem (lW0 d m + 11) = Y := f.2.1 _ (by unfold iterC; omega)
    simp only [condR, e12, e11, m11]
  have hbound : ∀ t S, I t S → condR S (r + 33) (r + 32) → t < N := by
    rintro t S ⟨f, ⟨-, -, h12', -⟩ | ⟨-, -, h12'⟩ | ⟨-, -, h12'⟩⟩ hcn <;> rw [hcond S f, h12'] at hcn
    · exact Nat.lt_ceil.2 hcn
    · simp at hcn
    · simp at hcn
  have hbody : ∀ t S, I t S → condR S (r + 33) (r + 32) →
      ∃ k S', k ≤ 70 * (d + 1) * (d + 1) * (m + 1) ∧ Exec w (iterCmd r) S k S' ∧ I (t + 1) S' := by
    intro t S hI hcn
    have htN := hbound t S hI hcn
    obtain ⟨f, ⟨g56, g57, g12, gC⟩ | ⟨-, -, h12'⟩ | ⟨-, -, h12'⟩⟩ := hI
    · obtain ⟨k, S', hk, x, f', hn, hcut, hzero⟩ := iter_exec (w := w) (hctx S f)
      refine ⟨k, S', hk, x, f.trans f', ?_⟩
      have hNt : N - t = (N - (t + 1)) + 1 := by omega
      rw [hNt] at gC
      cases hF : firstFail Am bv (1 / 2) (rdVec S (lFa d m)) with
      | none =>
        obtain ⟨a1, a2, a3⟩ := hn hF
        refine Or.inr (Or.inl ⟨a1, ?_, ?_⟩)
        · rw [gC, centreRun, hF, a3]
        · rw [a2, (f.2.1 _ (by unfold iterC; omega) : S.mem (lW0 d m + 11) = Y)]
      | some i =>
        by_cases hz : rowR Am i = 0
        · obtain ⟨a1, a2⟩ := hzero i hF hz
          refine Or.inr (Or.inr ⟨a1.trans g56, ?_, ?_⟩)
          · rw [gC, centreRun, hF]; simp [hz]
          · rw [a2, (f.2.1 _ (by unfold iterC; omega) : S.mem (lW0 d m + 11) = Y)]
        · obtain ⟨a1, a2, a3, a4, a5⟩ := hcut i hF hz
          refine Or.inl ⟨a1.trans g56, by rw [a2, g57], by rw [a3, g57], ?_⟩
          rw [gC, centreRun, hF]; simp only [hz, if_false, a4, a5]
    · rw [hcond S f, h12'] at hcn; simp at hcn
    · rw [hcond S f, h12'] at hcn; simp at hcn
  have hI0 : I 0 s := ⟨Fr.refl _ _ _, Or.inl ⟨h56, h57, by rw [h12]; simp, by simp [hC0]⟩⟩
  obtain ⟨k, S', t', hk, x, ⟨f, hst⟩, hnc⟩ := exec_whileR_inv (w := w) (a := r + 33) (b := r + 32) (c := iterCmd r)
    I N (70 * (d + 1) * (d + 1) * (m + 1)) hbound hbody 0 s hI0
  refine ⟨k, S', by simpa using hk, x, f, ?_⟩
  rcases hst with ⟨g56, -, g12, gC⟩ | ⟨g56, gC, -⟩ | ⟨g56, gC, -⟩
  · rw [hcond S' f, g12, not_lt] at hnc
    have : N - t' = 0 := by have := Nat.ceil_le.2 hnc; omega
    rw [this, centreRun] at gC
    exact Or.inr ⟨g56, gC⟩
  · exact Or.inl ⟨g56, gC⟩
  · exact Or.inr ⟨g56, gC⟩

/-- The bound on the steps of the stage `j`. -/
noncomputable def stageK (d m j : ℕ) : ℕ := (stageN d j + 1) * (100 * (d + 1) * (d + 1) * (m + 1))

/-- The registers and cells of a stage. -/
def stageR' (r i : ℕ) : Prop := (r + 48 ≤ i ∧ i ≤ r + 57) ∨ i = r + 59 ∨ i = r + 61

def stageC (d m c : ℕ) : Prop := MutC d m c

/-- The first primitives of a stage: `R²` and `Y = 2 d (d + 1) log (2 R) + 1`. -/
theorem stage_prims {w : World d} {r n m : ℕ} {δ : ℝ} {Am : Matrix (Fin m) (Fin d) ℚ} {bv : Fin m → ℚ}
    {s : State d} (hc : PCtx r n m δ Am bv s) :
    ∃ S1, Exec w (prims [.op2 .mul (r + 31) (r + 30) (r + 30), .op2 .mul (r + 42) (r + 24) (r + 30),
        .op1 .log (r + 42) (r + 42), .op2 .add (r + 43) (r + 26) (r + 23), .op2 .mul (r + 43) (r + 26) (r + 43),
        .op2 .mul (r + 43) (r + 24) (r + 43), .op2 .mul (r + 32) (r + 43) (r + 42), .op2 .add (r + 32) (r + 32) (r + 23)])
      s 8 S1 ∧
      Fr s S1 (fun _ => False) (fun c => c = lW0 d m + 10 ∨ c = lW0 d m + 11 ∨ c = lW0 d m + 21 ∨ c = lW0 d m + 22) ∧
      S1.mem (lW0 d m + 10) = s.mem (lW0 d m + 9) * s.mem (lW0 d m + 9) ∧
      S1.mem (lW0 d m + 11) = 2 * ((d : ℝ) * ((d : ℝ) + 1)) * Real.log (2 * s.mem (lW0 d m + 9)) + 1 := by
  have e : ∀ x < 24, s.nreg (r + 21 + x) = lW0 d m + x := hc.sc
  have e2 : s.nreg (r + 23) = lW0 d m + 2 := e 2 (by norm_num)
  have e3 : s.nreg (r + 24) = lW0 d m + 3 := e 3 (by norm_num)
  have e5 : s.nreg (r + 26) = lW0 d m + 5 := e 5 (by norm_num)
  have e9 : s.nreg (r + 30) = lW0 d m + 9 := e 9 (by norm_num)
  have e10 : s.nreg (r + 31) = lW0 d m + 10 := e 10 (by norm_num)
  have e11 : s.nreg (r + 32) = lW0 d m + 11 := e 11 (by norm_num)
  have e21 : s.nreg (r + 42) = lW0 d m + 21 := e 21 (by norm_num)
  have e22 : s.nreg (r + 43) = lW0 d m + 22 := e 22 (by norm_num)
  refine ⟨_, exec_prims w _ s, ⟨fun x _ => rfl, fun c hc' => ?_, rfl, rfl, rfl⟩, ?_, ?_⟩
  · have a1 : c ≠ lW0 d m + 10 := fun h => hc' (Or.inl h)
    have a2 : c ≠ lW0 d m + 11 := fun h => hc' (Or.inr (Or.inl h))
    have a3 : c ≠ lW0 d m + 21 := fun h => hc' (Or.inr (Or.inr (Or.inl h)))
    have a4 : c ≠ lW0 d m + 22 := fun h => hc' (Or.inr (Or.inr (Or.inr h)))
    simp only [List.foldl, Prim.exec, Function.update_apply, e10, e11, e21, e22, if_neg a1, if_neg a2, if_neg a3,
      if_neg a4]
  · simp [List.foldl, Prim.exec, Op2.eval, Function.update_apply, e9, e10, e11, e21, e22, e2, e3, e5]
  · simp [List.foldl, Prim.exec, Op1.eval, Op2.eval, Function.update_apply, e9, e10, e11, e21, e22, e2, e3, e5,
      hc.k2, hc.k3, hc.k5]

/-- A cell `d a + b` of the matrix lies on the diagonal `(d + 1) k` only for `a = b = k`. -/
theorem diag_cell {d a b k : ℕ} (hb : b < d) (hk : k < d) (h : d * a + b = (d + 1) * k) : a = k ∧ b = k := by
  have h' : d * a + b = d * k + k := by rw [h]; ring
  have hd : 0 < d := by omega
  have e1 : (d * a + b) / d = a := by rw [Nat.mul_add_div hd, Nat.div_eq_of_lt hb, add_zero]
  have e2 : (d * k + k) / d = k := by rw [Nat.mul_add_div hd, Nat.div_eq_of_lt hk, add_zero]
  have hak : a = k := by rw [← e1, h', e2]
  subst hak; omega

/-- The matrix after the fills: zero, then `v` on the diagonal. -/
theorem fill_mat {d FE : ℕ} {M2 M3 M5 : ℕ → ℝ} {v : ℝ} (h2 : ∀ k < d * d, M2 (FE + k) = 0)
    (h3 : ∀ k < d, M3 (FE + (d + 1) * k) = v) (h3' : ∀ c, (∀ k < d, c ≠ FE + (d + 1) * k) → M3 c = M2 c)
    (h5 : ∀ c, FE ≤ c → M5 c = M3 c) :
    ((fun a b : Fin d => M5 (FE + d * a + b)) : Matrix (Fin d) (Fin d) ℝ) = v • (1 : Matrix (Fin d) (Fin d) ℝ) := by
  ext a b
  have ha := a.2; have hb := b.2
  have hab : d * a + b < d * d := by nlinarith
  simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  rw [h5 _ (by omega)]
  by_cases h : a = b
  · subst h
    rw [if_pos rfl, mul_one, show FE + d * a + a = FE + (d + 1) * a by ring, h3 a a.2]
  · have hnd : ∀ k < d, FE + d * a + b ≠ FE + (d + 1) * k := fun k hk heq => by
      rw [add_assoc] at heq
      have := diag_cell b.2 hk (Nat.add_left_cancel heq)
      exact h (Fin.ext (this.1.trans this.2.symm))
    rw [if_neg h, mul_zero, h3' _ hnd, add_assoc, h2 _ hab]

/-- The fills of a stage: `E = R² I`, `a = 0`, then the count `0` and `status = 0`. -/
theorem stage_fill {w : World d} {r n m : ℕ} {δ : ℝ} {Am : Matrix (Fin m) (Fin d) ℚ} {bv : Fin m → ℚ}
    {s S1 : State d} (hc : PCtx r n m δ Am bv s)
    (f1 : Fr s S1 (fun _ => False)
      (fun c => c = lW0 d m + 10 ∨ c = lW0 d m + 11 ∨ c = lW0 d m + 21 ∨ c = lW0 d m + 22)) :
    ∃ S2 S3 S4 S5,
      Exec w (sfillCmd (r + 48) (r + 58) (r + 9) (r + 10) (r + 59) (r + 45) (r + 9) (r + 21) (r + 21)) S1
        (5 * (d * d) + 4) S2 ∧
      Exec w (sfillCmd (r + 48) (r + 1) (r + 9) (r + 10) (r + 59) (r + 45) (r + 47) (r + 31) (r + 21)) S2
        (5 * d + 4) S3 ∧
      Exec w (sfillCmd (r + 48) (r + 1) (r + 9) (r + 10) (r + 59) (r + 5) (r + 9) (r + 21) (r + 21)) S3
        (5 * d + 4) S4 ∧
      Exec w (prims [.nconst (r + 57) 0, .rconst (r + 33) 0, .nconst (r + 56) 0]) S4 3 S5 ∧
      Fr S1 S5 (fun x => x = r + 48 ∨ x = r + 56 ∨ x = r + 57 ∨ x = r + 59)
        (fun c => c = lW0 d m + 12 ∨ (lFa d m ≤ c ∧ c < lFa d m + d) ∨ (lFE d m ≤ c ∧ c < lOFF d m)) ∧
      S5.nreg (r + 56) = 0 ∧ S5.nreg (r + 57) = 0 ∧ S5.mem (lW0 d m + 12) = 0 ∧
      rdMat S5 (lFE d m) = S1.mem (lW0 d m + 10) • (1 : Matrix (Fin d) (Fin d) ℝ) ∧ rdVec S5 (lFa d m) = 0 := by
  have hFa : lFa d m = lW0 d m + 24 + m := rfl
  have hFs : lFs d m = lFa d m + d := rfl
  have hFE : lFE d m = lFs d m + d + 2 := rfl
  have hOFF : lOFF d m = lFE d m + d * d := rfl
  have g1 : ∀ x, S1.nreg x = s.nreg x := fun x => f1.1 x id
  have m0 : S1.mem (lW0 d m) = 0 := (f1.2.1 _ (by beta_reduce; omega)).trans hc.k0
  have s21 : s.nreg (r + 21) = lW0 d m := by simpa using hc.sc 0 (by norm_num)
  have s31 : s.nreg (r + 31) = lW0 d m + 10 := hc.sc 10 (by norm_num)
  have s33 : s.nreg (r + 33) = lW0 d m + 12 := hc.sc 12 (by norm_num)
  -- the first fill: the d² cells of E to 0
  obtain ⟨S2, x2, v2, f2⟩ := sfill_exec (w := w) (i := r + 48) (D := r + 58) (one := r + 9) (z := r + 10)
    (ptr := r + 59) (base := r + 45) (stride := r + 9) (src := r + 21) (zr := r + 21) S1 (by omega) (by omega)
    (by rw [g1]; exact hc.one) (by rw [g1]; exact hc.zero)
    (fun k hk => by simp only [g1, hc.fE, hc.one, s21, hc.d2] at hk ⊢; omega)
  simp only [g1, hc.d2, hc.fE, hc.one, s21, m0, add_zero, one_mul] at x2 v2 f2
  have q2 : ∀ x, x ≠ r + 48 → x ≠ r + 59 → S2.nreg x = s.nreg x := fun x a b =>
    (f2.1 x (by rintro (h | h) <;> contradiction)).trans (g1 x)
  have c2 : ∀ c, (c < lFE d m ∨ lOFF d m ≤ c) → S2.mem c = S1.mem c := fun c h =>
    f2.2.1 c (by rintro ⟨k, hk, rfl⟩; omega)
  have t1 : S2.nreg (r + 1) = d := (q2 _ (by omega) (by omega)).trans hc.dd
  have t9 : S2.nreg (r + 9) = 1 := (q2 _ (by omega) (by omega)).trans hc.one
  have t10 : S2.nreg (r + 10) = 0 := (q2 _ (by omega) (by omega)).trans hc.zero
  have t45 : S2.nreg (r + 45) = lFE d m := (q2 _ (by omega) (by omega)).trans hc.fE
  have t47 : S2.nreg (r + 47) = d + 1 := (q2 _ (by omega) (by omega)).trans hc.d1
  have t31 : S2.nreg (r + 31) = lW0 d m + 10 := (q2 _ (by omega) (by omega)).trans s31
  have t21 : S2.nreg (r + 21) = lW0 d m := (q2 _ (by omega) (by omega)).trans s21
  -- the second fill: the diagonal of E to R²
  have hdiag : ∀ k < d, (d + 1) * k < d * d := fun k hk => by nlinarith
  obtain ⟨S3, x3, v3, f3⟩ := sfill_exec (w := w) (i := r + 48) (D := r + 1) (one := r + 9) (z := r + 10)
    (ptr := r + 59) (base := r + 45) (stride := r + 47) (src := r + 31) (zr := r + 21) S2 (by omega) (by omega)
    t9 t10 (fun k hk => by
      simp only [t1, t45, t47, t31, t21] at hk ⊢
      have := hdiag k hk
      omega)
  simp only [t1, t45, t47, t31, t21] at x3 v3 f3
  rw [c2 _ (by omega), c2 _ (by omega), m0, add_zero] at v3
  have q3 : ∀ x, x ≠ r + 48 → x ≠ r + 59 → S3.nreg x = s.nreg x := fun x a b =>
    (f3.1 x (by rintro (h | h) <;> contradiction)).trans (q2 x a b)
  have c3 : ∀ c, (c < lFE d m ∨ lOFF d m ≤ c) → S3.mem c = S1.mem c := fun c h =>
    (f3.2.1 c (by rintro ⟨k, hk, rfl⟩; have := hdiag k hk; omega)).trans (c2 c h)
  have u1 : S3.nreg (r + 1) = d := (q3 _ (by omega) (by omega)).trans hc.dd
  have u9 : S3.nreg (r + 9) = 1 := (q3 _ (by omega) (by omega)).trans hc.one
  have u10 : S3.nreg (r + 10) = 0 := (q3 _ (by omega) (by omega)).trans hc.zero
  have u5 : S3.nreg (r + 5) = lFa d m := (q3 _ (by omega) (by omega)).trans hc.fa
  have u21 : S3.nreg (r + 21) = lW0 d m := (q3 _ (by omega) (by omega)).trans s21
  -- the third fill: a to 0
  obtain ⟨S4, x4, v4, f4⟩ := sfill_exec (w := w) (i := r + 48) (D := r + 1) (one := r + 9) (z := r + 10)
    (ptr := r + 59) (base := r + 5) (stride := r + 9) (src := r + 21) (zr := r + 21) S3 (by omega) (by omega)
    u9 u10 (fun k hk => by simp only [u1, u5, u9, u21] at hk ⊢; omega)
  simp only [u1, u5, u9, u21, one_mul] at x4 v4 f4
  rw [c3 _ (by omega), m0, add_zero] at v4
  have q4 : ∀ x, x ≠ r + 48 → x ≠ r + 59 → S4.nreg x = s.nreg x := fun x a b =>
    (f4.1 x (by rintro (h | h) <;> contradiction)).trans (q3 x a b)
  have c4 : ∀ c, lFa d m + d ≤ c → S4.mem c = S3.mem c := fun c h =>
    f4.2.1 c (by rintro ⟨k, hk, rfl⟩; omega)
  -- the count and the status
  have e33 : S4.nreg (r + 33) = lW0 d m + 12 := (q4 _ (by omega) (by omega)).trans s33
  obtain ⟨S5, hS5⟩ : ∃ S5, S5 = [Prim.nconst (r + 57) 0, .rconst (r + 33) 0, .nconst (r + 56) 0].foldl
      (fun s p => p.exec w s) S4 := ⟨_, rfl⟩
  have x5 := exec_prims w [Prim.nconst (r + 57) 0, .rconst (r + 33) 0, .nconst (r + 56) 0] S4
  rw [← hS5] at x5
  have n5 : ∀ x, S5.nreg x = if x = r + 56 then 0 else if x = r + 57 then 0 else S4.nreg x := fun x => by
    subst hS5; simp only [List.foldl, Prim.exec, Function.update_apply]
  have m5 : ∀ c, S5.mem c = if c = lW0 d m + 12 then 0 else S4.mem c := fun c => by
    subst hS5; simp only [List.foldl, Prim.exec, Function.update_apply, e33]
    split_ifs <;> simp_all
  have d5 : S5.draws = S4.draws ∧ S5.rounds = S4.rounds ∧ S5.pts = S4.pts := by subst hS5; exact ⟨rfl, rfl, rfl⟩
  refine ⟨S2, S3, S4, S5, x2, x3, x4, x5, ?_, by rw [n5, if_pos rfl], by rw [n5, if_neg (by omega), if_pos rfl],
    by rw [m5, if_pos rfl], ?_, ?_⟩
  · refine Fr.trans (f2.mono (fun x hx => ?_) (fun c hc' => ?_)) (Fr.trans (f3.mono (fun x hx => ?_)
      (fun c hc' => ?_)) (Fr.trans (f4.mono (fun x hx => ?_) (fun c hc' => ?_))
      ⟨fun x hx => ?_, fun c hc' => ?_, d5.1, d5.2.1, d5.2.2⟩))
    · rcases hx with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr (Or.inr h))
    · obtain ⟨k, hk, rfl⟩ := hc'; exact Or.inr (Or.inr ⟨by omega, by omega⟩)
    · rcases hx with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr (Or.inr h))
    · obtain ⟨k, hk, rfl⟩ := hc'; have := hdiag k hk; exact Or.inr (Or.inr ⟨by omega, by omega⟩)
    · rcases hx with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr (Or.inr h))
    · obtain ⟨k, hk, rfl⟩ := hc'; exact Or.inr (Or.inl ⟨by omega, by omega⟩)
    · rw [n5, if_neg (fun h => hx (Or.inr (Or.inl h))), if_neg (fun h => hx (Or.inr (Or.inr (Or.inl h))))]
    · rw [m5, if_neg (fun h => hc' (Or.inl h))]
  · have h3' : ∀ c, (∀ k < d, c ≠ lFE d m + (d + 1) * k) → S3.mem c = S2.mem c := fun c h =>
      f3.2.1 c (by rintro ⟨k, hk, rfl⟩; exact h k hk rfl)
    have h5 : ∀ c, lFE d m ≤ c → S5.mem c = S3.mem c := fun c h => by
      rw [m5, if_neg (by omega), c4 _ (by omega)]
    exact fill_mat v2 v3 h3' h5
  · funext j
    have hj := j.2
    show S5.mem (lFa d m + j) = 0
    rw [m5, if_neg (by omega), v4 j hj]

/-- The stage `j`: it computes `stageRes Am bv j`, sets `found` to `1` if it returned, and squares `R`. -/
theorem stage_exec {w : World d} {r n m : ℕ} {δ : ℝ} {Am : Matrix (Fin m) (Fin d) ℚ} {bv : Fin m → ℚ}
    {s : State d} (hc : PCtx r n m δ Am bv s) (j : ℕ) (hR : s.mem (lW0 d m + 9) = stageR j) :
    ∃ k s', k ≤ stageK d m j ∧ Exec w (stageCmd r) s k s' ∧ Fr s s' (stageR' r) (stageC d m) ∧
      s'.mem (lW0 d m + 9) = stageR (j + 1) ∧
      ((s'.nreg (r + 55) = 1 ∧ stageRes Am bv j = some (rdVec s' (lFa d m))) ∨
        (s'.nreg (r + 55) = 0 ∧ stageRes Am bv j = none)) := by
  have hFa : lFa d m = lW0 d m + 24 + m := rfl
  have hFs : lFs d m = lFa d m + d := rfl
  have hFE : lFE d m = lFs d m + d + 2 := rfl
  have hOFF : lOFF d m = lFE d m + d * d := rfl
  obtain ⟨S1, x1, f1, h10, h11⟩ := stage_prims (w := w) hc
  obtain ⟨S2, S3, S4, S5, x2, x3, x4, x5, f5, h56, h57, h12, hM, hV⟩ := stage_fill (w := w) hc f1
  have f15 : Fr s S5 (stageR' r) (stageC d m) := (f1.mono (fun x hx => hx.elim) (fun c hc' => by
      unfold stageC MutC; rcases hc' with h | h | h | h <;> omega)).trans
    (f5.mono (fun x hx => by unfold stageR'; omega) (fun c hc' => by
      unfold stageC MutC; rcases hc' with h | h | h <;> omega))
  have hRM : ∀ x, stageR' r x → MutR r x := fun x hx => by unfold stageR' at hx; unfold MutR; omega
  have hc5 : PCtx r n m δ Am bv S5 := pctx_of_fr hc (f15.mono hRM (fun c hc' => hc'))
  obtain ⟨k6, S6, hk6, x6, f6, hres⟩ := stageLoop_exec (w := w) hc5 h56 h57 h12
  -- the values carried to the loop
  have c15 : ∀ c, c = lW0 d m + 10 ∨ c = lW0 d m + 11 → S5.mem c = S1.mem c := fun c h =>
    f5.2.1 c (by beta_reduce; omega)
  have hRpos : 1 ≤ stageR j := one_le_pow₀ (by norm_num)
  have hY : ⌈S5.mem (lW0 d m + 11)⌉₊ = stageN d j := by
    rw [c15 _ (Or.inr rfl), h11, hR, stageN]
    rw [show 2 * ((d : ℝ) * ((d : ℝ) + 1)) * Real.log (2 * stageR j) = 2 * (d : ℝ) * ((d : ℝ) + 1) *
      Real.log (2 * stageR j) by ring]
    exact Nat.ceil_add_one (by have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ 2 * stageR j); positivity)
  have hRes : centreRun Am bv (1 / 2) ⌈S5.mem (lW0 d m + 11)⌉₊ (rdMat S5 (lFE d m)) (rdVec S5 (lFa d m)) =
      stageRes Am bv j := by
    rw [hY, hM, hV, h10, hR, stageRes, centreCap, sq]
  rw [hRes] at hres
  -- the last primitives: found ← status, R ← R²
  have g6 : ∀ x, ¬ iterR r x → S6.nreg x = S5.nreg x := fun x h => f6.1 x h
  have e56 : S6.nreg (r + 10) = 0 := (g6 _ (by unfold iterR; omega)).trans hc5.zero
  have e30 : S6.nreg (r + 30) = lW0 d m + 9 := (g6 _ (by unfold iterR; omega)).trans (hc5.sc 9 (by norm_num))
  have e31 : S6.nreg (r + 31) = lW0 d m + 10 := (g6 _ (by unfold iterR; omega)).trans (hc5.sc 10 (by norm_num))
  have e21 : S6.nreg (r + 21) = lW0 d m :=
    (g6 _ (by unfold iterR; omega)).trans (by simpa using hc5.sc 0 (by norm_num))
  have m10 : S6.mem (lW0 d m + 10) = stageR j * stageR j := by
    rw [f6.2.1 _ (by unfold iterC; omega), c15 _ (Or.inl rfl), h10, hR]
  have m0 : S6.mem (lW0 d m) = 0 := (f6.2.1 _ (by unfold iterC; omega)).trans hc5.k0
  obtain ⟨S7, hS7⟩ : ∃ S7, S7 = [Prim.nadd (r + 55) (r + 56) (r + 10), .op2 .add (r + 30) (r + 31) (r + 21)].foldl
      (fun s p => p.exec w s) S6 := ⟨_, rfl⟩
  have x7 := exec_prims w [Prim.nadd (r + 55) (r + 56) (r + 10), .op2 .add (r + 30) (r + 31) (r + 21)] S6
  rw [← hS7] at x7
  have n7 : ∀ x, S7.nreg x = if x = r + 55 then S6.nreg (r + 56) else S6.nreg x := fun x => by
    subst hS7; simp only [List.foldl, Prim.exec, Function.update_apply, e56, add_zero]
  have m7 : ∀ c, S7.mem c = if c = lW0 d m + 9 then stageR j * stageR j else S6.mem c := fun c => by
    subst hS7
    simp only [List.foldl, Prim.exec, Function.update_apply, Op2.eval, show r + 30 ≠ r + 55 by omega,
      show r + 31 ≠ r + 55 by omega, show r + 21 ≠ r + 55 by omega, ↓reduceIte, e30, e31, e21, m10, m0, add_zero]
  have d7 : S7.draws = S6.draws ∧ S7.rounds = S6.rounds ∧ S7.pts = S6.pts := by subst hS7; exact ⟨rfl, rfl, rfl⟩
  have vS7 : rdVec S7 (lFa d m) = rdVec S6 (lFa d m) := funext fun t => by
    have := t.2; show S7.mem _ = S6.mem _; rw [m7, if_neg (by omega)]
  refine ⟨_, S7, ?_, Exec.seq x1 (Exec.seq x2 (Exec.seq x3 (Exec.seq x4 (Exec.seq x5 (Exec.seq x6 x7))))), ?_, ?_, ?_⟩
  · have hN := hY ▸ hk6
    simp only [List.length_cons, List.length_nil]
    have hX : 1 ≤ (d + 1) * (d + 1) * (m + 1) := Nat.one_le_iff_ne_zero.2 (by positivity)
    have h1 : stageN d j * (70 * (d + 1) * (d + 1) * (m + 1) + 2) ≤
        stageN d j * (100 * (d + 1) * (d + 1) * (m + 1)) := Nat.mul_le_mul_left _ (by nlinarith)
    have h2 : 27 + 5 * (d * d) + 10 * d ≤ 100 * (d + 1) * (d + 1) * (m + 1) := by nlinarith
    have h3 : stageK d m j = stageN d j * (100 * (d + 1) * (d + 1) * (m + 1)) + 100 * (d + 1) * (d + 1) * (m + 1) := by
      rw [stageK]; ring
    rw [hY] at hk6
    omega
  · refine f15.trans ((f6.mono (fun x hx => ?_) (fun c hc' => ?_)).trans ⟨fun x hx => ?_, fun c hc' => ?_, d7.1,
      d7.2.1, d7.2.2⟩)
    · unfold iterR at hx; unfold stageR'; omega
    · unfold iterC at hc'; unfold stageC MutC; omega
    · rw [n7, if_neg (fun h => hx (Or.inl ⟨by omega, by omega⟩))]
    · rw [m7, if_neg (fun h => hc' (by unfold stageC MutC; omega))]
  · rw [m7, if_pos rfl, stageR, stageR, pow_succ, pow_mul, sq]
  · rw [n7, if_pos rfl, vS7]
    exact hres

/-- The stages, from `R = 2` and `found = 0`, until one returns: the polytope lies in `B(0, R₀)` and contains a unit
ball, so the stage `jStarOf R₀` returns if no stage before it did. -/
theorem outer_exec {w : World d} {r n m : ℕ} {δ : ℝ} {Am : Matrix (Fin m) (Fin d) ℚ} {bv : Fin m → ℚ}
    {s : State d} (hd : 1 ≤ d) (hc : PCtx r n m δ Am bv s) {R0 : ℝ}
    (hK : polytope Am bv ⊆ Metric.closedBall 0 R0) (z : E d) (hz : Metric.closedBall z 1 ⊆ polytope Am bv)
    (hR : s.mem (lW0 d m + 9) = 2) (hf : s.nreg (r + 55) = 0) :
    ∃ k s', k ≤ (jStarOf R0 + 1) * (stageK d m (jStarOf R0) + 2) + 2 ∧
      Exec w (.whileN (r + 55) (r + 9) (stageCmd r)) s k s' ∧ PCtx r n m δ Am bv s' ∧
      ∃ j, stageRes Am bv j = some (rdVec s' (lFa d m)) := by
  set J := jStarOf R0 with hJdef
  have hJR : R0 ≤ stageR J := by
    rw [hJdef]
    exact Nat.find_spec (exists_stageR_ge R0)
  have hstage_some : ∃ a0, stageRes Am bv J = some a0 :=
    stage_some hd Am bv hK z hz hJR
  -- stageR 0 = 2
  have hstageR0 : stageR 0 = (2 : ℝ) := by
    dsimp [stageR]
    norm_num
  -- monotonicity of stageR
  have hmono_pow : ∀ (a b : ℕ), a ≤ b → (2 : ℝ) ^ a ≤ (2 : ℝ) ^ b := by
    intro a b hle
    induction' hle with c hac IH
    · rfl
    · have : (2 : ℝ) ^ (c + 1) = (2 : ℝ) ^ c * 2 := by ring
      rw [this]
      have hpos : 0 ≤ (2 : ℝ) ^ c := pow_nonneg (by norm_num) c
      nlinarith
  have hstageR_mono : ∀ {j₁ j₂ : ℕ}, j₁ ≤ j₂ → stageR j₁ ≤ stageR j₂ := by
    intro j₁ j₂ h
    dsimp [stageR]
    have hpow : 2 ^ j₁ ≤ 2 ^ j₂ := Nat.pow_le_pow_right (by norm_num) h
    exact hmono_pow (2 ^ j₁) (2 ^ j₂) hpow
  have hstageN_mono : ∀ {j₁ j₂ : ℕ}, j₁ ≤ j₂ → stageN d j₁ ≤ stageN d j₂ := by
    intro j₁ j₂ h
    dsimp [stageN]
    have hlog : Real.log (2 * stageR j₁) ≤ Real.log (2 * stageR j₂) := by
      refine Real.log_le_log (by
        have : 0 < stageR j₁ := by
          dsimp [stageR]
          positivity
        nlinarith) ?_
      have : stageR j₁ ≤ stageR j₂ := hstageR_mono h
      nlinarith
    have hceil : Nat.ceil (2 * (d : ℝ) * ((d : ℝ) + 1) * Real.log (2 * stageR j₁)) ≤
                 Nat.ceil (2 * (d : ℝ) * ((d : ℝ) + 1) * Real.log (2 * stageR j₂)) :=
      Nat.ceil_mono (by
        have hpos : 0 ≤ 2 * (d : ℝ) * ((d : ℝ) + 1) := by
          have hd' : (0 : ℝ) ≤ d := by exact mod_cast (Nat.zero_le _)
          nlinarith
        apply mul_le_mul_of_nonneg_left hlog hpos)
    omega
  have hstageK_mono : ∀ {j₁ j₂ : ℕ}, j₁ ≤ j₂ → stageK d m j₁ ≤ stageK d m j₂ := by
    intro j₁ j₂ h
    dsimp [stageK]
    have hN : stageN d j₁ ≤ stageN d j₂ := hstageN_mono h
    have hN' : stageN d j₁ + 1 ≤ stageN d j₂ + 1 := by omega
    exact Nat.mul_le_mul hN' (by rfl)
  -- the invariant I
  let I : ℕ → State d → Prop := fun t S =>
    PCtx r n m δ Am bv S ∧
    (((S.nreg (r + 55) = 0 ∧ S.mem (lW0 d m + 9) = stageR t ∧ (∀ j < t, stageRes Am bv j = none)) ∨
      (S.nreg (r + 55) = 1 ∧ ∃ j, stageRes Am bv j = some (rdVec S (lFa d m)))))
  have hI0 : I 0 s := by
    refine ⟨hc, Or.inl ⟨hf, ?_, ?_⟩⟩
    · rw [hstageR0]
      exact hR
    · intro j hj
      exfalso
      exact Nat.not_lt_zero _ hj
  have hcond0 : condN s (r + 55) (r + 9) := by
    dsimp [condN]
    have : s.nreg (r + 9) = 1 := hc.one
    rw [this, hf]
    omega
  have hbound : ∀ t S, I t S → condN S (r + 55) (r + 9) → t < J + 1 := by
    intro t S hI hcond
    rcases hI with ⟨hPCtx, hcases⟩
    rcases hcases with (⟨hfound0, hRmem, hprev⟩ | ⟨hfound1, hj⟩)
    · -- case found = 0
      by_contra! hge
      have hJt : J < t := by omega
      have hnone : stageRes Am bv J = none := hprev J hJt
      rcases hstage_some with ⟨a0, hsome⟩
      rw [hsome] at hnone
      simp at hnone
    · -- case found = 1, but condN would be 1 < 1, contradiction
      dsimp [condN] at hcond
      have hnreg9 : S.nreg (r + 9) = 1 := hPCtx.one
      rw [hnreg9, hfound1] at hcond
      omega
  have hbody : ∀ t S, I t S → condN S (r + 55) (r + 9) → ∃ k S', k ≤ stageK d m J ∧ Exec w (stageCmd r) S k S' ∧ I (t + 1) S' := by
    intro t S hI hcond
    have hI_copy := hI
    rcases hI with ⟨hPCtx, hcases⟩
    rcases hcases with (⟨hfound0, hRmem, hprev⟩ | ⟨hfound1, hj⟩)
    · -- case found = 0
      rcases stage_exec hPCtx t hRmem with ⟨k, S', hk, hExec, hFr, hRnext, hres⟩
      have hPCtx' : PCtx r n m δ Am bv S' := by
        apply pctx_of_fr hPCtx
        have hFr' : Fr S S' (MutR r) (MutC d m) := by
          apply Fr.mono hFr
          · intro i hi
            rcases hi with (⟨hlo, hhi⟩ | hi | hi)
            · exact Or.inr (Or.inl ⟨hlo, hhi⟩)
            · exact Or.inr (Or.inr (Or.inl hi))
            · exact Or.inr (Or.inr (Or.inr (le_of_eq hi.symm)))
          · intro c hc
            dsimp [stageC, MutC] at hc ⊢
            exact hc
        exact hFr'
      have hInext : I (t + 1) S' := by
        rcases hres with (⟨hfound1', hsome⟩ | ⟨hfound0', hnone⟩)
        · refine ⟨hPCtx', Or.inr ⟨hfound1', ?_⟩⟩
          exact ⟨t, hsome⟩
        · refine ⟨hPCtx', Or.inl ⟨hfound0', hRnext, ?_⟩⟩
          intro j hj'
          rcases Nat.lt_succ_iff_lt_or_eq.mp hj' with (hj' | hj')
          · exact hprev j hj'
          · subst hj'
            exact hnone
      have hkJ : k ≤ stageK d m J := by
        have htJ : t ≤ J := by
          have : t < J + 1 := hbound t S hI_copy hcond
          omega
        have hk_t : k ≤ stageK d m t := hk
        have hK_mono : stageK d m t ≤ stageK d m J := hstageK_mono htJ
        omega
      exact ⟨k, S', hkJ, hExec, hInext⟩
    · -- case found = 1, but condN would be 1 < 1, contradiction
      dsimp [condN] at hcond
      have hnreg9 : S.nreg (r + 9) = 1 := hPCtx.one
      rw [hnreg9, hfound1] at hcond
      omega
  rcases exec_whileN_inv I (J + 1) (stageK d m J) hbound hbody 0 s hI0 with
    ⟨k, S', s', hk, hExec, hI_final, hcond_not⟩
  -- hk : k ≤ ((J + 1) - 0) * (stageK d m J + 2) + 2
  -- simplify ((J + 1) - 0) to (J + 1)
  have hk_simp : k ≤ (J + 1) * (stageK d m J + 2) + 2 := by
    simpa [Nat.sub_zero] using hk
  refine ⟨k, S', hk_simp, hExec, hI_final.1, ?_⟩
  rcases hI_final.2 with (⟨hfound0, hRmem, hprev⟩ | ⟨hfound1, hj⟩)
  · -- found = 0 shouldn't happen since condN is false
    dsimp [condN] at hcond_not
    have hnreg9 : S'.nreg (r + 9) = 1 := hI_final.1.one
    rw [hnreg9, hfound0] at hcond_not
    omega
  · -- found = 1
    exact hj

/-! ## The set-up and the frame -/

/-- The first primitives of the set-up. -/
theorem setup_exec_aux1 {w : World d} {r : ℕ} (hr : 4 ≤ r) (s : State d) :
    let T := [Prim.nconst (r + 9) 1, .nconst (r + 10) 0, .nadd (r + 1) 0 (r + 10), .nadd (r + 2) 2 (r + 10),
      .nconst (r + 3) 3, .nadd (r + 47) (r + 1) (r + 9), .nconst (r + 60) 2, .nconst (r + 46) 3,
      .nconst (r + 58) 0].foldl (fun s p => p.exec w s) s
    T.mem = s.mem ∧ T.draws = s.draws ∧ T.rounds = s.rounds ∧ T.pts = s.pts ∧ (∀ i < r, T.nreg i = s.nreg i) ∧
      T.nreg (r + 1) = s.nreg 0 ∧ T.nreg (r + 2) = s.nreg 2 ∧ T.nreg (r + 3) = 3 ∧ T.nreg (r + 9) = 1 ∧
      T.nreg (r + 10) = 0 ∧ T.nreg (r + 46) = 3 ∧ T.nreg (r + 47) = s.nreg 0 + 1 ∧ T.nreg (r + 58) = 0 ∧
      T.nreg (r + 60) = 2 := by
  intro T
  have n0 : (0 : ℕ) ≠ r + 10 := by omega
  have n0' : (0 : ℕ) ≠ r + 9 := by omega
  have n0'' : (0 : ℕ) ≠ r + 1 := by omega
  have n2 : (2 : ℕ) ≠ r + 10 := by omega
  have n2' : (2 : ℕ) ≠ r + 9 := by omega
  have n2'' : (2 : ℕ) ≠ r + 1 := by omega
  refine ⟨rfl, rfl, rfl, rfl, fun i hi => ?_, ?_⟩
  · have ni : ∀ k, i ≠ r + k := fun k => by omega
    simp [T, List.foldl, Prim.exec, Function.update_apply, ni]
  · simp [T, List.foldl, Prim.exec, Function.update_apply, n0, n2, n0', n2', n0'', n2'']

/-- The last primitives of the set-up, on the registers. -/
theorem setup_exec_aux2 {w : World d} {r : ℕ} (s : State d) :
    let T := [Prim.nadd (r + 4) (r + 44) (r + 9), .nadd (r + 5) (r + 4) (r + 2), .nadd (r + 6) (r + 5) (r + 1),
      .nadd (r + 7) (r + 6) (r + 1), .nadd (r + 8) (r + 7) (r + 9), .nadd (r + 45) (r + 8) (r + 9),
      .nadd r (r + 45) (r + 58)].foldl (fun s p => p.exec w s) s
    T.mem = s.mem ∧ T.draws = s.draws ∧ T.rounds = s.rounds ∧ T.pts = s.pts ∧
      (∀ i, i ≠ r → i ≠ r + 4 → i ≠ r + 5 → i ≠ r + 6 → i ≠ r + 7 → i ≠ r + 8 → i ≠ r + 45 → T.nreg i = s.nreg i) ∧
      T.nreg (r + 4) = s.nreg (r + 44) + s.nreg (r + 9) ∧
      T.nreg (r + 5) = s.nreg (r + 44) + s.nreg (r + 9) + s.nreg (r + 2) ∧
      T.nreg (r + 6) = s.nreg (r + 44) + s.nreg (r + 9) + s.nreg (r + 2) + s.nreg (r + 1) ∧
      T.nreg (r + 7) = s.nreg (r + 44) + s.nreg (r + 9) + s.nreg (r + 2) + s.nreg (r + 1) + s.nreg (r + 1) ∧
      T.nreg (r + 8) = s.nreg (r + 44) + s.nreg (r + 9) + s.nreg (r + 2) + s.nreg (r + 1) + s.nreg (r + 1) +
        s.nreg (r + 9) ∧
      T.nreg (r + 45) = s.nreg (r + 44) + s.nreg (r + 9) + s.nreg (r + 2) + s.nreg (r + 1) + s.nreg (r + 1) +
        s.nreg (r + 9) + s.nreg (r + 9) ∧
      T.nreg r = s.nreg (r + 44) + s.nreg (r + 9) + s.nreg (r + 2) + s.nreg (r + 1) + s.nreg (r + 1) +
        s.nreg (r + 9) + s.nreg (r + 9) + s.nreg (r + 58) := by
  intro T
  refine ⟨rfl, rfl, rfl, rfl, fun i h0 h4 h5 h6 h7 h8 h45 => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [T, List.foldl, Prim.exec, Function.update_apply, *]

/-- The last primitives of the set-up, on the constants. -/
theorem setup_exec_aux3 {w : World d} {r W : ℕ} (s : State d) (hs : ∀ x ≤ 23, s.nreg (r + 21 + x) = W + x) :
    let T := [Prim.rconst (r + 21) 0, .rconst (r + 22) (1 / 2), .rconst (r + 23) 1, .rconst (r + 24) 2,
      .rconst (r + 25) (1 / 4), .ncast (r + 26) 0,
      .op2 .mul (r + 42) (r + 26) (r + 26), .op2 .sub (r + 43) (r + 42) (r + 23), .op2 .div (r + 27) (r + 42) (r + 43),
      .op2 .add (r + 43) (r + 26) (r + 23), .op2 .div (r + 28) (r + 24) (r + 43), .op2 .div (r + 29) (r + 23) (r + 43),
      .rconst (r + 30) 2, .nconst (r + 55) 0].foldl (fun s p => p.exec w s) s
    T.draws = s.draws ∧ T.rounds = s.rounds ∧ T.pts = s.pts ∧
      (∀ i, i ≠ r + 55 → T.nreg i = s.nreg i) ∧ T.nreg (r + 55) = 0 ∧
      (∀ c, (c < W ∨ W + 24 ≤ c) → T.mem c = s.mem c) ∧
      T.mem W = 0 ∧ T.mem (W + 1) = 1 / 2 ∧ T.mem (W + 2) = 1 ∧ T.mem (W + 3) = 2 ∧ T.mem (W + 4) = 1 / 4 ∧
      T.mem (W + 5) = s.nreg 0 ∧
      T.mem (W + 6) = (s.nreg 0 : ℝ) ^ 2 / ((s.nreg 0 : ℝ) ^ 2 - 1) ∧
      T.mem (W + 7) = 2 / ((s.nreg 0 : ℝ) + 1) ∧ T.mem (W + 8) = ((s.nreg 0 : ℝ) + 1)⁻¹ ∧ T.mem (W + 9) = 2 := by
  intro T
  have s21 : s.nreg (r + 21) = W := hs 0 (by norm_num)
  have s22 : s.nreg (r + 22) = W + 1 := hs 1 (by norm_num)
  have s23 : s.nreg (r + 23) = W + 2 := hs 2 (by norm_num)
  have s24 : s.nreg (r + 24) = W + 3 := hs 3 (by norm_num)
  have s25 : s.nreg (r + 25) = W + 4 := hs 4 (by norm_num)
  have s26 : s.nreg (r + 26) = W + 5 := hs 5 (by norm_num)
  have s27 : s.nreg (r + 27) = W + 6 := hs 6 (by norm_num)
  have s28 : s.nreg (r + 28) = W + 7 := hs 7 (by norm_num)
  have s29 : s.nreg (r + 29) = W + 8 := hs 8 (by norm_num)
  have s30 : s.nreg (r + 30) = W + 9 := hs 9 (by norm_num)
  have s42 : s.nreg (r + 42) = W + 21 := hs 21 (by norm_num)
  have s43 : s.nreg (r + 43) = W + 22 := hs 22 (by norm_num)
  refine ⟨by simp only [T, List.foldl, Prim.exec], by simp only [T, List.foldl, Prim.exec],
    by simp only [T, List.foldl, Prim.exec], fun i hi => ?_, ?_, fun c hc => ?_, ?_⟩
  · simp [T, List.foldl, Prim.exec, Function.update_apply, hi]
  · simp [T, List.foldl, Prim.exec]
  · have nk : ∀ k < 24, c ≠ W + k := fun k hk => by omega
    have nW : c ≠ W := by omega
    simp [T, List.foldl, Prim.exec, Function.update_apply, s21, s22, s23, s24, s25, s26, s27, s28, s29, s30, s42,
      s43, nk, nW]
  · simp [T, List.foldl, Prim.exec, Function.update_apply, Op2.eval, s21, s22, s23, s24, s25, s26, s27, s28, s29,
      s30, s42, s43, sq]

theorem setup_exec {w : World d} {r n m : ℕ} {δ : ℝ} (Am : Matrix (Fin m) (Fin d) ℚ) (bv : Fin m → ℚ) (hr : 4 ≤ r) :
    ∃ s', Exec w (setupCmd r) (initPoly d n m δ Am bv) (4 * m + 4 * d + 60) s' ∧ PCtx r n m δ Am bv s' ∧
      s'.mem (lW0 d m + 9) = 2 ∧ s'.nreg (r + 55) = 0 := by
  classical
  set s0 := initPoly d n m δ Am bv with hs0
  have hn0 : s0.nreg 0 = d := rfl
  have hn1 : s0.nreg 1 = n := rfl
  have hn2 : s0.nreg 2 = m := rfl
  have hW : 3 ≤ lW0 d m := by unfold lW0; omega
  -- the first primitives
  have e1 := exec_prims w [.nconst (r + 9) 1, .nconst (r + 10) 0, .nadd (r + 1) 0 (r + 10), .nadd (r + 2) 2 (r + 10),
      .nconst (r + 3) 3, .nadd (r + 47) (r + 1) (r + 9), .nconst (r + 60) 2, .nconst (r + 46) 3, .nconst (r + 58) 0] s0
  obtain ⟨m1, k1d, k1r, k1p, l1, a1d, a1m, a1r, a1o, a1z, a146, a147, a158, a160⟩ :=
    setup_exec_aux1 (w := w) hr s0
  set S1 := [Prim.nconst (r + 9) 1, .nconst (r + 10) 0, .nadd (r + 1) 0 (r + 10), .nadd (r + 2) 2 (r + 10),
      .nconst (r + 3) 3, .nadd (r + 47) (r + 1) (r + 9), .nconst (r + 60) 2, .nconst (r + 46) 3,
      .nconst (r + 58) 0].foldl (fun s p => p.exec w s) s0 with hS1
  rw [hn0] at a1d a147
  rw [hn2] at a1m
  -- the two accumulations
  obtain ⟨S2, e2, h2x, hf2⟩ := nacc_exec (w := w) (i := r + 48) (D := r + 2) (one := r + 9) (x := r + 46)
    (y := r + 47) S1 (by omega) (by omega) a1o
  have f2 : ∀ i, i ≠ r + 48 → i ≠ r + 46 → S2.nreg i = S1.nreg i := fun i h1 h2 =>
    hf2.1 i (by rintro (h | h) <;> contradiction)
  obtain ⟨S3, e3, h3x, hf3⟩ := nacc_exec (w := w) (i := r + 48) (D := r + 1) (one := r + 9) (x := r + 58)
    (y := r + 1) S2 (by omega) (by omega) (by rw [f2 _ (by omega) (by omega)]; exact a1o)
  have f3 : ∀ i, i ≠ r + 48 → i ≠ r + 58 → S3.nreg i = S2.nreg i := fun i h1 h2 =>
    hf3.1 i (by rintro (h | h) <;> contradiction)
  -- the first scalar address
  set S4 := (Prim.nadd (r + 21) (r + 46) (r + 10)).exec w S3 with hS4
  have e4 : Exec w (.prim (.nadd (r + 21) (r + 46) (r + 10))) S3 1 S4 := Exec.prim _ S3
  have h4 : ∀ i, S4.nreg i = if i = r + 21 then lW0 d m else S3.nreg i := by
    intro i
    simp only [hS4, Prim.exec, Function.update_apply]
    split_ifs
    · rw [f3 _ (by omega) (by omega), h2x, f3 _ (by omega) (by omega), f2 _ (by omega) (by omega), a146, a147,
        a1m, a1z]
      unfold lW0; ring
    · rfl
  -- the scalar addresses
  obtain ⟨S5, e5, h5x, hf5⟩ := chain_exec (w := w) (b := r + 21) (one := r + 9) 23 S4 (Or.inl (by omega))
    (by rw [h4, if_neg (by omega), f3 _ (by omega) (by omega), f2 _ (by omega) (by omega), a1o])
  have f5 : ∀ i, (i ≤ r + 21 ∨ r + 44 < i) → S5.nreg i = S4.nreg i := fun i h =>
    hf5.1 i (by rintro ⟨h1, h2⟩; omega)
  have g : ∀ i, i ≠ r + 21 → i ≠ r + 48 → i ≠ r + 58 → i ≠ r + 46 → (i ≤ r + 21 ∨ r + 44 < i) →
      S5.nreg i = S1.nreg i := by
    intro i h1 h2 h3 h4' h5
    rw [f5 i h5, h4, if_neg h1, f3 i h2 h3, f2 i h2 h4']
  have g1 : S5.nreg (r + 1) = d := by rw [g _ (by omega) (by omega) (by omega) (by omega) (by omega), a1d]
  have g2 : S5.nreg (r + 2) = m := by rw [g _ (by omega) (by omega) (by omega) (by omega) (by omega), a1m]
  have g3 : S5.nreg (r + 3) = 3 := by rw [g _ (by omega) (by omega) (by omega) (by omega) (by omega), a1r]
  have g9 : S5.nreg (r + 9) = 1 := by rw [g _ (by omega) (by omega) (by omega) (by omega) (by omega), a1o]
  have g10 : S5.nreg (r + 10) = 0 := by rw [g _ (by omega) (by omega) (by omega) (by omega) (by omega), a1z]
  have g47 : S5.nreg (r + 47) = d + 1 := by rw [g _ (by omega) (by omega) (by omega) (by omega) (by omega), a147]
  have g60 : S5.nreg (r + 60) = 2 := by rw [g _ (by omega) (by omega) (by omega) (by omega) (by omega), a160]
  have g58 : S5.nreg (r + 58) = d * d := by
    rw [f5 _ (by omega), h4, if_neg (by omega), h3x, f2 _ (by omega) (by omega), a158,
      f2 _ (by omega) (by omega), a1d, zero_add]
  have gsc : ∀ x ≤ 23, S5.nreg (r + 21 + x) = lW0 d m + x := by
    intro x hx
    rw [h5x x hx, h4, if_pos rfl]
  have glow : ∀ i < r, S5.nreg i = s0.nreg i := fun i hi => by
    rw [g _ (by omega) (by omega) (by omega) (by omega) (by omega), l1 i hi]
  have gm : S5.mem = s0.mem := by
    funext c
    rw [hf5.2.1 c id, show S4.mem = S3.mem from rfl, hf3.2.1 c id, hf2.2.1 c id, m1]
  have gk : S5.draws = s0.draws ∧ S5.rounds = s0.rounds ∧ S5.pts = s0.pts := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hf5.2.2.1, show S4.draws = S3.draws from rfl, hf3.2.2.1, hf2.2.2.1, k1d]
    · rw [hf5.2.2.2.1, show S4.rounds = S3.rounds from rfl, hf3.2.2.2.1, hf2.2.2.2.1, k1r]
    · rw [hf5.2.2.2.2, show S4.pts = S3.pts from rfl, hf3.2.2.2.2, hf2.2.2.2.2, k1p]
  have h44 : S5.nreg (r + 44) = lW0 d m + 23 := gsc 23 (by norm_num)
  -- the last primitives: the frame registers, then the constants
  obtain ⟨bm, bd, br, bp, b0, b4, b5, b6, b7, b8, b45, br0⟩ := setup_exec_aux2 (w := w) (r := r) S5
  set S6a := [Prim.nadd (r + 4) (r + 44) (r + 9), .nadd (r + 5) (r + 4) (r + 2), .nadd (r + 6) (r + 5) (r + 1),
      .nadd (r + 7) (r + 6) (r + 1), .nadd (r + 8) (r + 7) (r + 9), .nadd (r + 45) (r + 8) (r + 9),
      .nadd r (r + 45) (r + 58)].foldl (fun s p => p.exec w s) S5 with hS6a
  have sa : ∀ x ≤ 23, S6a.nreg (r + 21 + x) = lW0 d m + x := fun x hx => by
    rw [b0 _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), gsc x hx]
  obtain ⟨cd, cr, cp, cn, c55, cm, cv0, cv1, cv2, cv3, cv4, cv5, cv6, cv7, cv8, cv9⟩ :=
    setup_exec_aux3 (w := w) (r := r) (W := lW0 d m) S6a sa
  set S6 := [Prim.rconst (r + 21) 0, .rconst (r + 22) (1 / 2), .rconst (r + 23) 1, .rconst (r + 24) 2,
      .rconst (r + 25) (1 / 4), .ncast (r + 26) 0,
      .op2 .mul (r + 42) (r + 26) (r + 26), .op2 .sub (r + 43) (r + 42) (r + 23), .op2 .div (r + 27) (r + 42) (r + 43),
      .op2 .add (r + 43) (r + 26) (r + 23), .op2 .div (r + 28) (r + 24) (r + 43), .op2 .div (r + 29) (r + 23) (r + 43),
      .rconst (r + 30) 2, .nconst (r + 55) 0].foldl (fun s p => p.exec w s) S6a with hS6
  have e6 := exec_prims w ([Prim.nadd (r + 4) (r + 44) (r + 9), .nadd (r + 5) (r + 4) (r + 2),
      .nadd (r + 6) (r + 5) (r + 1), .nadd (r + 7) (r + 6) (r + 1), .nadd (r + 8) (r + 7) (r + 9),
      .nadd (r + 45) (r + 8) (r + 9), .nadd r (r + 45) (r + 58)] ++
    [Prim.rconst (r + 21) 0, .rconst (r + 22) (1 / 2), .rconst (r + 23) 1, .rconst (r + 24) 2,
      .rconst (r + 25) (1 / 4), .ncast (r + 26) 0,
      .op2 .mul (r + 42) (r + 26) (r + 26), .op2 .sub (r + 43) (r + 42) (r + 23), .op2 .div (r + 27) (r + 42) (r + 43),
      .op2 .add (r + 43) (r + 26) (r + 23), .op2 .div (r + 28) (r + 24) (r + 43), .op2 .div (r + 29) (r + 23) (r + 43),
      .rconst (r + 30) 2, .nconst (r + 55) 0]) S5
  rw [List.foldl_append] at e6
  -- registers and cells of the final state
  have sd : S6a.nreg 0 = d := by
    rw [b0 _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), glow 0 (by omega), hn0]
  have nr : ∀ i, i ≠ r + 55 → i ≠ r → i ≠ r + 4 → i ≠ r + 5 → i ≠ r + 6 → i ≠ r + 7 → i ≠ r + 8 → i ≠ r + 45 →
      S6.nreg i = S5.nreg i := fun i h55 h0 h4' h5 h6 h7 h8 h45 => by
    rw [cn i h55, b0 i h0 h4' h5 h6 h7 h8 h45]
  have mm : ∀ c, (c < lW0 d m ∨ lW0 d m + 24 ≤ c) → S6.mem c = s0.mem c := fun c hc => by
    rw [cm c hc, bm, gm]
  have hOFF : lW0 d m + 24 ≤ lOFF d m := by unfold lOFF lFE lFs lFa lFb; omega
  have cost : 9 + ((4 * S1.nreg (r + 2) + 3) + ((4 * S2.nreg (r + 1) + 3) + (1 + (23 + 21)))) = 4 * m + 4 * d + 60 := by
    rw [a1m, f2 _ (by omega) (by omega), a1d]; ring
  refine ⟨S6, (Exec.seq e1 (Exec.seq e2 (Exec.seq e3 (Exec.seq e4 (Exec.seq e5 e6))))).cost cost, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, fun i h3 hi => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun x hx => ?_, ?_, ?_, ?_, ?_,
      ?_, fun i j => ?_, fun i => ?_, fun c hc => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [nr 0 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), glow 0 (by omega), hn0]
    · rw [nr 1 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), glow 1 (by omega), hn1]
    · rw [nr 2 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), glow 2 (by omega), hn2]
    · rw [nr i (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), glow i hi]
      exact (Conj1PolySanity.initPoly_nreg (n := n) (δ := δ) Am bv).2.2.2 i h3
    · rw [cn _ (by omega), br0, h44, g9, g2, g1, g58]; unfold lOFF lFE lFs lFa lFb; ring
    · rw [nr _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), g1]
    · rw [nr _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), g2]
    · rw [nr _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), g3]
    · rw [cn _ (by omega), b4, h44, g9]; unfold lFb; ring
    · rw [cn _ (by omega), b5, h44, g9, g2]; unfold lFa lFb; ring
    · rw [cn _ (by omega), b6, h44, g9, g2, g1]; unfold lFs lFa lFb; ring
    · rw [cn _ (by omega), b7, h44, g9, g2, g1]; unfold lFs lFa lFb; ring
    · rw [cn _ (by omega), b8, h44, g9, g2, g1]; unfold lFs lFa lFb; ring
    · rw [nr _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), g9]
    · rw [nr _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), g10]
    · rw [cn _ (by omega), sa x (by omega)]
    · rw [cn _ (by omega), b45, h44, g9, g2, g1]; unfold lFE lFs lFa lFb; ring
    · rw [nr _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), g47]
    · rw [nr _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), g58]
    · rw [nr _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), g60]
    · rw [mm 2 (by omega)]; rfl
    · have := row_cell_lt i.2 j.2
      rw [mm _ (by unfold lW0; omega)]
      exact Conj1PolySanity.initPoly_mem_A Am bv i j
    · have h := Nat.mul_le_mul_left (d + 1) (Nat.succ_le_of_lt i.2)
      rw [Nat.mul_succ] at h
      rw [mm _ (by unfold lW0; omega)]
      exact Conj1PolySanity.initPoly_mem_b Am bv i
    · rw [mm _ (by omega)]
      exact Conj1PolySanity.initPoly_mem_high Am bv c (by unfold lW0 at hOFF; omega)
    · simpa using cv0
    · exact cv1
    · exact cv2
    · exact cv3
    · exact cv4
    · rw [cv5, sd]
    · rw [cv6, sd]
    · rw [cv7, sd]
    · rw [cv8, sd]
    · rw [cd, bd, gk.1]; rfl
    · rw [cr, br, gk.2.1]; rfl
    · rw [cp, bp, gk.2.2]; rfl
  · exact cv9
  · exact c55

/-- The primitives after the dot product of a row of the frame. -/
theorem frame_exec_aux0 {w : World d} {r t p A B : ℕ} (X : State d) (h1 : X.nreg (r + 1) = d)
    (h4 : X.nreg (r + 4) = B) (h9 : X.nreg (r + 9) = 1) (h34 : X.nreg (r + 34) = A) (h47 : X.nreg (r + 47) = d + 1)
    (h48 : X.nreg (r + 48) = t) (h50 : X.nreg (r + 50) = p) :
    let Y := [Prim.nadd (r + 61) (r + 50) (r + 1), .nadd (r + 51) (r + 4) (r + 48),
      .op2 .sub (r + 51) (r + 61) (r + 34), .nadd (r + 50) (r + 50) (r + 47),
      .nadd (r + 48) (r + 48) (r + 9)].foldl (fun s p => p.exec w s) X
    Y.nreg (r + 48) = t + 1 ∧ Y.nreg (r + 50) = p + (d + 1) ∧
      (∀ i, i ≠ r + 48 → i ≠ r + 50 → i ≠ r + 51 → i ≠ r + 61 → Y.nreg i = X.nreg i) ∧
      (∀ c, Y.mem c = if c = B + t then X.mem (p + d) - X.mem A else X.mem c) ∧
      Y.draws = X.draws ∧ Y.rounds = X.rounds ∧ Y.pts = X.pts := by
  intro Y
  refine ⟨?_, ?_, fun i i1 i2 i3 i4 => ?_, fun c => ?_, by simp only [Y, List.foldl, Prim.exec],
    by simp only [Y, List.foldl, Prim.exec], by simp only [Y, List.foldl, Prim.exec]⟩
  · simp [Y, List.foldl, Prim.exec, h48, h9]
  · simp [Y, List.foldl, Prim.exec, h50, h47]
  · simp [Y, List.foldl, Prim.exec, i1, i2, i3, i4]
  · simp [Y, List.foldl, Prim.exec, Function.update_apply, Op2.eval, h1, h4, h34, h48, h50]

/-- One row of the frame: `b'_t = b_t - ⟨a_t, a₀⟩` at `F_b + t`. -/
theorem frame_exec_aux1 {w : World d} {r n m : ℕ} {δ : ℝ} {Am : Matrix (Fin m) (Fin d) ℚ} {bv : Fin m → ℚ}
    {s : State d} (hc : PCtx r n m δ Am bv s) (a0 : E d) (ha : rdVec s (lFa d m) = WithLp.ofLp a0) {t : ℕ}
    (ht : t < m) {S : State d} (h48 : S.nreg (r + 48) = t) (h50 : S.nreg (r + 50) = 3 + (d + 1) * t)
    (hcells : ∀ i : Fin m, (i : ℕ) < t → S.mem (lFb d m + i) = (bv i : ℝ) - ∑ j, (Am i j : ℝ) * a0 j)
    (hfr : Fr s S (fun i => i = r + 48 ∨ i = r + 49 ∨ i = r + 50 ∨ i = r + 51 ∨ i = r + 52 ∨ i = r + 61)
      (fun c => c = lW0 d m + 13 ∨ c = lW0 d m + 15 ∨ (lFb d m ≤ c ∧ c < lFb d m + m))) :
    ∃ S', Exec w (fbBody r) S (7 * d + 9) S' ∧ S'.nreg (r + 48) = t + 1 ∧
      S'.nreg (r + 50) = 3 + (d + 1) * (t + 1) ∧
      (∀ i : Fin m, (i : ℕ) < t + 1 → S'.mem (lFb d m + i) = (bv i : ℝ) - ∑ j, (Am i j : ℝ) * a0 j) ∧
      Fr s S' (fun i => i = r + 48 ∨ i = r + 49 ∨ i = r + 50 ∨ i = r + 51 ∨ i = r + 52 ∨ i = r + 61)
        (fun c => c = lW0 d m + 13 ∨ c = lW0 d m + 15 ∨ (lFb d m ≤ c ∧ c < lFb d m + m)) := by
  obtain ⟨hn, hm, hdr, hro, hpt⟩ := hfr
  have rS : ∀ k, k ≠ 48 → k ≠ 49 → k ≠ 50 → k ≠ 51 → k ≠ 52 → k ≠ 61 → S.nreg (r + k) = s.nreg (r + k) :=
    fun k h1 h2 h3 h4 h5 h6 => hn _ (by omega)
  have e1 : S.nreg (r + 1) = d := (rS 1 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans hc.dd
  have e4 : S.nreg (r + 4) = lFb d m :=
    (rS 4 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans hc.fb
  have e5 : S.nreg (r + 5) = lFa d m :=
    (rS 5 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans hc.fa
  have e9 : S.nreg (r + 9) = 1 := (rS 9 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans hc.one
  have e47 : S.nreg (r + 47) = d + 1 :=
    (rS 47 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans hc.d1
  have e34 : S.nreg (r + 34) = lW0 d m + 13 :=
    (rS 34 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans (hc.sc 13 (by norm_num))
  have e36 : S.nreg (r + 36) = lW0 d m + 15 :=
    (rS 36 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans (hc.sc 15 (by norm_num))
  have hrow : ∀ k ≤ d, 3 + (d + 1) * t + k < lW0 d m := fun k hk => by
    have := Nat.mul_le_mul_left (d + 1) (Nat.succ_le_of_lt ht)
    rw [Nat.mul_succ] at this
    unfold lW0; omega
  have hFa : lW0 d m + 24 ≤ lFa d m := by unfold lFa lFb; omega
  -- the dot product `⟨a_t, a⟩`
  obtain ⟨S1, ed, hacc, hn1, hm1, hdr1, hro1, hpt1⟩ := dot_exec (w := w) (j := r + 49) (dv := r + 1) (one := r + 9)
    (pA := r + 50) (pB := r + 5) (tA := r + 51) (tB := r + 52) (acc := r + 34) (prod := r + 36) S
    (by omega) (by omega) (by omega) e9 (by rw [e34, e36]; omega)
    (fun k hk => by rw [e1] at hk; rw [h50, e34, e36]; have := hrow k hk.le; omega)
    (fun k hk => by rw [e5, e34, e36]; omega)
  rw [e1] at ed hacc
  have r1 : ∀ k, k ≠ 49 → k ≠ 51 → k ≠ 52 → S1.nreg (r + k) = S.nreg (r + k) := fun k h1 h2 h3 =>
    hn1 _ (by omega)
  have m1 : ∀ c, c ≠ lW0 d m + 13 → c ≠ lW0 d m + 15 → S1.mem c = S.mem c := fun c h1 h2 =>
    hm1 c (by rw [e34, e36]; omega)
  -- the cell `b'_t`, the next row
  have f1 := r1 1 (by omega) (by omega) (by omega)
  have f4 := r1 4 (by omega) (by omega) (by omega)
  have f9 := r1 9 (by omega) (by omega) (by omega)
  have f34 := r1 34 (by omega) (by omega) (by omega)
  have f47 := r1 47 (by omega) (by omega) (by omega)
  have f48 := r1 48 (by omega) (by omega) (by omega)
  have f50 := r1 50 (by omega) (by omega) (by omega)
  rw [e1] at f1; rw [e4] at f4; rw [e9] at f9; rw [e34] at f34; rw [e47] at f47; rw [h48] at f48; rw [h50] at f50
  obtain ⟨y48, y50, yn, ym, ydr, yro, ypt⟩ := frame_exec_aux0 (w := w) S1 f1 f4 f9 f34 f47 f48 f50
  have ep := exec_prims w [Prim.nadd (r + 61) (r + 50) (r + 1), .nadd (r + 51) (r + 4) (r + 48),
      .op2 .sub (r + 51) (r + 61) (r + 34), .nadd (r + 50) (r + 50) (r + 47), .nadd (r + 48) (r + 48) (r + 9)] S1
  set S2 := [Prim.nadd (r + 61) (r + 50) (r + 1), .nadd (r + 51) (r + 4) (r + 48), .op2 .sub (r + 51) (r + 61) (r + 34),
      .nadd (r + 50) (r + 50) (r + 47), .nadd (r + 48) (r + 48) (r + 9)].foldl (fun s p => p.exec w s) S1 with hS2
  -- the value of `b'_t`
  have hrowv : ∀ k < d, S.mem (3 + (d + 1) * t + k) = s.mem (3 + (d + 1) * t + k) := fun k hk =>
    hm _ (by have := hrow k hk.le; unfold lFb; omega)
  have hval : S1.mem (3 + (d + 1) * t + d) - S1.mem (lW0 d m + 13) =
      (bv ⟨t, ht⟩ : ℝ) - ∑ j, (Am ⟨t, ht⟩ j : ℝ) * a0 j := by
    have hb : S1.mem (3 + (d + 1) * t + d) = (bv ⟨t, ht⟩ : ℝ) := by
      rw [m1 _ (by have := hrow d le_rfl; omega) (by have := hrow d le_rfl; omega),
        hm _ (by have := hrow d le_rfl; unfold lFb; omega)]
      exact hc.cellB ⟨t, ht⟩
    rw [hb, ← e34, hacc, h50, e5, ← Fin.sum_univ_eq_sum_range]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hrowv j j.2, hm _ (by unfold lFa at hFa ⊢; omega)]
    have h1 := hc.cellA ⟨t, ht⟩ j
    have h2 := congrFun ha j
    simp only [rdVec] at h2
    rw [h1, h2]
  refine ⟨S2, (Exec.seq ed ep).cost (by simp), ?_, ?_, ?_,
    ⟨fun i hi => ?_, fun c hc' => ?_, ?_, ?_, ?_⟩⟩
  · exact y48
  · rw [y50]; ring
  · intro i hi
    rw [ym]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi' | hi'
    · rw [ite_eq_right (by omega), m1 _ (by unfold lFb; omega) (by unfold lFb; omega)]
      exact hcells i hi'
    · have hi2 : i = ⟨t, ht⟩ := Fin.ext hi'
      subst hi2
      rw [ite_eq_left rfl]
      exact hval
  · simp only [not_or] at hi
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hi
    rw [yn i h1 h3 h4 h6]
    exact (hn1 i (by omega)).trans (hn i (by omega))
  · simp only [not_or, not_and, not_lt] at hc'
    obtain ⟨h1, h2, h3⟩ := hc'
    rw [ym, ite_eq_right (by have := h3; omega), m1 c h1 h2]
    exact hm c (by omega)
  · rw [ydr, hdr1, hdr]
  · rw [yro, hro1, hro]
  · rw [ypt, hpt1, hpt]

/-- The loop of the frame: the cells `b'_i` for every row. -/
theorem frame_exec_aux2 {w : World d} {r n m : ℕ} {δ : ℝ} {Am : Matrix (Fin m) (Fin d) ℚ} {bv : Fin m → ℚ}
    {s : State d} (hc : PCtx r n m δ Am bv s) (a0 : E d) (ha : rdVec s (lFa d m) = WithLp.ofLp a0)
    {S : State d} (h48 : S.nreg (r + 48) = 0) (h50 : S.nreg (r + 50) = 3)
    (hfr : Fr s S (fun i => i = r + 48 ∨ i = r + 49 ∨ i = r + 50 ∨ i = r + 51 ∨ i = r + 52 ∨ i = r + 61)
      (fun c => c = lW0 d m + 13 ∨ c = lW0 d m + 15 ∨ (lFb d m ≤ c ∧ c < lFb d m + m))) :
    ∃ k S', k ≤ m * (7 * d + 11) + 2 ∧ Exec w (.whileN (r + 48) (r + 2) (fbBody r)) S k S' ∧
      (∀ i : Fin m, S'.mem (lFb d m + i) = (bv i : ℝ) - ∑ j, (Am i j : ℝ) * a0 j) ∧
      Fr s S' (fun i => i = r + 48 ∨ i = r + 49 ∨ i = r + 50 ∨ i = r + 51 ∨ i = r + 52 ∨ i = r + 61)
        (fun c => c = lW0 d m + 13 ∨ c = lW0 d m + 15 ∨ (lFb d m ≤ c ∧ c < lFb d m + m)) := by
  set I : ℕ → State d → Prop := fun t S => t ≤ m ∧ S.nreg (r + 48) = t ∧ S.nreg (r + 50) = 3 + (d + 1) * t ∧
      (∀ i : Fin m, (i : ℕ) < t → S.mem (lFb d m + i) = (bv i : ℝ) - ∑ j, (Am i j : ℝ) * a0 j) ∧
      Fr s S (fun i => i = r + 48 ∨ i = r + 49 ∨ i = r + 50 ∨ i = r + 51 ∨ i = r + 52 ∨ i = r + 61)
        (fun c => c = lW0 d m + 13 ∨ c = lW0 d m + 15 ∨ (lFb d m ≤ c ∧ c < lFb d m + m)) with hI
  have hbound : ∀ t S, I t S → condN S (r + 48) (r + 2) → t < m := by
    rintro t S ⟨-, h48, -, -, hfr⟩ hcond
    have e2 : S.nreg (r + 2) = m := (hfr.1 (r + 2) (by omega)).trans hc.mm
    simp only [condN] at hcond
    omega
  have hbody : ∀ t S, I t S → condN S (r + 48) (r + 2) →
      ∃ k S', k ≤ 7 * d + 9 ∧ Exec w (fbBody r) S k S' ∧ I (t + 1) S' := by
    rintro t S ⟨-, h48, h50, hcells, hfr⟩ hcond
    have e2 : S.nreg (r + 2) = m := (hfr.1 (r + 2) (by omega)).trans hc.mm
    have ht : t < m := by simp only [condN] at hcond; omega
    obtain ⟨S', he, y48, y50, ycells, yfr⟩ := frame_exec_aux1 (w := w) hc a0 ha ht h48 h50 hcells hfr
    exact ⟨7 * d + 9, S', le_rfl, he, ht, y48, y50, ycells, yfr⟩
  have hI0 : I 0 S := ⟨Nat.zero_le _, h48, by rw [h50, Nat.mul_zero, Nat.add_zero],
    fun i hi => absurd hi (Nat.not_lt_zero _), hfr⟩
  obtain ⟨k, S', t', hk, he, ⟨-, h48', -, hcells', hfr'⟩, hnc⟩ :=
    exec_whileN_inv (w := w) (c := fbBody r) I m (7 * d + 9) hbound hbody 0 S hI0
  refine ⟨k, S', ?_, he, fun i => hcells' i ?_, hfr'⟩
  · rw [Nat.sub_zero] at hk
    have e : m * (7 * d + 9 + 2) = m * (7 * d + 11) := by ring
    omega
  · have e2 : S'.nreg (r + 2) = m := (hfr'.1 (r + 2) (by omega)).trans hc.mm
    simp only [condN, not_lt] at hnc
    have := i.2
    omega

/-- The primitives after the loop of the frame: the first three cells of the memory of `P`. -/
theorem frame_exec_aux3 {w : World d} {r n O W : ℕ} (hW : 3 ≤ W) (hO : W < O) (X : State d)
    (h0 : X.nreg r = O) (h9 : X.nreg (r + 9) = 1) (h1 : X.nreg 1 = n) (h21 : X.nreg (r + 21) = W) :
    let Y := [Prim.rconst r (1 / 2), .nadd (r + 51) r (r + 9), .ncast (r + 51) 1, .nadd (r + 51) (r + 51) (r + 9),
      .nconst (r + 52) 2, .op2 .add (r + 51) (r + 52) (r + 21), .nconst 2 0].foldl (fun s p => p.exec w s) X
    Y.nreg 2 = 0 ∧ (∀ i, i ≠ 2 → i ≠ r + 51 → i ≠ r + 52 → Y.nreg i = X.nreg i) ∧
      Y.mem O = 1 / 2 ∧ Y.mem (O + 1) = n ∧ Y.mem (O + 2) = X.mem 2 + X.mem W ∧
      (∀ c, c ≠ O → c ≠ O + 1 → c ≠ O + 2 → Y.mem c = X.mem c) ∧
      Y.draws = X.draws ∧ Y.rounds = X.rounds ∧ Y.pts = X.pts := by
  intro Y
  have b1 : (2 : ℕ) ≠ O := by omega
  have b2 : (2 : ℕ) ≠ O + 1 := by omega
  have b3 : W ≠ O := by omega
  have b4 : W ≠ O + 1 := by omega
  have b5 : O ≠ O + 1 + 1 := by omega
  refine ⟨by simp only [Y, List.foldl, Prim.exec, Function.update_self], fun i i1 i2 i3 => ?_, ?_, ?_, ?_,
    fun c c1 c2 c3 => ?_, by simp only [Y, List.foldl, Prim.exec], by simp only [Y, List.foldl, Prim.exec],
    by simp only [Y, List.foldl, Prim.exec]⟩
  · simp [Y, List.foldl, Prim.exec, Function.update_apply, i1, i2, i3]
  · simp [Y, List.foldl, Prim.exec, Function.update_apply, h0, h9, h21, b5]
  · simp [Y, List.foldl, Prim.exec, h0, h9, h1, h21, b1, b2, b3, b4]
  · simp [Y, List.foldl, Prim.exec, h0, h9, h21, b1, b2, b3, b4, Op2.eval]
  · simp [Y, List.foldl, Prim.exec, Function.update_apply, h0, h9, h21, c1, c2, c3]

theorem frame_exec {w : World d} {r n m : ℕ} {δ : ℝ} {Am : Matrix (Fin m) (Fin d) ℚ} {bv : Fin m → ℚ}
    {s : State d} (hd : 1 ≤ d) (hr : 4 ≤ r) (hc : PCtx r n m δ Am bv s) (a0 : E d)
    (ha : rdVec s (lFa d m) = WithLp.ofLp a0) (L : ℕ) :
    ∃ k s', k ≤ 10 * (d + 1) * (m + 1) + 10 ∧ Exec w (frameCmd r) s k s' ∧ s'.rounds = 0 ∧
      ∀ τ : ℕ → ℕ, τ 0 = L → SimRel r τ a0 Am bv (init d n (1 / 2) n δ) (atPc s' L) := by
  have hO : lW0 d m + 24 + m ≤ lFa d m := by unfold lFa lFb; omega
  have hOFF : lFa d m + d ≤ lOFF d m := by unfold lOFF lFE lFs; omega
  have hW : 3 ≤ lW0 d m := by unfold lW0; omega
  -- the two primitives before the loop
  have epA := exec_prims w [Prim.nconst (r + 48) 0, .nadd (r + 50) (r + 3) (r + 10)] s
  set S0 := [Prim.nconst (r + 48) 0, .nadd (r + 50) (r + 3) (r + 10)].foldl (fun s p => p.exec w s) s with hS0
  have s48 : S0.nreg (r + 48) = 0 := by simp [S0, List.foldl, Prim.exec]
  have s50 : S0.nreg (r + 50) = 3 := by
    simp [S0, List.foldl, Prim.exec, hc.rows, hc.zero]
  have sfr : Fr s S0 (fun i => i = r + 48 ∨ i = r + 49 ∨ i = r + 50 ∨ i = r + 51 ∨ i = r + 52 ∨ i = r + 61)
      (fun c => c = lW0 d m + 13 ∨ c = lW0 d m + 15 ∨ (lFb d m ≤ c ∧ c < lFb d m + m)) := by
    refine ⟨fun i hi => ?_, fun c _ => by simp [S0, List.foldl, Prim.exec], by simp [S0, List.foldl, Prim.exec],
      by simp [S0, List.foldl, Prim.exec], by simp [S0, List.foldl, Prim.exec]⟩
    simp only [not_or] at hi
    simp [S0, List.foldl, Prim.exec, hi.1, hi.2.2.1]
  -- the loop
  obtain ⟨k1, S1, hk1, e1, hcells, hfr1⟩ := frame_exec_aux2 (w := w) hc a0 ha s48 s50 sfr
  obtain ⟨hn1, hm1, hdr1, hro1, hpt1⟩ := hfr1
  have rS : ∀ i, i < r + 48 → S1.nreg i = s.nreg i := fun i hi => hn1 i (by omega)
  have mS : ∀ c, c < lW0 d m + 13 → S1.mem c = s.mem c := fun c hc' => hm1 c (by unfold lFb; omega)
  have mS' : ∀ c, lFb d m + m ≤ c → S1.mem c = s.mem c := fun c hc' => hm1 c (by unfold lFb at hc' ⊢; omega)
  -- the primitives after the loop
  obtain ⟨y2, yn, y0, y1, y2', ym, ydr, yro, ypt⟩ := frame_exec_aux3 (w := w) (n := n) hW
    (show lW0 d m < lOFF d m by omega) S1 ((rS r (by omega)).trans hc.off) ((rS (r + 9) (by omega)).trans hc.one)
    ((rS 1 (by omega)).trans hc.n1) ((rS (r + 21) (by omega)).trans (hc.sc 0 (by norm_num)))
  have epC := exec_prims w [Prim.rconst r (1 / 2), .nadd (r + 51) r (r + 9), .ncast (r + 51) 1,
    .nadd (r + 51) (r + 51) (r + 9), .nconst (r + 52) 2, .op2 .add (r + 51) (r + 52) (r + 21), .nconst 2 0] S1
  set S2 := [Prim.rconst r (1 / 2), .nadd (r + 51) r (r + 9), .ncast (r + 51) 1, .nadd (r + 51) (r + 51) (r + 9),
    .nconst (r + 52) 2, .op2 .add (r + 51) (r + 52) (r + 21), .nconst 2 0].foldl (fun s p => p.exec w s) S1 with hS2
  have nS : ∀ i, i ≠ 2 → i < r + 48 → S2.nreg i = s.nreg i := fun i h1 h2 =>
    (yn i h1 (by omega) (by omega)).trans (rS i h2)
  have mS2 : ∀ c, c < lOFF d m → c < lW0 d m + 13 → S2.mem c = s.mem c := fun c h1 h2 =>
    (ym c (by omega) (by omega) (by omega)).trans (mS c h2)
  have off2 : S2.nreg r = lOFF d m := (nS r (by omega) (by omega)).trans hc.off
  have f4 : S2.nreg (r + 4) = lFb d m := (nS (r + 4) (by omega) (by omega)).trans hc.fb
  have f5 : S2.nreg (r + 5) = lFa d m := (nS (r + 5) (by omega) (by omega)).trans hc.fa
  have f6 : S2.nreg (r + 6) = lFs d m := (nS (r + 6) (by omega) (by omega)).trans hc.fs
  refine ⟨2 + (k1 + 7), S2, ?_, (Exec.seq epA (Exec.seq e1 epC)).cost (by simp), by rw [yro, hro1, hc.rounds],
    fun τ hτ => ?_⟩
  · have : 2 + (k1 + 7) ≤ 7 * d * m + 11 * m + 11 := by
      have e : m * (7 * d + 11) = 7 * d * m + 11 * m := by ring
      omega
    refine this.trans ?_
    have := Nat.mul_le_mul_right m hd
    nlinarith
  refine ⟨fun i hi => ?_, fun c => ?_, ?_, ?_, fun u hu => ?_, ?_, ?_⟩
  · -- the registers below the frame
    simp only [atPc, init]
    rcases Nat.lt_or_ge i 3 with h3 | h3
    · interval_cases i
      · rw [nS 0 (by omega) (by omega), hc.n0]; rfl
      · rw [nS 1 (by omega) (by omega), hc.n1]; rfl
      · rw [y2]; rfl
    · rw [nS i (by omega) (by omega), hc.low i h3 hi, ite_eq_right (by omega), ite_eq_right (by omega)]
  · -- the memory of `P`
    simp only [atPc, init, off2]
    rcases Nat.lt_or_ge c 3 with h3 | h3
    · interval_cases c
      · rw [Nat.add_zero, y0]; rfl
      · rw [y1]; rfl
      · rw [y2', mS 2 (by omega), mS (lW0 d m) (by omega), hc.cδ, hc.k0, add_zero]; rfl
    · rw [ym _ (by omega) (by omega) (by omega), mS' _ (by unfold lOFF lFE lFs lFa at *; omega),
        hc.high _ (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
  · simp only [atPc, init]; rw [ydr, hdr1, hc.draws]
  · simp only [atPc, init]; rw [yro, hro1, hc.rounds]
  · simp [init] at hu
  · simp only [atPc, init]; exact hτ.symm
  · -- the frame
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun i j => ?_, fun i => ?_, fun j => ?_⟩ <;>
      simp only [atPc]
    · exact (nS (r + 1) (by omega) (by omega)).trans hc.dd
    · exact (nS (r + 2) (by omega) (by omega)).trans hc.mm
    · exact (nS (r + 3) (by omega) (by omega)).trans hc.rows
    · rw [nS (r + 7) (by omega) (by omega), f6, hc.acc]
    · rw [nS (r + 8) (by omega) (by omega), f6, hc.tmp]
    · exact (nS (r + 9) (by omega) (by omega)).trans hc.one
    · exact (nS (r + 10) (by omega) (by omega)).trans hc.zero
    · rw [f4]; unfold lFb lW0; omega
    · rw [f4, f5]; unfold lFa; omega
    · rw [f5, f6]; unfold lFs; omega
    · rw [f6, off2]; unfold lOFF lFE; omega
    · have hrow : 3 + (d + 1) * (i : ℕ) + j < lW0 d m := by
        have := Nat.mul_le_mul_left (d + 1) (Nat.succ_le_of_lt i.2)
        rw [Nat.mul_succ] at this
        have := j.2
        unfold lW0; omega
      rw [mS2 _ (by omega) (by omega)]
      exact hc.cellA i j
    · rw [f4, ym _ (by unfold lFb at *; omega) (by unfold lFb at *; omega) (by unfold lFb at *; omega)]
      exact hcells i
    · rw [f5, ym _ (by have := j.2; omega) (by have := j.2; omega) (by have := j.2; omega),
        mS' _ (by unfold lFa at *; omega)]
      have h2 := congrFun ha j
      simp only [rdVec] at h2
      rw [h2]

end AdversarialBco.Conj1Poly
