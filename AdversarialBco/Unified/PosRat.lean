/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.PosSep

@[expose] public section

/-!
# UNI-POS: the procedure stays on rational points

The program's SEP field is read at rational points only (the oracle answers rational queries), so the analysis of
TRI-OGD-O follows the procedure on rational points: the draws of the sampler, the iterates of the core (the rounding
`triRound` returns rational points, the clip has rational ends), their averages, the base points `μ + L w` of the steps,
the compositions of positions and the first position `(c, r0 I)` for a rational frame. Closure lemmas for `IsQ`,
`IsRatE`, `IsRatPg` (Unified/PosSep.lean).
-/

open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius

namespace AdversarialBco.UniPos

open AdversarialBco.Poly AdversarialBco.Bit

variable {d : ℕ}

theorem isQ_nat (n : ℕ) : IsQ (n : ℝ) := ⟨n, by push_cast; rfl⟩

theorem isQ_int (n : ℤ) : IsQ (n : ℝ) := ⟨n, by push_cast; rfl⟩

theorem isQ_zero : IsQ 0 := ⟨0, by push_cast; rfl⟩

theorem isQ_one : IsQ 1 := ⟨1, by push_cast; rfl⟩

theorem IsQ.add {x y : ℝ} (hx : IsQ x) (hy : IsQ y) : IsQ (x + y) := by
  obtain ⟨p, rfl⟩ := hx; obtain ⟨q, rfl⟩ := hy; exact ⟨p + q, by push_cast; rfl⟩

theorem IsQ.sub {x y : ℝ} (hx : IsQ x) (hy : IsQ y) : IsQ (x - y) := by
  obtain ⟨p, rfl⟩ := hx; obtain ⟨q, rfl⟩ := hy; exact ⟨p - q, by push_cast; rfl⟩

theorem IsQ.mul {x y : ℝ} (hx : IsQ x) (hy : IsQ y) : IsQ (x * y) := by
  obtain ⟨p, rfl⟩ := hx; obtain ⟨q, rfl⟩ := hy; exact ⟨p * q, by push_cast; rfl⟩

theorem IsQ.neg {x : ℝ} (hx : IsQ x) : IsQ (-x) := by
  obtain ⟨p, rfl⟩ := hx; exact ⟨-p, by push_cast; rfl⟩

theorem IsQ.inv {x : ℝ} (hx : IsQ x) : IsQ x⁻¹ := by
  obtain ⟨p, rfl⟩ := hx; exact ⟨p⁻¹, by push_cast; rfl⟩

theorem IsQ.div {x y : ℝ} (hx : IsQ x) (hy : IsQ y) : IsQ (x / y) := by
  rw [div_eq_mul_inv]; exact hx.mul hy.inv

theorem IsQ.pow {x : ℝ} (hx : IsQ x) (n : ℕ) : IsQ (x ^ n) := by
  obtain ⟨p, rfl⟩ := hx; exact ⟨p ^ n, by push_cast; rfl⟩

theorem IsQ.max {x y : ℝ} (hx : IsQ x) (hy : IsQ y) : IsQ (max x y) := by
  rcases le_total x y with h | h
  · rw [max_eq_right h]; exact hy
  · rw [max_eq_left h]; exact hx

theorem IsQ.min {x y : ℝ} (hx : IsQ x) (hy : IsQ y) : IsQ (min x y) := by
  rcases le_total x y with h | h
  · rw [min_eq_left h]; exact hx
  · rw [min_eq_right h]; exact hy

theorem isQ_two_pow (n : ℕ) : IsQ ((2 : ℝ) ^ n) := by
  have : (2 : ℝ) = ((2 : ℕ) : ℝ) := by norm_num
  rw [this]; exact (isQ_nat 2).pow n

theorem isQ_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ) (h : ∀ i ∈ s, IsQ (f i)) : IsQ (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isQ_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-! ## The parameters -/

theorem isQ_triR (d : ℕ) : IsQ (triR d) := by unfold triR; exact isQ_two_pow _

theorem isQ_triA (d : ℕ) : IsQ (triA d) := by unfold triA; exact isQ_one.div (isQ_two_pow _)

theorem isQ_triB (d : ℕ) : IsQ (triB d) := by
  unfold triB
  have : (161 : ℝ) = ((161 : ℕ) : ℝ) := by norm_num
  rw [this]; exact (isQ_nat 161).mul (isQ_two_pow _)

theorem isQ_triLo (r a b : ℝ) (hr : IsQ r) (ha : IsQ a) (hb : IsQ b) (k : Fin d ⊕ Fin d × Fin d) :
    IsQ (triLo r a b k) := by
  cases k with
  | inl i => exact hr.neg
  | inr p =>
    simp only [triLo, Sum.elim_inr]
    split_ifs
    · exact hb.neg
    · exact ha
    · exact isQ_zero

theorem isQ_triHi (r b : ℝ) (hr : IsQ r) (hb : IsQ b) (k : Fin d ⊕ Fin d × Fin d) : IsQ (triHi r b k) := by
  cases k with
  | inl i => exact hr
  | inr p =>
    simp only [triHi, Sum.elim_inr]
    split_ifs
    · exact hb
    · exact isQ_zero

/-! ## Points of `PgSp d` -/

theorem IsRatPg.add {x y : PgSp d} (hx : IsRatPg x) (hy : IsRatPg y) : IsRatPg (x + y) := fun k => by
  simpa using (hx k).add (hy k)

theorem IsRatPg.sub {x y : PgSp d} (hx : IsRatPg x) (hy : IsRatPg y) : IsRatPg (x - y) := fun k => by
  simpa using (hx k).sub (hy k)

theorem IsRatPg.smul {s : ℝ} {x : PgSp d} (hs : IsQ s) (hx : IsRatPg x) : IsRatPg (s • x) := fun k => by
  simpa using hs.mul (hx k)

theorem isRatPg_zero : IsRatPg (0 : PgSp d) := fun k => by simpa using isQ_zero

theorem isRatPg_sum {ι : Type*} (s : Finset ι) (f : ι → PgSp d) (h : ∀ i ∈ s, IsRatPg (f i)) :
    IsRatPg (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isRatPg_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem isRatPg_triRound (Bv : ℕ) (v : PgSp d) : IsRatPg (triRound Bv v) := fun k => by
  simp only [triRound, PiLp.toLp_apply]
  exact (isQ_int _).div (isQ_two_pow _)

theorem isRatPg_triClip (r a b : ℝ) (hr : IsQ r) (ha : IsQ a) (hb : IsQ b) (x : PgSp d) (hx : IsRatPg x) :
    IsRatPg (triClip r a b x) := fun k => by
  simp only [triClip, PiLp.toLp_apply]
  exact (isQ_triLo r a b hr ha hb k).max ((isQ_triHi r b hr hb k).min (hx k))

theorem isRatPg_pgPack (μ : EuclideanSpace ℝ (Fin d)) (M : Matrix (Fin d) (Fin d) ℝ) (hμ : IsRatE μ)
    (hM : ∀ i j, IsQ (M i j)) : IsRatPg (pgPack μ M) := fun k => by
  cases k with
  | inl i => simpa [pgPack] using hμ i
  | inr p => simpa [pgPack] using hM p.1 p.2

theorem isRatE_pgMu (x : PgSp d) (hx : IsRatPg x) : IsRatE (pgMu x) := fun i => by
  simpa [pgMu] using hx (Sum.inl i)

theorem isQ_pgMat (x : PgSp d) (hx : IsRatPg x) (i j : Fin d) : IsQ (pgMat x i j) := by
  simpa [pgMat] using hx (Sum.inr (i, j))

theorem isRatE_pgOp (x : PgSp d) (hx : IsRatPg x) (w : EuclideanSpace ℝ (Fin d)) (hw : IsRatE w) :
    IsRatE (pgOp x w) := fun i => by
  rw [pgOp_apply]
  simp only [Matrix.mulVec, dotProduct]
  exact isQ_sum _ _ fun j _ => (isQ_pgMat x hx i j).mul (hw j)

theorem IsRatE.add {z w : EuclideanSpace ℝ (Fin d)} (hz : IsRatE z) (hw : IsRatE w) : IsRatE (z + w) := fun i => by
  simpa using (hz i).add (hw i)

/-- The base point `μ + L w` of a step is rational. -/
theorem isRatE_base (x : PgSp d) (hx : IsRatPg x) (w : EuclideanSpace ℝ (Fin d)) (hw : IsRatE w) :
    IsRatE (pgMu x + pgOp x w) :=
  (isRatE_pgMu x hx).add (isRatE_pgOp x hx w hw)

/-- The composition of two rational positions is rational. -/
theorem isRatPg_pgComp (P Q : PgSp d) (hP : IsRatPg P) (hQ : IsRatPg Q) : IsRatPg (pgComp P Q) := by
  unfold pgComp
  refine isRatPg_pgPack _ _ (isRatE_base P hP (pgMu Q) (isRatE_pgMu Q hQ)) fun i j => ?_
  simp only [Matrix.mul_apply]
  exact isQ_sum _ _ fun k _ => (isQ_pgMat P hP i k).mul (isQ_pgMat Q hQ k j)

/-- The first position `(c, r0 I)` of a rational frame is rational. -/
theorem isRatPg_start (c : EuclideanSpace ℝ (Fin d)) (hc : IsRatE c) (r0 : ℝ) (hr0 : IsQ r0) :
    IsRatPg (pgPack c (r0 • (1 : Matrix (Fin d) (Fin d) ℝ))) := by
  refine isRatPg_pgPack _ _ hc fun i j => ?_
  simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  split_ifs
  · simpa using hr0
  · simpa using isQ_zero

theorem isRatPg_pgPack01 : IsRatPg (pgPack 0 1 : PgSp d) :=
  isRatPg_pgPack _ _ (fun i => by simpa using isQ_zero) fun i j => by
    simp only [Matrix.one_apply]
    split_ifs
    · exact isQ_one
    · exact isQ_zero

/-- The draws of the sampler are rational. -/
theorem isRatE_triDraw (d B : ℕ) (x : ℕ → Bool) (t : ℕ) : IsRatE (triDraw d B x t) := fun i => by
  simp only [triDraw, gsVec, PiLp.toLp_apply]
  exact (isQ_int _).div (isQ_two_pow _)

/-- The iterates of the core with a rounded field are rational, from a rational start, with rational box ends and a
rational step. -/
theorem isRatPg_triIter (r a b s : ℝ) (hr : IsQ r) (ha : IsQ a) (hb : IsQ b) (hs : IsQ s) (Bv : ℕ)
    (V : PgSp d → EuclideanSpace ℝ (Fin d) → PgSp d) (y : ℕ → EuclideanSpace ℝ (Fin d)) (t : ℕ) :
    IsRatPg (triIter r a b s (fun x w => triRound Bv (V x w)) y t) := by
  induction t with
  | zero => exact isRatPg_pgPack01
  | succ t ih =>
    exact isRatPg_triClip r a b hr ha hb _ (ih.sub (IsRatPg.smul hs (isRatPg_triRound Bv _)))

theorem isRatPg_triAvg (r a b s : ℝ) (hr : IsQ r) (ha : IsQ a) (hb : IsQ b) (hs : IsQ s) (Bv : ℕ)
    (V : PgSp d → EuclideanSpace ℝ (Fin d) → PgSp d) (y : ℕ → EuclideanSpace ℝ (Fin d)) (N : ℕ) :
    IsRatPg (triAvg r a b s (fun x w => triRound Bv (V x w)) y N) := by
  unfold triAvg
  exact IsRatPg.smul (isQ_nat N).inv
    (isRatPg_sum _ _ fun t _ => isRatPg_triIter r a b s hr ha hb hs Bv V y t)

end AdversarialBco.UniPos
