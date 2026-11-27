/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.MachPGStage
public import AdversarialBco.Poly.Df2Run

@[expose] public section

/-!
# Procedure PG in VL: the variables of the code and of its stages

The lists of the naturals and the scalars that a stage, the stages and the code of PG write (`pgBodyS`, `pgLoopN`,
`pgCodeN`, `pgCodeS`), the flag and the position against the output of a stage (`PgPos`), the offsets of the stages in
the stream (`df2oPgOff_succ`), and `1 ≤ ρ_i` (`one_le_pgRhoStage`). The rule of the code of PG-N with CLAMP-NS,
`runs_pgCodeNS` (Conj1Arith/MachN/Rule.lean), reads them.
-/

open AdversarialBco AdversarialBco.RealRAM AdversarialBco.Poly AdversarialBco.Poly.Mach AdversarialBco.Poly.Mach.VL
  Matrix

namespace AdversarialBco.Poly.PG

variable {d : ℕ}

/-! ## The ratios of the stages -/

theorem one_le_pgRhoStage (hd : 1 ≤ d) : ∀ i, 1 ≤ pgRhoStage d i
  | 0 => by simp [pgRhoStage]
  | i + 1 => by
    have ih := one_le_pgRhoStage hd i
    have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
    have hlog : (1 / 4 : ℝ) ≤ Real.log (1 + pgRhoStage d i) := by
      have h2 : Real.log 2 ≤ Real.log (1 + pgRhoStage d i) := Real.log_le_log (by norm_num) (by linarith)
      have := Real.log_two_gt_d9
      linarith
    have hs : (1 / 2 : ℝ) ≤ Real.sqrt (Real.log (1 + pgRhoStage d i)) := by
      rw [show (1 / 2 : ℝ) = Real.sqrt (1 / 4) by
        rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt hlog
    simp only [pgRhoStage]
    nlinarith

/-! ## A stage followed by the next ratio and radius -/

/-- The flag and the position against the output `o` of a stage. -/
def PgPos (σ : Env d) (okv muv Av : ℕ) (o : Option (PgSp d)) : Prop :=
  (o = none ∧ σ.sc okv = 0) ∨ (∃ P, o = some P ∧ σ.sc okv = 1 ∧ PgAt σ muv Av P)

/-- The scalars a stage and the next ratio write (besides `ok`). -/
def pgBodyS (s0 : ℕ) : List ℕ := pgStageS s0 ++ [s0 + 19, s0 + 42]

theorem pgBodyS_not_mem {s0 x : ℕ} (h : x < s0 ∨ s0 + 64 ≤ x) : x ∉ pgBodyS s0 := by
  simp only [pgBodyS, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or]
  exact ⟨pgStageS_not_mem h, by omega, by omega⟩

theorem df2oPgOff_succ (d : ℕ) (δ' : ℝ) (t : ℕ) :
    df2oPgOff d δ' (t + 1) = df2oPgOff d δ' t + pgJr δ' * (pgW d (pgRhoStage d t) δ' * d) := by
  simp only [df2oPgOff, Finset.sum_range_succ, df2oPgBlock, df2oPgW, pgW]; ring

theorem pgS19 (s0 : ℕ) : s0 + 19 ∉ pgStageS s0 := by simp [pgStageS, pgTmpS]
theorem pgS42 (s0 : ℕ) : s0 + 42 ∉ pgStageS s0 := by simp [pgStageS, pgTmpS]
theorem pgS48 (s0 : ℕ) : s0 + 48 ∉ pgStageS s0 := by simp [pgStageS, pgTmpS]

/-! ## The stages -/

/-- The naturals the stages and the stage counter write. -/
def pgLoopN (n0 : ℕ) : List ℕ := pgStageN n0 ++ [n0 + 19]

/-! ## The code of PG -/

/-- The naturals the code of PG writes. -/
def pgCodeN (n0 : ℕ) : List ℕ := pgLoopN n0 ++ [n0 + 9, n0 + 14, n0 + 16, n0 + 18]

/-- The scalars the code of PG writes (besides `ok`). -/
def pgCodeS (s0 : ℕ) : List ℕ := pgBodyS s0 ++ [s0 + 43, s0 + 48]

theorem pgPack_zero_smul_one (r0 : ℝ) :
    Matrix.of (fun a b : Fin d => if a = b then r0 else (0 : ℝ)) = pgMat (pgPack 0 (r0 • (1 : Matrix (Fin d) (Fin d) ℝ))) := by
  rw [pgMat_pgPack]; ext a b; simp [Matrix.one_apply]

end AdversarialBco.Poly.PG
