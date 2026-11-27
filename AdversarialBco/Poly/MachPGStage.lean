/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.MachPGPar
public import AdversarialBco.Poly.MachPGLoops

@[expose] public section

/-!
# Procedure PG in VL: the data of one stage

A stage runs the `J` repeats, each a descent and an amplified test, on the stream `pgOmegaAt` (repeat `r` reads `W d`
draws from `b + r W d`, `pgW`), keeps the first accepted average, then composes it with the current position
(`PgAt.comp`), or sets `ok := 0` when no repeat is accepted. This file holds that stream and the lists of the
variables a stage writes (`pgStageN`, `pgStageS`, `pgStageA`); the rule of a stage of PG-N with CLAMP-NS is
`runs_pgStageCNS` (Conj1Arith/MachN/Stage.lean).
-/

open AdversarialBco AdversarialBco.RealRAM AdversarialBco.Poly AdversarialBco.Poly.Mach AdversarialBco.Poly.Mach.VL
  Matrix

namespace AdversarialBco.Poly.PG

variable {d : ℕ}

/-- The samples of one repeat of a stage: the `N` steps of the descent, then the `m_T` blocks of `n_T` samples of the
amplified test. -/
noncomputable def pgW (d : ℕ) (ρ δ : ℝ) : ℕ := pgNs d ρ + pgMT δ * pgNT d ρ

/-- The stream of the repeats of a stage that starts at the draw `b`: repeat `r` reads the `W d` draws from
`b + r W d`, the `N` samples of the descent first, then the `m_T` blocks of `n_T` samples of the test. -/
noncomputable def pgOmegaAt (w : World d) (ρ δ : ℝ) (b : ℕ) : ℕ → PgRound d := fun r =>
  (fun k => WithLp.toLp 2 fun c => w.gs (b + r * (pgW d ρ δ * d) + k * d + c),
    fun v k => WithLp.toLp 2 fun c => w.gs (b + r * (pgW d ρ δ * d) + pgNs d ρ * d + (v * pgNT d ρ + k) * d + c))

/-- The natural variables a stage writes. -/
def pgStageN (n0 : ℕ) : List ℕ := pgTmpN n0 ++ [n0 + 10, n0 + 11, n0 + 12, n0 + 13, n0 + 15, n0 + 17]

/-- The scalars a stage writes (besides `ok`). -/
def pgStageS (s0 : ℕ) : List ℕ :=
  pgTmpS s0 ++ [s0 + 20, s0 + 21, s0 + 22, s0 + 23, s0 + 24, s0 + 25, s0 + 26, s0 + 27, s0 + 28, s0 + 29, s0 + 30,
    s0 + 31, s0 + 32, s0 + 33, s0 + 34, s0 + 35, s0 + 36, s0 + 37, s0 + 38, s0 + 39, s0 + 40, s0 + 41, s0 + 44,
    s0 + 45, s0 + 46, s0 + 47, s0 + 49, s0 + 50, s0 + 51]

/-- The arrays a repeat writes. -/
def pgRepA (a0 : ℕ) : List ℕ :=
  [a0, a0 + 1, a0 + 2, a0 + 3, a0 + 4, a0 + 5, a0 + 6, a0 + 7, a0 + 8, a0 + 9, a0 + 10, a0 + 11, a0 + 12, a0 + 13,
    a0 + 14, a0 + 15, a0 + 16, a0 + 17, a0 + 18, a0 + 19, a0 + 20]

/-- The arrays a stage writes (besides `μ` and `A`). -/
def pgStageA (a0 : ℕ) : List ℕ := pgRepA a0 ++ [a0 + 21, a0 + 22]

theorem pgStageN_compC (n0 : ℕ) : ∀ i ∈ [n0, n0 + 1, n0 + 2, n0 + 3, n0 + 4, n0 + 5, n0 + 6], i ∈ pgStageN n0 := by
  simp [pgStageN, pgTmpN]

theorem pgStageS_compC (s0 : ℕ) : ∀ x ∈ [s0 + 2, s0 + 8, s0 + 9, s0 + 11], x ∈ pgStageS s0 := by
  simp [pgStageS, pgTmpS]

theorem pgStageS_not_mem {x s0 : ℕ} (h : x < s0 ∨ s0 + 64 ≤ x) : x ∉ pgStageS s0 := by
  simp [pgStageS, pgTmpS]; omega

theorem kCompC_ge (d : ℕ) : 1 + 2 ≤ kCompC d + 1 := by unfold kCompC; omega

/-- The composition `μ := μ + A μ'`, `A := A T'` puts `μ`, `A` at the composed position. -/
theorem PgAt.comp {σ σ' : Env d} {muv Av a b : ℕ} {P X : PgSp d} (hP : PgAt σ muv Av P) (hX : PgAt σ a b X)
    (hv : σ'.vec muv = σ.vec muv + σ.mat Av *ᵥ σ.vec a) (hm : σ'.mat Av = σ.mat Av * σ.mat b) :
    PgAt σ' muv Av (pgComp P (pgOut X)) := by
  refine ⟨?_, ?_⟩
  · rw [hv, hP.1, hP.2, hX.1]
    funext i
    simp [pgComp, pgOut, pgMu_pgPack, pgOp_apply]
  · rw [hm, hP.2, hX.2]
    simp [pgComp, pgOut, pgMat_pgPack, pgA]

end AdversarialBco.Poly.PG
