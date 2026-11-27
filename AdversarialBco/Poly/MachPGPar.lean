/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.MachPGLin

@[expose] public section

/-!
# Procedure PG in VL: the rules of the straight-line parameter code

The parameters of a stage from `ρ` (parts A to D: `runs_pgParA`, `runs_pgParB`, `runs_pgParC1`, `runs_pgParC2`), the
next ratio and radius (`runs_pgRho`) and the caps of the whole procedure (`runs_pgCaps`), each read off the blocks of
scalar instructions of MachPGCode.lean through `runs_sprog` of MachSI.lean.
-/

open AdversarialBco AdversarialBco.RealRAM AdversarialBco.Poly AdversarialBco.Poly.Mach AdversarialBco.Poly.Mach.VL
  Matrix

namespace AdversarialBco.Poly.PG

variable {d : ℕ} {L : Layout} {w : World d}

/-- The tactic of the block values: unfold the block, read the updates, decide the index equalities. -/
macro "pg_val" : tactic => `(tactic| (
  simp only [sEval, List.foldl, SI.step, SI.dst, SI.val, Function.update_apply, Op2.eval, Op1.eval]
  simp))

section blocks

variable (n : ℕ → ℕ) (f : ℕ → ℝ) (s0 n0 : ℕ)

theorem pgA1_v2 : sEval n (pgA1 s0) f (s0 + 2) = 1 := by simp only [pgA1]; pg_val
theorem pgA1_v20 : sEval n (pgA1 s0) f (s0 + 20) = Real.sqrt (2 * Real.log (1 + f (s0 + 19))) := by
  simp only [pgA1]; pg_val
theorem pgA2_v22 : sEval n (pgA2 s0) f (s0 + 22) = 627 / 4000 * f (s0 + 19) := by simp only [pgA2]; pg_val
theorem pgA3_v21 : sEval n (pgA3 s0) f (s0 + 21) = f (s0 + 2) / (9 * f (s0 + 48) * f (s0 + 20)) := by
  simp only [pgA3]; pg_val
theorem pgA4_v23 : sEval n (pgA4 s0) f (s0 + 23) = 1 / 8 * f (s0 + 19) := by simp only [pgA4]; pg_val
theorem pgA5_v24 : sEval n (pgA5 s0) f (s0 + 24) =
    f (s0 + 23) * Real.sqrt (4 + 393129 / 250000 * f (s0 + 48)) := by simp only [pgA5]; pg_val
theorem pgA6_v32 : sEval n (pgA6 s0) f (s0 + 32) = -1 / 8 / f (s0 + 48) := by simp only [pgA6]; pg_val

theorem pgB1_v45 : sEval n (pgB1 s0) f (s0 + 45) =
    5 * (f (s0 + 22) * f (s0 + 22)) * f (s0 + 48) * (f (s0 + 48) + 2) * (f (s0 + 48) + 5) := by
  simp only [pgB1]; pg_val
theorem pgB2_v25 : sEval n (pgB2 s0) f (s0 + 25) =
    (f (s0 + 45) + 1 / 32 / f (s0 + 48)) / (f (s0 + 21) * f (s0 + 21)) := by simp only [pgB2]; pg_val
theorem pgB3_v26 : sEval n (pgB3 s0) f (s0 + 26) =
    1 / 64 / (922 * f (s0 + 48) * f (s0 + 48) * (f (s0 + 20) * f (s0 + 20)) * f (s0 + 22)) := by
  simp only [pgB3]; pg_val
theorem pgB4_v27 : sEval n (pgB4 s0) f (s0 + 27) =
    f (s0 + 26) * f (s0 + 21) / (7 * f (s0 + 22) * (f (s0 + 2) + Real.sqrt (f (s0 + 48))) * f (s0 + 24)) := by
  simp only [pgB4]; pg_val
theorem pgB5_v28 : sEval n (pgB5 s0) f (s0 + 28) = 1 / 8 / (12 * f (s0 + 48) * f (s0 + 20)) := by
  simp only [pgB5]; pg_val
theorem pgC1_v45 : sEval n (pgC1 s0) f (s0 + 45) =
    5 / 4 * (f (s0 + 22) * f (s0 + 22)) * f (s0 + 48) * f (s0 + 48) * f (s0 + 48) := by simp only [pgC1]; pg_val
theorem pgC2_v46 : sEval n (pgC2 s0) f (s0 + 46) = 6144 * (f (s0 + 48) + f (s0 + 2)) * (f (s0 + 48) + 5) := by
  simp only [pgC2]; pg_val
theorem pgC3_v47 : sEval n (pgC3 s0) f (s0 + 47) = 221184 * (f (s0 + 48) + 3) * (f (s0 + 20) * f (s0 + 20)) := by
  simp only [pgC3]; pg_val
theorem pgC4_v45 : sEval n (pgC4 s0) f (s0 + 45) = f (s0 + 45) * max (f (s0 + 46)) (f (s0 + 47)) / (1 / 64) := by
  simp only [pgC4]; pg_val
theorem pgD1_v45 : sEval n (pgD1 s0) f (s0 + 45) =
    16 * (f (s0 + 24) * f (s0 + 24)) * f (s0 + 25) / (f (s0 + 26) * f (s0 + 26)) := by simp only [pgD1]; pg_val
theorem pgD2_v45 : sEval n (pgD2 s0) f (s0 + 45) = Real.log (f (s0 + 19) / f (s0 + 27)) / Real.log 2 := by
  simp only [pgD2]; pg_val
theorem pgD3_v29 : sEval n (pgD3 s0 n0) f (s0 + 29) =
    f (s0 + 24) / (Real.sqrt (f (s0 + 25)) * Real.sqrt (n (n0 + 11))) := by simp only [pgD3]; pg_val
theorem pgD3_v30 : sEval n (pgD3 s0 n0) f (s0 + 30) =
    -(f (s0 + 24) / (Real.sqrt (f (s0 + 25)) * Real.sqrt (n (n0 + 11)))) := by simp only [pgD3]; pg_val
theorem pgRhoL_v19 : sEval n (pgRhoL s0) f (s0 + 19) = 162 * f (s0 + 48) * Real.sqrt (Real.log (1 + f (s0 + 19))) := by
  simp only [pgRhoL]; pg_val
theorem pgRhoL_v42 : sEval n (pgRhoL s0) f (s0 + 42) = f (s0 + 42) + f (s0 + 42) := by simp only [pgRhoL]; pg_val
end blocks

theorem pgParAL_ok {s0 : ℕ} (hs0 : s0 + 64 ≤ L.NS) : (pgParAL s0).all (SI.ok L) = true := by
  simp only [pgParAL, pgA1, pgA2, pgA3, pgA4, pgA5, pgA6, List.cons_append, List.nil_append, List.all_cons,
    List.all_nil, SI.ok, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq]
  omega

theorem sCost_pgParAL (s0 : ℕ) : sCost (pgParAL s0) = 22 := by
  simp only [sCost, pgParAL, pgA1, pgA2, pgA3, pgA4, pgA5, pgA6, List.cons_append, List.nil_append, List.map_cons,
    List.map_nil, SI.cost, List.sum_cons, List.sum_nil]
  norm_num

theorem pgParAL_dst {s0 x : ℕ}
    (hx : x ∉ [s0 + 2, s0 + 20, s0 + 21, s0 + 22, s0 + 23, s0 + 24, s0 + 32, s0 + 45, s0 + 46]) :
    x ∉ (pgParAL s0).map SI.dst := by
  simp only [pgParAL, pgA1, pgA2, pgA3, pgA4, pgA5, pgA6, List.cons_append, List.nil_append, List.map_cons,
    List.map_nil, SI.dst, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
  omega

theorem runs_pgParA {n0 s0 : ℕ} {ρ : ℝ} (σ : Env d) (hn0 : n0 + 20 ≤ L.NN) (hs0 : s0 + 64 ≤ L.NS)
    (hρ : σ.sc (s0 + 19) = ρ) (hdR : σ.sc (s0 + 48) = d) :
    Runs L w (pgParA L s0) σ 22
      (fun σ' => σ'.sc (s0 + 2) = 1 ∧ σ'.sc (s0 + 20) = pgLam ρ ∧ σ'.sc (s0 + 21) = pgTmin d ρ ∧
        σ'.sc (s0 + 22) = pgLD ρ ∧ σ'.sc (s0 + 23) = pgKappa * ρ ∧ σ'.sc (s0 + 24) = pgDelta d ρ ∧
        σ'.sc (s0 + 32) = -(pgKappa / d) ∧
        Env.Frame σ σ' [] [s0 + 2, s0 + 20, s0 + 21, s0 + 22, s0 + 23, s0 + 24, s0 + 32, s0 + 45, s0 + 46] []) := by
  refine runs_mono (runs_sprog (pgParAL s0) (pgParAL_ok hs0) σ) (by rw [sCost_pgParAL]) ?_
  rintro σ' rfl
  set F := sEval σ.nat (pgParAL s0) σ.sc with hF
  have e : F = sEval σ.nat (pgA6 s0) (sEval σ.nat (pgA5 s0) (sEval σ.nat (pgA4 s0)
      (sEval σ.nat (pgA3 s0) (sEval σ.nat (pgA2 s0) (sEval σ.nat (pgA1 s0) σ.sc))))) := by
    simp only [hF, pgParAL, sEval_append]
  have h2 : F (s0 + 2) = 1 := by
    rw [e]; simp (disch := simp [pgA2, pgA3, pgA4, pgA5, pgA6, SI.dst]) only [sEval_frame, pgA1_v2]
  have h20 : F (s0 + 20) = pgLam ρ := by
    rw [e]; simp (disch := simp [pgA2, pgA3, pgA4, pgA5, pgA6, SI.dst]) only [sEval_frame, pgA1_v20, hρ]
    rw [pgLam]
  have h22 : F (s0 + 22) = pgLD ρ := by
    rw [e]; simp (disch := simp [pgA1, pgA3, pgA4, pgA5, pgA6, SI.dst]) only [sEval_frame, pgA2_v22, hρ]
    rw [pgLD, pgKappa, pgPB]; ring
  have h21 : F (s0 + 21) = pgTmin d ρ := by
    rw [e]; simp (disch := simp [pgA1, pgA2, pgA3, pgA4, pgA5, pgA6, SI.dst]) only [sEval_frame, pgA3_v21,
      pgA1_v2, pgA1_v20, hρ, hdR]
    rw [pgTmin, pgLam]
  have h23 : F (s0 + 23) = pgKappa * ρ := by
    rw [e]; simp (disch := simp [pgA1, pgA2, pgA3, pgA5, pgA6, SI.dst]) only [sEval_frame, pgA4_v23, hρ]
    rw [pgKappa]; try ring
  have h24 : F (s0 + 24) = pgDelta d ρ := by
    rw [e]; simp (disch := simp [pgA1, pgA2, pgA3, pgA4, pgA6, SI.dst]) only [sEval_frame, pgA5_v24, pgA4_v23,
      hρ, hdR]
    rw [pgDelta, pgKappa, pgPB]; norm_num
  have h32 : F (s0 + 32) = -(pgKappa / d) := by
    rw [e]; simp (disch := simp [pgA1, pgA2, pgA3, pgA4, pgA5, SI.dst]) only [sEval_frame, pgA6_v32, hdR]
    rw [pgKappa]; try ring
  refine ⟨h2, h20, h21, h22, h23, h24, h32, fun _ _ => rfl, fun x hx => ?_, fun _ _ => rfl, rfl, rfl, rfl⟩
  exact sEval_frame _ _ _ (pgParAL_dst hx)

/-- The blocks of a list of scalar instructions unfolded to their instructions. -/
macro "pg_unfold" : tactic => `(tactic| simp only [pgParAL, pgParBL, pgParC1L, pgRhoL, pgA1, pgA2, pgA3, pgA4, pgA5,
  pgA6, pgB1, pgB2, pgB3, pgB4, pgB5, pgC1, pgC2, pgC3, pgC4, pgD1, pgD2, pgD3, List.cons_append, List.nil_append])

theorem pgParBL_ok {s0 : ℕ} (hs0 : s0 + 64 ≤ L.NS) : (pgParBL s0).all (SI.ok L) = true := by
  pg_unfold; simp only [List.all_cons, List.all_nil, SI.ok, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq]
  omega

theorem sCost_pgParBL (s0 : ℕ) : sCost (pgParBL s0) = 36 := by
  pg_unfold; simp only [sCost, List.map_cons, List.map_nil, SI.cost, List.sum_cons, List.sum_nil]; norm_num

theorem pgParBL_dst {s0 x : ℕ} (hx : x ∉ [s0 + 25, s0 + 26, s0 + 27, s0 + 28, s0 + 45, s0 + 46, s0 + 47]) :
    x ∉ (pgParBL s0).map SI.dst := by
  pg_unfold
  simp only [List.map_cons, List.map_nil, SI.dst, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
  omega

theorem runs_pgParB {n0 s0 : ℕ} {ρ : ℝ} (σ : Env d) (hn0 : n0 + 20 ≤ L.NN) (hs0 : s0 + 64 ≤ L.NS)
    (hdR : σ.sc (s0 + 48) = d) (ho : σ.sc (s0 + 2) = 1) (hlam : σ.sc (s0 + 20) = pgLam ρ)
    (htmin : σ.sc (s0 + 21) = pgTmin d ρ) (htmax : σ.sc (s0 + 22) = pgLD ρ) (hDel : σ.sc (s0 + 24) = pgDelta d ρ) :
    Runs L w (pgParB L s0) σ 36
      (fun σ' => σ'.sc (s0 + 25) = pgG2 d ρ ∧ σ'.sc (s0 + 26) = pgEh d ρ ∧ σ'.sc (s0 + 27) = pgEta d ρ ∧
        σ'.sc (s0 + 28) = pgTaub d ρ ∧
        Env.Frame σ σ' [] [s0 + 25, s0 + 26, s0 + 27, s0 + 28, s0 + 45, s0 + 46, s0 + 47] []) := by
  refine runs_mono (runs_sprog (pgParBL s0) (pgParBL_ok hs0) σ) (by rw [sCost_pgParBL]) ?_
  rintro σ' rfl
  set F := sEval σ.nat (pgParBL s0) σ.sc with hF
  have e : F = sEval σ.nat (pgB5 s0) (sEval σ.nat (pgB4 s0) (sEval σ.nat (pgB3 s0) (sEval σ.nat (pgB2 s0)
      (sEval σ.nat (pgB1 s0) σ.sc)))) := by
    simp only [hF, pgParBL, sEval_append]
  have h25 : F (s0 + 25) = pgG2 d ρ := by
    rw [e]; simp (disch := pg_unfold; simp [SI.dst]) only [sEval_frame, pgB2_v25, pgB1_v45, hdR, htmin, htmax]
    rw [pgG2, pgKappa]; ring
  have h26 : F (s0 + 26) = pgEh d ρ := by
    rw [e]; simp (disch := pg_unfold; simp [SI.dst]) only [sEval_frame, pgB3_v26, hdR, hlam, htmax]
    rw [pgEh, pgKappa]; ring
  have h27 : F (s0 + 27) = pgEta d ρ := by
    rw [e]; simp (disch := pg_unfold; simp [SI.dst]) only [sEval_frame, pgB4_v27, pgB3_v26, hdR, hlam, htmax,
      htmin, ho, hDel]
    rw [pgEta, pgEh, pgKappa]; try ring
  have h28 : F (s0 + 28) = pgTaub d ρ := by
    rw [e]; simp (disch := pg_unfold; simp [SI.dst]) only [sEval_frame, pgB5_v28, hdR, hlam]
    rw [pgTaub, pgKappa]; try ring
  exact ⟨h25, h26, h27, h28, fun _ _ => rfl, fun x hx => sEval_frame _ _ _ (pgParBL_dst hx), fun _ _ => rfl, rfl, rfl,
    rfl⟩

theorem runs_pgRho {s0 : ℕ} (σ : Env d) (hs0 : s0 + 64 ≤ L.NS) (hdR : σ.sc (s0 + 48) = d) :
    Runs L w (pgRho L s0) σ 8
      (fun σ' => σ'.sc (s0 + 19) = 3 * (54 * d * Real.sqrt (Real.log (1 + σ.sc (s0 + 19)))) ∧
        σ'.sc (s0 + 42) = 2 * σ.sc (s0 + 42) ∧
        Env.Frame σ σ' [] [s0 + 2, s0 + 19, s0 + 42, s0 + 45, s0 + 46] []) := by
  have hok : (pgRhoL s0).all (SI.ok L) = true := by
    pg_unfold; simp only [List.all_cons, List.all_nil, SI.ok, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq]
    omega
  have hc : sCost (pgRhoL s0) = 8 := by
    pg_unfold; simp only [sCost, List.map_cons, List.map_nil, SI.cost, List.sum_cons, List.sum_nil]; norm_num
  refine runs_mono (runs_sprog (pgRhoL s0) hok σ) hc.le ?_
  rintro σ' rfl
  refine ⟨?_, ?_, fun _ _ => rfl, fun x hx => sEval_frame _ _ _ ?_, fun _ _ => rfl, rfl, rfl, rfl⟩
  · show sEval σ.nat (pgRhoL s0) σ.sc (s0 + 19) = _
    rw [pgRhoL_v19, hdR]; ring
  · show sEval σ.nat (pgRhoL s0) σ.sc (s0 + 42) = _
    rw [pgRhoL_v42]; ring
  · pg_unfold
    simp only [List.map_cons, List.map_nil, SI.dst, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
    omega

theorem runs_pgParC1 {one n0 s0 : ℕ} {ρ : ℝ} (σ : Env d) (hn0 : n0 + 20 ≤ L.NN) (hs0 : s0 + 64 ≤ L.NS)
    (hone : one < L.NN) (honeb : one < n0 ∨ n0 + 20 ≤ one) (h1 : σ.nat one = 1)
    (hdR : σ.sc (s0 + 48) = d) (ho : σ.sc (s0 + 2) = 1) (hlam : σ.sc (s0 + 20) = pgLam ρ)
    (htmax : σ.sc (s0 + 22) = pgLD ρ) :
    Runs L w (pgParC1 L one n0 s0) σ (pgNT d ρ * 4 + 28)
      (fun σ' => σ'.nat (n0 + 12) = pgNT d ρ ∧
        Env.Frame σ σ' [n0 + 12] [s0 + 45, s0 + 46, s0 + 47, s0 + 50] []) := by
  have hok : (pgParC1L s0).all (SI.ok L) = true := by
    pg_unfold; simp only [List.all_cons, List.all_nil, SI.ok, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq]
    omega
  have hc : sCost (pgParC1L s0) = 24 := by
    pg_unfold; simp only [sCost, List.map_cons, List.map_nil, SI.cost, List.sum_cons, List.sum_nil]; norm_num
  set F := sEval σ.nat (pgParC1L s0) σ.sc with hF
  have hv : F (s0 + 45) = pgNTreal d ρ := by
    simp only [hF, pgParC1L, sEval_append, pgC4_v45]
    simp (disch := pg_unfold; simp [SI.dst]) only [sEval_frame, pgC1_v45, pgC2_v46, pgC3_v47, hdR, ho, hlam, htmax]
    rw [pgNTreal, pgKappa]; ring_nf
  have hdst : ∀ x, x ∉ [s0 + 45, s0 + 46, s0 + 47, s0 + 50] → F x = σ.sc x := fun x hx =>
    sEval_frame _ _ _ (by
      pg_unfold
      simp only [List.map_cons, List.map_nil, SI.dst, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      omega)
  have hs := runs_seq_eq (runs_sprog (L := L) (w := w) (pgParC1L s0) hok σ)
    (runs_nceil (L := L) (w := w) { σ with sc := F } (i := n0 + 12) (one := one) (x := s0 + 45) (t := s0 + 46)
      (by omega) hone (by omega) (by omega) (by omega) (by omega) h1)
  refine runs_mono hs ?_ ?_
  · show sCost (pgParC1L s0) + (⌈F (s0 + 45)⌉₊ * 4 + 4) ≤ _
    rw [hc, hv, pgNT]; omega
  · rintro σ' rfl
    refine ⟨?_, fun k hk => ?_, fun x hx => ?_, fun _ _ => rfl, rfl, rfl, rfl⟩
    · show (if n0 + 12 = n0 + 12 then ⌈F (s0 + 45)⌉₊ else σ.nat (n0 + 12)) = _
      rw [if_pos rfl, hv, pgNT]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      simp [hk]
    · have h46 : x ≠ s0 + 46 := fun h => hx (by simp [h])
      simp only [Env.setSc_sc, h46, if_false, Env.setNat_sc]
      exact hdst x hx

theorem runs_pgParC2 {one n0 s0 : ℕ} {ρ : ℝ} (σ : Env d) (hn0 : n0 + 20 ≤ L.NN) (hs0 : s0 + 64 ≤ L.NS)
    (hone : one < L.NN) (honeb : one < n0 ∨ n0 + 20 ≤ one) (h1 : σ.nat one = 1)
    (hρ : σ.sc (s0 + 19) = ρ) (hDel : σ.sc (s0 + 24) = pgDelta d ρ) (hG2 : σ.sc (s0 + 25) = pgG2 d ρ)
    (heh : σ.sc (s0 + 26) = pgEh d ρ) (heta : σ.sc (s0 + 27) = pgEta d ρ) :
    Runs L w (pgParC2 L one n0 s0) σ (pgNs d ρ * 4 + pgJb d ρ * 4 + 26)
      (fun σ' => σ'.nat (n0 + 11) = pgNs d ρ ∧ σ'.nat (n0 + 10) = pgJb d ρ ∧
        σ'.sc (s0 + 29) = pgStepSize d ρ ∧ σ'.sc (s0 + 30) = -pgStepSize d ρ ∧
        Env.Frame σ σ' [n0 + 10, n0 + 11] [s0, s0 + 29, s0 + 30, s0 + 45, s0 + 46] []) := by
  have ok1 : (pgD1 s0).all (SI.ok L) = true := by
    simp only [pgD1, List.all_cons, List.all_nil, SI.ok, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq]; omega
  have ok2 : (pgD2 s0).all (SI.ok L) = true := by
    simp only [pgD2, List.all_cons, List.all_nil, SI.ok, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq]; omega
  have ok3 : (pgD3 s0 n0).all (SI.ok L) = true := by
    simp only [pgD3, List.all_cons, List.all_nil, SI.ok, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq]; omega
  -- the first block and `N`
  set F1 := sEval σ.nat (pgD1 s0) σ.sc with hF1
  have v1 : F1 (s0 + 45) = pgNreal d ρ := by
    rw [hF1, pgD1_v45, hDel, hG2, heh, pgNreal]; ring
  have f1 : ∀ x, x ∉ [s0 + 45, s0 + 46] → F1 x = σ.sc x := fun x hx => sEval_frame _ _ _ (by
    simp only [pgD1, List.map_cons, List.map_nil, SI.dst, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
    omega)
  set σ2 := ({ σ with sc := F1 } : Env d).setNat (n0 + 11) ⌈F1 (s0 + 45)⌉₊ |>.setSc (s0 + 46) (⌈F1 (s0 + 45)⌉₊ : ℝ)
    with hσ2
  have hN : ⌈F1 (s0 + 45)⌉₊ = pgNs d ρ := by rw [v1, pgNs]
  -- the second block and `j`
  set F2 := sEval σ2.nat (pgD2 s0) σ2.sc with hF2
  have e19 : σ2.sc (s0 + 19) = ρ := by
    simp only [σ2, Env.setSc_sc, Env.setNat_sc]; rw [if_neg (by omega), f1 _ (by simp), hρ]
  have e27 : σ2.sc (s0 + 27) = pgEta d ρ := by
    simp only [σ2, Env.setSc_sc, Env.setNat_sc]; rw [if_neg (by omega), f1 _ (by simp), heta]
  have v2 : F2 (s0 + 45) = Real.logb 2 (ρ / pgEta d ρ) := by
    rw [hF2, pgD2_v45, e19, e27, Real.logb]
  have f2 : ∀ x, x ∉ [s0 + 45, s0 + 46] → F2 x = σ2.sc x := fun x hx => sEval_frame _ _ _ (by
    simp only [pgD2, List.map_cons, List.map_nil, SI.dst, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
    omega)
  have h12 : σ2.nat one = 1 := by
    simp only [σ2, Env.setSc_nat, Env.setNat_nat]; rw [if_neg (by omega)]; exact h1
  set σ4 := ({ σ2 with sc := F2 } : Env d).setNat (n0 + 10) ⌈F2 (s0 + 45)⌉₊ |>.setSc (s0 + 46) (⌈F2 (s0 + 45)⌉₊ : ℝ)
    with hσ4
  have hJ : ⌈F2 (s0 + 45)⌉₊ = pgJb d ρ := by rw [v2, pgJb]
  -- the third block: the step
  set F3 := sEval σ4.nat (pgD3 s0 n0) σ4.sc with hF3
  have n11 : σ4.nat (n0 + 11) = pgNs d ρ := by simp [σ4, σ2, hN]
  have e24 : σ4.sc (s0 + 24) = pgDelta d ρ := by
    have a : σ4.sc (s0 + 24) = F2 (s0 + 24) := by simp [σ4]
    have b : σ2.sc (s0 + 24) = F1 (s0 + 24) := by simp [σ2]
    rw [a, f2 (s0 + 24) (by simp), b, f1 (s0 + 24) (by simp), hDel]
  have e25 : σ4.sc (s0 + 25) = pgG2 d ρ := by
    have a : σ4.sc (s0 + 25) = F2 (s0 + 25) := by simp [σ4]
    have b : σ2.sc (s0 + 25) = F1 (s0 + 25) := by simp [σ2]
    rw [a, f2 (s0 + 25) (by simp), b, f1 (s0 + 25) (by simp), hG2]
  have v29 : F3 (s0 + 29) = pgStepSize d ρ := by rw [hF3, pgD3_v29, e24, e25, n11, pgStepSize]
  have v30 : F3 (s0 + 30) = -pgStepSize d ρ := by rw [hF3, pgD3_v30, e24, e25, n11, pgStepSize]
  have f3 : ∀ x, x ∉ [s0 + 45, s0 + 46, s0 + 29, s0, s0 + 30] → F3 x = σ4.sc x := fun x hx => sEval_frame _ _ _ (by
    simp only [pgD3, List.map_cons, List.map_nil, SI.dst, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
    omega)
  have hc3 : sCost (pgD3 s0 n0) = 7 := by
    simp only [pgD3, sCost, List.map_cons, List.map_nil, SI.cost, List.sum_cons, List.sum_nil]; rfl
  have hc1 : sCost (pgD1 s0) = 6 := by
    simp only [pgD1, sCost, List.map_cons, List.map_nil, SI.cost, List.sum_cons, List.sum_nil]; rfl
  have hc2 : sCost (pgD2 s0) = 5 := by
    simp only [pgD2, sCost, List.map_cons, List.map_nil, SI.cost, List.sum_cons, List.sum_nil]; rfl
  have hs := runs_seq_eq (runs_sprog (L := L) (w := w) (pgD1 s0) ok1 σ)
    (runs_seq_eq (runs_nceil (L := L) (w := w) { σ with sc := F1 } (i := n0 + 11) (one := one) (x := s0 + 45)
      (t := s0 + 46) (by omega) hone (by omega) (by omega) (by omega) (by omega) h1)
      (runs_seq_eq (runs_sprog (L := L) (w := w) (pgD2 s0) ok2 σ2)
        (runs_seq_eq (runs_nceil (L := L) (w := w) { σ2 with sc := F2 } (i := n0 + 10) (one := one) (x := s0 + 45)
          (t := s0 + 46) (by omega) hone (by omega) (by omega) (by omega) (by omega) h12)
          (runs_sprog (L := L) (w := w) (pgD3 s0 n0) ok3 σ4))))
  refine runs_mono hs ?_ ?_
  · show sCost (pgD1 s0) + ((⌈F1 (s0 + 45)⌉₊ * 4 + 4) + (sCost (pgD2 s0) + ((⌈F2 (s0 + 45)⌉₊ * 4 + 4) +
      sCost (pgD3 s0 n0)))) ≤ _
    rw [hc1, hc2, hc3, hN, hJ]; omega
  · rintro σ' rfl
    refine ⟨n11, ?_, v29, v30, fun k hk => ?_, fun x hx => ?_, fun _ _ => rfl, rfl, rfl, rfl⟩
    · show σ4.nat (n0 + 10) = _
      simp [σ4, hJ]
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hk
      show σ4.nat k = _
      simp [σ4, σ2, hk.1, hk.2]
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
      show F3 x = _
      have a : σ4.sc x = F2 x := by simp [σ4, hx.2.2.2.2]
      have b : σ2.sc x = F1 x := by simp [σ2, hx.2.2.2.2]
      rw [f3 x (by simp; omega), a, f2 x (by simp; omega), b, f1 x (by simp; omega)]

section blocksK

variable (n : ℕ → ℕ) (f : ℕ → ℝ) (s0 n0 : ℕ)

theorem pgK1_v45 {dv r0v R0v : ℕ} (h1 : R0v ≠ s0 + 48) (h2 : R0v ≠ s0 + 2) (h3 : r0v ≠ s0 + 48)
    (h4 : r0v ≠ s0 + 2) :
    sEval n (pgK1 dv r0v R0v s0) f (s0 + 45) = Real.log (f R0v / f r0v) / Real.log 2 := by
  simp only [pgK1, sEval, List.foldl, SI.step, SI.dst, SI.val, Function.update_apply, Op2.eval, Op1.eval]
  simp [h1, h2, h3, h4]
theorem pgK1_v48 {dv r0v R0v : ℕ} : sEval n (pgK1 dv r0v R0v s0) f (s0 + 48) = (n dv : ℝ) := by
  simp only [pgK1]; pg_val
theorem pgK1_v2 {dv r0v R0v : ℕ} : sEval n (pgK1 dv r0v R0v s0) f (s0 + 2) = 1 := by simp only [pgK1]; pg_val
theorem pgK2_v43 {δv : ℕ} (h : δv ≠ s0 + 45) : sEval n (pgK2 δv n0 s0) f (s0 + 43) = f δv / (n (n0 + 18) : ℝ) := by
  simp only [pgK2, sEval, List.foldl, SI.step, SI.dst, SI.val, Function.update_apply, Op2.eval, Op1.eval]
  simp [h]
theorem pgK2_v45 {δv : ℕ} (h : δv ≠ s0 + 45) :
    sEval n (pgK2 δv n0 s0) f (s0 + 45) = Real.log (4 / (f δv / (n (n0 + 18) : ℝ))) / Real.log 2 := by
  simp only [pgK2, sEval, List.foldl, SI.step, SI.dst, SI.val, Function.update_apply, Op2.eval, Op1.eval]
  simp [h]
theorem pgK3_v45 : sEval n (pgK3 n0 s0) f (s0 + 45) = 8 * Real.log (2 * (n (n0 + 16) : ℝ) / f (s0 + 43)) := by
  simp only [pgK3]; pg_val

end blocksK

/-- A straight-line scalar block changes only the scalars it writes. -/
theorem frame_sprog (σ : Env d) (l : List SI) {ns ss as : List ℕ} (h : ∀ x ∈ l.map SI.dst, x ∈ ss) :
    Env.Frame σ { σ with sc := sEval σ.nat l σ.sc } ns ss as :=
  ⟨fun _ _ => rfl, fun _ hx => sEval_frame _ _ _ (fun h' => hx (h _ h')), fun _ _ => rfl, rfl, rfl, rfl⟩

theorem runs_pgCaps {dv one r0v R0v δv n0 s0 : ℕ} {r0 R0 δ₁ : ℝ} (σ : Env d) (hn0 : n0 + 20 ≤ L.NN)
    (hs0 : s0 + 64 ≤ L.NS) (hdv : dv < L.NN) (hone : one < L.NN)
    (hdvb : dv < n0 ∨ n0 + 20 ≤ dv) (honeb : one < n0 ∨ n0 + 20 ≤ one) (hr0v : r0v < L.NS) (hR0v : R0v < L.NS)
    (hδv : δv < L.NS) (hr0b : r0v < s0 ∨ s0 + 64 ≤ r0v) (hR0b : R0v < s0 ∨ s0 + 64 ≤ R0v)
    (hδb : δv < s0 ∨ s0 + 64 ≤ δv) (hd : σ.nat dv = d) (h1 : σ.nat one = 1) (hr0 : σ.sc r0v = r0)
    (hR0 : σ.sc R0v = R0) (hδ : σ.sc δv = δ₁) :
    Runs L w (pgCaps L dv one r0v R0v δv n0 s0) σ
      (kCaps d ⌈Real.logb 2 (R0 / r0)⌉₊ (pgJr (δ₁ / pgStages r0 R0)) (pgMT (δ₁ / pgStages r0 R0)))
      (fun σ' => σ'.nat (n0 + 9) = d * d ∧ σ'.sc (s0 + 48) = d ∧ σ'.sc (s0 + 2) = 1 ∧
        σ'.nat (n0 + 18) = pgStages r0 R0 ∧ σ'.sc (s0 + 43) = δ₁ / pgStages r0 R0 ∧
        σ'.nat (n0 + 16) = pgJr (δ₁ / pgStages r0 R0) ∧ σ'.nat (n0 + 14) = pgMT (δ₁ / pgStages r0 R0) ∧
        Env.Frame σ σ' [n0, n0 + 9, n0 + 14, n0 + 16, n0 + 18] [s0 + 2, s0 + 43, s0 + 45, s0 + 46, s0 + 48] []) := by
  have ok1 : (pgK1 dv r0v R0v s0).all (SI.ok L) = true := by
    simp only [pgK1, List.all_cons, List.all_nil, SI.ok, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq]; omega
  have ok2 : (pgK2 δv n0 s0).all (SI.ok L) = true := by
    simp only [pgK2, List.all_cons, List.all_nil, SI.ok, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq]; omega
  have ok3 : (pgK3 n0 s0).all (SI.ok L) = true := by
    simp only [pgK3, List.all_cons, List.all_nil, SI.ok, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq]; omega
  have hc1 : sCost (pgK1 dv r0v R0v s0) = 7 := by
    simp only [pgK1, sCost, List.map_cons, List.map_nil, SI.cost, List.sum_cons, List.sum_nil]; rfl
  have hc2 : sCost (pgK2 δv n0 s0) = 8 := by
    simp only [pgK2, sCost, List.map_cons, List.map_nil, SI.cost, List.sum_cons, List.sum_nil]; rfl
  have hc3 : sCost (pgK3 n0 s0) = 7 := by
    simp only [pgK3, sCost, List.map_cons, List.map_nil, SI.cost, List.sum_cons, List.sum_nil]; rfl
  set m0 := ⌈Real.logb 2 (R0 / r0)⌉₊ with hm0
  have hst : pgStages r0 R0 = max 1 m0 := rfl
  set δ' := δ₁ / pgStages r0 R0 with hδ'
  unfold pgCaps
  refine runs_mono (K := (d * 4 + 4) + (sCost (pgK1 dv r0v R0v s0) + ((m0 * 4 + 4) + (2 + (sCost (pgK2 δv n0 s0) +
    ((pgJr δ' * 4 + 4) + (sCost (pgK3 n0 s0) + (pgMT δ' * 4 + 4)))))))) ?_ (by rw [hc1, hc2, hc3, kCaps]; omega)
    (fun _ h => h)
  refine runs_seq (runs_nsq σ hdv hone (i := n0) (dd := n0 + 9) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) hd h1) fun σ1 h1' => ?_
  obtain ⟨hdd1, hF1⟩ := h1'
  have hd1 : σ1.nat dv = d := by rw [hF1.1 _ (by simp <;> omega)]; exact hd
  have h11 : σ1.nat one = 1 := by rw [hF1.1 _ (by simp <;> omega)]; exact h1
  have hsc1 : ∀ x, σ1.sc x = σ.sc x := fun x => hF1.2.1 x (by simp)
  -- the block K1 and `m`
  set G1 := sEval σ1.nat (pgK1 dv r0v R0v s0) σ1.sc with hG1
  have g45 : G1 (s0 + 45) = Real.logb 2 (R0 / r0) := by
    rw [hG1, pgK1_v45 _ _ _ (by omega) (by omega) (by omega) (by omega), hsc1, hsc1, hR0, hr0, Real.logb]
  have g1 : ∀ x, x ∉ [s0 + 2, s0 + 45, s0 + 46, s0 + 48] → G1 x = σ.sc x := fun x hx => by
    rw [hG1, sEval_frame _ _ _ (by
      simp only [pgK1, List.map_cons, List.map_nil, SI.dst, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      omega), hsc1]
  refine runs_seq_eq (runs_sprog (L := L) (w := w) (pgK1 dv r0v R0v s0) ok1 σ1) ?_
  refine runs_seq (runs_mono (runs_nceil (L := L) (w := w) { σ1 with sc := G1 } (i := n0 + 18) (one := one)
    (x := s0 + 45) (t := s0 + 46) (by omega) hone (by omega) (by omega) (by omega) (by omega) h11)
    (show ⌈G1 (s0 + 45)⌉₊ * 4 + 4 ≤ m0 * 4 + 4 by rw [g45]) (fun _ h => h)) fun σ3 h3 => ?_
  have n318 : σ3.nat (n0 + 18) = m0 := by rw [h3]; simp [g45, hm0]
  have n3 : ∀ k, k ≠ n0 + 18 → σ3.nat k = σ1.nat k := fun k hk => by rw [h3]; simp [hk]
  have sc3 : ∀ x, x ≠ s0 + 46 → σ3.sc x = G1 x := fun x hx => by rw [h3]; simp [hx]
  have n3one : σ3.nat one = 1 := by rw [n3 _ (by omega), h11]
  have F13 : Env.Frame σ1 σ3 [n0, n0 + 9, n0 + 14, n0 + 16, n0 + 18] [s0 + 2, s0 + 43, s0 + 45, s0 + 46, s0 + 48] []
      := by
    rw [h3]
    exact Env.Frame.setSc (Env.Frame.setNat (frame_sprog σ1 _ (by simp [pgK1, SI.dst])) (by simp) _) (by simp) _
  -- the floor `m ≥ 1`
  refine runs_seq (Q₁ := fun σ4 => σ4.nat (n0 + 18) = pgStages r0 R0 ∧ Env.Frame σ3 σ4 [n0 + 18] [] []) ?_
    fun σ4 h4 => ?_
  · by_cases hc : σ3.nat (n0 + 18) < σ3.nat one
    · refine runs_mono (runs_ifN_t (by omega) hone hc (runs_nconst (L := L) (w := w) (σ := σ3) (by omega) 1))
        (by norm_num) ?_
      rintro σ' rfl
      refine ⟨?_, Env.Frame.setNat (Env.Frame.refl σ3 _ _ _) (by simp) _⟩
      rw [n318, n3one] at hc
      rw [Env.setNat_nat, if_pos rfl, hst]; omega
    · refine runs_mono (runs_ifN_f (by omega) hone hc (runs_skip (L := L) (w := w) σ3)) (by norm_num) ?_
      intro σ' e; rw [e]
      refine ⟨?_, Env.Frame.refl σ3 _ _ _⟩
      rw [n318, n3one] at hc
      rw [n318, hst]; omega
  obtain ⟨n418, F34⟩ := h4
  have n4 : ∀ k, k ≠ n0 + 18 → σ4.nat k = σ3.nat k := fun k hk => F34.1 k (by simp [hk])
  have sc4 : ∀ x, σ4.sc x = σ3.sc x := fun x => F34.2.1 x (by simp)
  have n4one : σ4.nat one = 1 := by rw [n4 _ (by omega), n3one]
  -- the block K2 and `J`
  set G2 := sEval σ4.nat (pgK2 δv n0 s0) σ4.sc with hG2
  have e4δ : σ4.sc δv = δ₁ := by rw [sc4, sc3 _ (by omega), g1 _ (by simp <;> omega), hδ]
  have g243 : G2 (s0 + 43) = δ' := by rw [hG2, pgK2_v43 _ _ _ _ (by omega), e4δ, n418]
  have g245 : G2 (s0 + 45) = Real.logb 2 (4 / δ') := by
    rw [hG2, pgK2_v45 _ _ _ _ (by omega), e4δ, n418, Real.logb]
  have g2 : ∀ x, x ∉ [s0 + 43, s0 + 45, s0 + 46] → G2 x = σ4.sc x := fun x hx => sEval_frame _ _ _ (by
    simp only [pgK2, List.map_cons, List.map_nil, SI.dst, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
    omega)
  refine runs_seq_eq (runs_sprog (L := L) (w := w) (pgK2 δv n0 s0) ok2 σ4) ?_
  refine runs_seq (runs_mono (runs_nceil (L := L) (w := w) { σ4 with sc := G2 } (i := n0 + 16) (one := one)
    (x := s0 + 45) (t := s0 + 46) (by omega) hone (by omega) (by omega) (by omega) (by omega) n4one)
    (show ⌈G2 (s0 + 45)⌉₊ * 4 + 4 ≤ pgJr δ' * 4 + 4 by rw [g245, pgJr]) (fun _ h => h)) fun σ5 h5 => ?_
  have n516 : σ5.nat (n0 + 16) = pgJr δ' := by rw [h5]; simp [g245, pgJr]
  have n5 : ∀ k, k ≠ n0 + 16 → σ5.nat k = σ4.nat k := fun k hk => by rw [h5]; simp [hk]
  have sc5 : ∀ x, x ≠ s0 + 46 → σ5.sc x = G2 x := fun x hx => by rw [h5]; simp [hx]
  have n5one : σ5.nat one = 1 := by rw [n5 _ (by omega), n4one]
  have F45 : Env.Frame σ4 σ5 [n0, n0 + 9, n0 + 14, n0 + 16, n0 + 18] [s0 + 2, s0 + 43, s0 + 45, s0 + 46, s0 + 48] []
      := by
    rw [h5]
    exact Env.Frame.setSc (Env.Frame.setNat (frame_sprog σ4 _ (by simp [pgK2, SI.dst])) (by simp) _) (by simp) _
  -- the block K3 and `m_T`
  set G3 := sEval σ5.nat (pgK3 n0 s0) σ5.sc with hG3
  have g345 : G3 (s0 + 45) = 8 * Real.log (2 * pgJr δ' / δ') := by
    rw [hG3, pgK3_v45, n516, sc5 _ (by omega), g243]
  have g3 : ∀ x, x ∉ [s0 + 45, s0 + 46] → G3 x = σ5.sc x := fun x hx => sEval_frame _ _ _ (by
    simp only [pgK3, List.map_cons, List.map_nil, SI.dst, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
    omega)
  refine runs_seq_eq (runs_sprog (L := L) (w := w) (pgK3 n0 s0) ok3 σ5) ?_
  refine runs_mono (runs_nceil (L := L) (w := w) { σ5 with sc := G3 } (i := n0 + 14) (one := one)
    (x := s0 + 45) (t := s0 + 46) (by omega) hone (by omega) (by omega) (by omega) (by omega) n5one)
    (show ⌈G3 (s0 + 45)⌉₊ * 4 + 4 ≤ pgMT δ' * 4 + 4 by rw [g345, pgMT]) ?_
  rintro σ6 rfl
  have F56 : Env.Frame σ5 (({ σ5 with sc := G3 } : Env d).setNat (n0 + 14) ⌈G3 (s0 + 45)⌉₊ |>.setSc (s0 + 46)
      (⌈G3 (s0 + 45)⌉₊ : ℝ)) [n0, n0 + 9, n0 + 14, n0 + 16, n0 + 18]
      [s0 + 2, s0 + 43, s0 + 45, s0 + 46, s0 + 48] [] :=
    Env.Frame.setSc (Env.Frame.setNat (frame_sprog σ5 _ (by simp [pgK3, SI.dst])) (by simp) _) (by simp) _
  -- the scalars kept through the blocks
  have keep : ∀ x, x ∉ [s0 + 43, s0 + 45, s0 + 46] →
      G3 x = G1 x := fun x hx => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    rw [g3 _ (by simp; omega), sc5 _ hx.2.2, g2 _ (by simp; omega), sc4, sc3 _ hx.2.2]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Env.setSc_nat, Env.setNat_nat]
    rw [if_neg (by omega), n5 _ (by omega), n4 _ (by omega), n3 _ (by omega), hdd1]
  · simp only [Env.setSc_sc]
    rw [if_neg (by omega)]
    show G3 (s0 + 48) = _
    rw [keep _ (by simp), hG1, pgK1_v48, hd1]
  · simp only [Env.setSc_sc]
    rw [if_neg (by omega)]
    show G3 (s0 + 2) = _
    rw [keep _ (by simp), hG1, pgK1_v2]
  · simp only [Env.setSc_nat, Env.setNat_nat]
    rw [if_neg (by omega), n5 _ (by omega), n418]
  · simp only [Env.setSc_sc]
    rw [if_neg (by omega)]
    show G3 (s0 + 43) = _
    rw [g3 _ (by simp), sc5 _ (by omega), g243]
  · simp only [Env.setSc_nat, Env.setNat_nat]
    rw [if_neg (by omega), n516]
  · simp only [Env.setSc_nat, Env.setNat_nat]
    rw [if_pos trivial, g345, pgMT]
  · exact Env.Frame.trans (Env.Frame.mono hF1 (by simp) (by simp) (by simp))
      (Env.Frame.trans F13 (Env.Frame.trans (Env.Frame.mono F34 (by simp) (by simp) (by simp))
        (Env.Frame.trans F45 F56)))

end AdversarialBco.Poly.PG
