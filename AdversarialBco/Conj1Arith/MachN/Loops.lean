/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Conj1Arith.MachN.Clamp
public import AdversarialBco.Conj1Arith.Proc
public import AdversarialBco.Poly.MachPGBound

@[expose] public section

/-!
# The loops of PG-N with CLAMP-NS: the step, the descent, the verdict, the test, the repeat

The rules of the loops of the code of MachN/Code.lean: `runs_pgStepMNS` follows `runs_pgStepM`
(Poly/MachPGLeaves.lean), and the rules of the descent, the verdict, the test and the repeat are written on the same
pattern, over the states `PgAt` and `PgStageVars` of Poly/MachPGLoops.lean. The step runs `pgUpdNS` (`runs_pgUpdNS`)
and the verdict `pgVerdC3P` (`runs_pgVerdC3P`); the semantics is that of PG-N (`pgDescentN clampNSRoutine`,
`pgVerdictS`, `pgTestS`). The other leaves are those of `pgParts` and `pgLeaves` (Poly/MachPGParts.lean).
-/

open AdversarialBco AdversarialBco.RealRAM AdversarialBco.Poly AdversarialBco.Poly.Mach AdversarialBco.Poly.Mach.VL
  AdversarialBco.Poly.PG Matrix

namespace AdversarialBco.Conj1Arith

variable {d : ℕ}

/-! ## One step of the descent -/

theorem runs_pgStepMNS {d : ℕ} {L : Layout} {w : World d} {dv one n0 s0 a0 muv Av : ℕ}
    (σ : Env d) (hn0 : n0 + 20 ≤ L.NN) (hs0 : s0 + 64 ≤ L.NS) (ha0 : a0 + 32 ≤ L.NA) (hdv : dv < L.NN) (hone : one < L.NN)
    (hdvb : dv < n0 ∨ n0 + 20 ≤ dv) (honeb : one < n0 ∨ n0 + 20 ≤ one) (hd : σ.nat dv = d) (h1 : σ.nat one = 1)
    (hmuv : muv < L.NA) (hAv : Av < L.NA) (hmub : muv < a0 ∨ a0 + 32 ≤ muv) (hAb : Av < a0 ∨ a0 + 32 ≤ Av) (hdd : σ.nat (n0 + 9) = d * d)
    {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ : σ.sc (s0 + 19) = ρ) (htmin : σ.sc (s0 + 21) = pgTmin d ρ)
    (hLD : σ.sc (s0 + 22) = pgLD ρ) (hdR : σ.sc (s0 + 48) = d) (hN : σ.nat (n0 + 11) = pgNs d ρ) :
    Runs L w (pgStepNS L dv one n0 s0 a0 muv Av) σ
      (kStepNS d (σ.nat (n0 + 10)) (nsK d ρ) (Nat.clog 2 (3 * nsK d ρ + 3)) (nsCount (nsK d ρ)))
      (fun σ' =>
        let g : Fin d → ℝ := fun c => w.gs (σ.draws + c)
        let F := piTilde (pgBodySet w.K (σ.vec muv) (σ.mat Av) (σ.sc (s0 + 42))) (σ.sc (s0 + 19)) (σ.nat (n0 + 10))
          (WithLp.toLp 2 (σ.mat (a0 + 1) *ᵥ g + σ.vec a0))
        let B := (gjRun (σ.mat (a0 + 1)) d).2
        let G := vecMulVec g g - 1
        WithLp.toLp 2 (σ'.vec a0) =
            ballClip (σ.sc (s0 + 23)) (WithLp.toLp 2 (σ.vec a0 + σ.sc (s0 + 30) • (F • (B *ᵥ g)))) ∧
          σ'.mat (a0 + 1) = clampNSRoutine.run d (pgTmin d ρ) (pgLD ρ) (pgEpr d ρ)
            (σ.mat (a0 + 1) + σ.sc (s0 + 30) • ((F / 2) • (B * G + (B * G)ᵀ) + σ.sc (s0 + 32) • B)) ∧
          σ'.vec (a0 + 2) = σ.vec (a0 + 2) + σ.vec a0 ∧ σ'.mat (a0 + 3) = σ.mat (a0 + 3) + σ.mat (a0 + 1) ∧
          σ'.draws = σ.draws + d ∧
          Env.Frame σ { σ' with draws := σ.draws } (pgTmpN n0) (pgTmpS s0 ++ [s0 + 31, s0 + 34, s0 + 35, s0 + 36])
            [a0, a0 + 1, a0 + 2, a0 + 3, a0 + 4, a0 + 5, a0 + 6, a0 + 7, a0 + 8, a0 + 9, a0 + 10, a0 + 11, a0 + 12,
              a0 + 13, a0 + 14]) := by
  have nd : dv ∉ [n0, n0 + 1, n0 + 2, n0 + 3, n0 + 4, n0 + 5, n0 + 6, n0 + 7, n0 + 8] := by simp; omega
  have no : one ∉ [n0, n0 + 1, n0 + 2, n0 + 3, n0 + 4, n0 + 5, n0 + 6, n0 + 7, n0 + 8] := by simp; omega
  unfold pgStepNS kStepNS
  refine runs_seq_eq (runs_sconst (L := L) (w := w) (σ := σ) (x := s0 + 2) (by omega) 1) ?_
  set σ1 := σ.setSc (s0 + 2) ((1 : ℚ) : ℝ) with hσ1
  have e12 : σ1.sc (s0 + 2) = 1 := by simp [hσ1]
  refine runs_seq (runs_vaxpy (y := a0 + 2) (x := a0) (α := s0 + 2) (t1 := s0 + 8) (t2 := s0 + 9) σ1 hdv hone
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) hd h1) fun σ2 h2 => ?_
  obtain ⟨v2, F2, -⟩ := h2
  refine runs_seq (runs_mlin (C := a0 + 3) (A := a0 + 3) (B := a0 + 1) (α := s0 + 2) (β := s0 + 2) (t1 := s0 + 8)
    (t2 := s0 + 9) σ2 (by omega) hone (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    ((F2.1 _ (by simp)).trans hdd) ((F2.1 _ (by simp; omega)).trans h1)) fun σ3 h3 => ?_
  obtain ⟨m3, F3, -⟩ := h3
  have F03 : Env.Frame σ σ3 [n0] [s0 + 2, s0 + 8, s0 + 9] [a0 + 2, a0 + 3] :=
    Env.Frame.trans (Env.Frame.setSc (Env.Frame.refl σ [n0] [s0 + 2, s0 + 8, s0 + 9] [a0 + 2, a0 + 3]) (by simp) _)
      (Env.Frame.trans (Env.Frame.mono F2 (by simp) (by simp) (by simp)) (Env.Frame.mono F3 (by simp) (by simp) (by simp)))
  have d3 : σ3.nat dv = d := (F03.1 _ (by simp; omega)).trans hd
  have o3 : σ3.nat one = 1 := (F03.1 _ (by simp; omega)).trans h1
  refine runs_seq (runs_vgauss (y := a0 + 4) (t := s0 + 8) σ3 hdv hone (by omega) (by omega) (by omega) (by omega)
    (by omega) d3 o3) fun σ4 h4 => ?_
  obtain ⟨v4, dr4, n4, s4, a4, r4, p4, -⟩ := h4
  have F34 : Env.Frame σ3 { σ4 with draws := σ3.draws } [n0] [s0 + 8] [a0 + 4] :=
    ⟨fun j hj => n4 j (by simpa using hj), fun z hz => s4 z (by simpa using hz), fun b hb => a4 b (by simpa using hb),
      rfl, r4, p4⟩
  have F04 : Env.Frame σ { σ4 with draws := σ.draws } [n0] [s0 + 2, s0 + 8, s0 + 9] [a0 + 2, a0 + 3, a0 + 4] :=
    frameD_trans (frameD_of_frame (Env.Frame.mono F03 (by simp) (by simp) (by simp)))
      (Env.Frame.mono F34 (by simp) (by simp) (by simp))
  have n04 : ∀ i ∉ [n0], σ4.nat i = σ.nat i := F04.1
  have s04 : ∀ x ∉ [s0 + 2, s0 + 8, s0 + 9], σ4.sc x = σ.sc x := F04.2.1
  have a04 : ∀ a ∉ [a0 + 2, a0 + 3, a0 + 4], σ4.arr a = σ.arr a := F04.2.2.1
  have a34 : ∀ a ∉ [a0 + 4], σ4.arr a = σ3.arr a := F34.2.2.1
  have d4 : σ4.nat dv = d := (F04.1 _ (by simp; omega)).trans hd
  have o4 : σ4.nat one = 1 := (F04.1 _ (by simp; omega)).trans h1
  have j4 : σ4.nat (n0 + 10) = σ.nat (n0 + 10) := F04.1 _ (by simp)
  refine runs_seq (runs_mono (runs_pgGauge pgParts (xm := a0) (xT := a0 + 1) σ4 hn0 hs0 ha0 hdv hone hdvb honeb d4 o4 hmuv
    hAv hmub hAb (by omega) (by omega) (by simp) (by simp)) (by rw [j4]) (fun σ' h => h)) fun σ5 h5 => ?_
  obtain ⟨e518, F5⟩ := h5
  have d5 : σ5.nat dv = d := (F5.1 _ (by simp; omega)).trans d4
  have o5 : σ5.nat one = 1 := (F5.1 _ (by simp; omega)).trans o4
  have dd5 : σ5.nat (n0 + 9) = d * d := (F5.1 _ (by simp)).trans ((F04.1 _ (by simp)).trans hdd)
  refine runs_seq (runs_pgVinv pgParts σ5 hn0 hs0 ha0 hdv hone hdvb honeb d5 o5 dd5) fun σ6 h6 => ?_
  obtain ⟨m6, v6, F6⟩ := h6
  have d6 : σ6.nat dv = d := (F6.1 _ (by simp; omega)).trans d5
  have o6 : σ6.nat one = 1 := (F6.1 _ (by simp; omega)).trans o5
  have dd6 : σ6.nat (n0 + 9) = d * d := (F6.1 _ (by simp)).trans dd5
  refine runs_seq (runs_pgVmat pgParts σ6 hn0 hs0 ha0 hdv hone hdvb honeb d6 o6 dd6) fun σ7 h7 => ?_
  obtain ⟨m7, F7⟩ := h7
  have d7 : σ7.nat dv = d := (F7.1 _ (by simp; omega)).trans d6
  have o7 : σ7.nat one = 1 := (F7.1 _ (by simp; omega)).trans o6
  have dd7 : σ7.nat (n0 + 9) = d * d := (F7.1 _ (by simp)).trans dd6
  -- the frame from σ4 to σ7 and the values carried
  have F47 : Env.Frame σ4 σ7 [n0, n0 + 1, n0 + 2, n0 + 3, n0 + 4, n0 + 5, n0 + 6, n0 + 7, n0 + 8]
      (pgTmpS s0 ++ [s0 + 31, s0 + 36]) [a0 + 5, a0 + 6, a0 + 7, a0 + 8, a0 + 9, a0 + 10, a0 + 11, a0 + 12, a0 + 13,
        a0 + 14] :=
    Env.Frame.trans (Env.Frame.mono F5 (by simp) (by simp [pgTmpS]) (by simp))
      (Env.Frame.trans (Env.Frame.mono F6 (by simp) (by simp [pgTmpS]) (by simp))
        (Env.Frame.mono F7 (by simp) (by simp [pgTmpS]) (by simp)))
  have s47 : ∀ k, 19 ≤ k → k ≠ 31 → k ≠ 36 → σ7.sc (s0 + k) = σ.sc (s0 + k) := fun k hk h31 h36 => by
    rw [F47.2.1 _ (by simp [pgTmpS]; omega), F04.2.1 _ (by simp; omega)]
  have a7 : σ7.arr a0 = σ.arr a0 := by rw [F47.2.2.1 _ (by simp), F04.2.2.1 _ (by simp)]
  have a71 : σ7.arr (a0 + 1) = σ.arr (a0 + 1) := by rw [F47.2.2.1 _ (by simp), F04.2.2.1 _ (by simp)]
  have a51 : σ5.arr (a0 + 1) = σ.arr (a0 + 1) := by rw [F5.2.2.1 _ (by simp), F04.2.2.1 _ (by simp)]
  have a54 : σ5.vec (a0 + 4) = fun c : Fin d => w.gs (σ.draws + c) := by
    rw [Env.vec_of_arr (F5.2.2.1 _ (by simp)), v4, F03.2.2.2.1]
  have a64 : σ6.vec (a0 + 4) = fun c : Fin d => w.gs (σ.draws + c) := by
    rw [Env.vec_of_arr (F6.2.2.1 _ (by simp))]; exact a54
  have e618 : σ6.sc (s0 + 18) = σ5.sc (s0 + 18) := F6.2.1 _ (by simp)
  have e632 : σ6.sc (s0 + 32) = σ.sc (s0 + 32) := by
    rw [F6.2.1 _ (by simp), F5.2.1 _ (by simp [pgTmpS]), F04.2.1 _ (by simp)]
  have hF : σ5.sc (s0 + 18) = piTilde (pgBodySet w.K (σ.vec muv) (σ.mat Av) (σ.sc (s0 + 42))) (σ.sc (s0 + 19))
      (σ.nat (n0 + 10)) (WithLp.toLp 2 (σ.mat (a0 + 1) *ᵥ (fun c : Fin d => w.gs (σ.draws + c)) + σ.vec a0)) := by
    rw [e518, Env.vec_of_arr (a04 muv (by simp; omega)), Env.mat_of_arr (a04 Av (by simp; omega)),
      s04 (s0 + 42) (by simp), s04 (s0 + 19) (by simp), j4, Env.mat_of_arr (a04 (a0 + 1) (by simp)),
      Env.vec_of_arr (a04 a0 (by simp)), v4, F03.2.2.2.1]
  have n7 : σ7.nat (n0 + 11) = σ.nat (n0 + 11) := by rw [F47.1 _ (by simp), F04.1 _ (by simp)]
  refine runs_mono (runs_pgUpdNS σ7 hn0 hs0 ha0 hdv hone hdvb honeb d7 o7 dd7 hρ0
    ((s47 19 (by omega) (by omega) (by omega)).trans hρ) ((s47 21 (by omega) (by omega) (by omega)).trans htmin)
    ((s47 22 (by omega) (by omega) (by omega)).trans hLD) ((s47 48 (by omega) (by omega) (by omega)).trans hdR)
    (n7.trans hN)) le_rfl fun σ8 h8 => ?_
  obtain ⟨v8, m8, F8⟩ := h8
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [v8, s47 23 (by omega) (by omega) (by omega), s47 30 (by omega) (by omega) (by omega), Env.vec_of_arr a7,
      Env.vec_of_arr (F7.2.2.1 _ (by simp)), v6, hF, Env.mat_of_arr a51, a54]
  · rw [m8,
      s47 30 (by omega) (by omega) (by omega), Env.mat_of_arr a71, m7, m6, e618, e632, hF, Env.mat_of_arr a51, a64]
  · rw [Env.vec_of_arr (F8.2.2.1 _ (by simp)), Env.vec_of_arr (F47.2.2.1 _ (by simp)),
      Env.vec_of_arr (a34 _ (by simp)), Env.vec_of_arr (F3.2.2.1 _ (by simp)), v2, e12, one_smul]
    rfl
  · rw [Env.mat_of_arr (F8.2.2.1 _ (by simp)), Env.mat_of_arr (F47.2.2.1 _ (by simp)),
      Env.mat_of_arr (a34 _ (by simp)), m3, F2.2.1 _ (by simp), e12, one_smul, one_smul,
      Env.mat_of_arr (F2.2.2.1 (a0 + 1) (by simp)), Env.mat_of_arr (F2.2.2.1 (a0 + 3) (by simp))]
    rfl
  · rw [F8.2.2.2.1, F47.2.2.2.1, dr4, F03.2.2.2.1]
  · have F48 : Env.Frame σ4 σ8 (pgTmpN n0) (pgTmpS s0 ++ [s0 + 31, s0 + 34, s0 + 35, s0 + 36])
        [a0, a0 + 1, a0 + 2, a0 + 3, a0 + 4, a0 + 5, a0 + 6, a0 + 7, a0 + 8, a0 + 9, a0 + 10, a0 + 11, a0 + 12, a0 + 13,
          a0 + 14] :=
      Env.Frame.trans (Env.Frame.mono F47 (by simp [pgTmpN]) (by simp [pgTmpS]) (by simp))
        (Env.Frame.mono F8 (by simp [pgTmpN]) (by simp [pgTmpS]) (by simp))
    exact frameD_trans (Env.Frame.mono F04 (by simp [pgTmpN]) (by simp [pgTmpS]) (by simp)) (frameD_of_frame F48)


theorem runs_pgStepNS {L : Layout} {w : World d} {dv one n0 s0 a0 muv Av : ℕ} {ρ : ℝ} {P X S : PgSp d}
    (σ : Env d) (hn0 : n0 + 20 ≤ L.NN) (hs0 : s0 + 64 ≤ L.NS) (ha0 : a0 + 32 ≤ L.NA) (hdv : dv < L.NN)
    (hone : one < L.NN) (hdvb : dv < n0 ∨ n0 + 20 ≤ dv) (honeb : one < n0 ∨ n0 + 20 ≤ one) (hd : σ.nat dv = d)
    (h1 : σ.nat one = 1) (hmuv : muv < L.NA) (hAv : Av < L.NA) (hmub : muv < a0 ∨ a0 + 32 ≤ muv)
    (hAb : Av < a0 ∨ a0 + 32 ≤ Av) (hd1 : 1 ≤ d) (hρ1 : 1 ≤ ρ) (hV : PgStageVars σ n0 s0 ρ)
    (hP : PgAt σ muv Av P) (hX : PgAt σ a0 (a0 + 1) X) (hXD : X ∈ pgDom d ρ) (hS : PgAt σ (a0 + 2) (a0 + 3) S) :
    Runs L w (pgStepNS L dv one n0 s0 a0 muv Av) σ (kStepNS d (pgJb d ρ) (nsK d ρ) (Nat.clog 2 (3 * nsK d ρ + 3)) (nsCount (nsK d ρ)))
      (fun σ' => PgAt σ' a0 (a0 + 1) (pgProjR clampNSRoutine d ρ (X - pgStepSize d ρ • pgV (pgKi w.K (σ.sc (s0 + 42)) P) ρ X
            (WithLp.toLp 2 fun c => w.gs (σ.draws + c)))) ∧
        PgAt σ' (a0 + 2) (a0 + 3) (S + X) ∧ σ'.draws = σ.draws + d ∧
        Env.Frame σ { σ' with draws := σ.draws } (pgTmpN n0) (pgTmpS s0 ++ [s0 + 31, s0 + 34, s0 + 35, s0 + 36])
          [a0, a0 + 1, a0 + 2, a0 + 3, a0 + 4, a0 + 5, a0 + 6, a0 + 7, a0 + 8, a0 + 9, a0 + 10, a0 + 11, a0 + 12,
            a0 + 13, a0 + 14]) := by
  obtain ⟨hdd, hjb, hNs, -, hρ, htmin, htmax, hkr, -, hnegs, hkd, hdR⟩ := hV
  obtain ⟨hPm, hPA⟩ := hP
  obtain ⟨hXm, hXT⟩ := hX
  obtain ⟨hSm, hST⟩ := hS
  have hstep := runs_pgStepMNS (w := w) σ hn0 hs0 ha0 hdv hone hdvb honeb hd h1 hmuv hAv hmub hAb hdd
    (by linarith) hρ htmin htmax hdR hNs
  rw [hjb] at hstep
  refine runs_mono hstep le_rfl ?_
  intro σ' hσ'
  dsimp only at hσ'
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := hσ'
  set gv : Fin d → ℝ := fun c => w.gs (σ.draws + c) with hgv
  set K' := pgKi w.K (σ.sc (s0 + 42)) P with hK'
  have hB : (gjRun (pgMat X) d).2 = (pgMat X)⁻¹ := gjRun_inv _ (pgMat_posDef hd1 hρ1 hXD)
  have hF : piTilde (pgBodySet w.K (σ.vec muv) (σ.mat Av) (σ.sc (s0 + 42))) (σ.sc (s0 + 19)) (pgJb d ρ)
      (WithLp.toLp 2 (σ.mat (a0 + 1) *ᵥ gv + σ.vec a0)) = pgFt K' ρ X (WithLp.toLp 2 gv) := by
    rw [pgFt_eq, hK', pgKi_eq, hPm, hPA, hXm, hXT, hρ]
  rw [hF, hXT, hB, hXm, hnegs, hkr] at e1
  rw [hF, hXT, hB, hnegs, hkd] at e2
  refine ⟨?_, ?_, e5, e6⟩
  · unfold pgProjR
    refine ⟨?_, ?_⟩
    · rw [pgMu_pgPack, pgMove_mu]
      rw [show σ'.vec a0 = WithLp.ofLp (WithLp.toLp 2 (σ'.vec a0)) from rfl, e1]
    · rw [pgMat_pgPack, pgMove_mat, e2]
  · refine ⟨?_, ?_⟩
    · rw [e3, hSm, hXm, pgMu_add]; all_goals rfl
    · rw [e4, hST, hXT, pgMat_add]

/-! ## The descent -/

theorem pgIterN_mem {K' : Set (EuclideanSpace ℝ (Fin d))} {ρ : ℝ} (hd1 : 1 ≤ d) (hρ1 : 1 ≤ ρ)
    (a : ℕ → EuclideanSpace ℝ (Fin d)) (t : ℕ) :
    sgdIter (pgProjR clampNSRoutine d ρ) (pgV K' ρ) (pgStepSize d ρ) (pgX1 d ρ) a t ∈ pgDom d ρ := by
  cases t with
  | zero => exact pgX1_mem d ρ hd1 hρ1
  | succ t => simp only [sgdIter]; exact pgProjR_mem clampNSRoutine hd1 hρ1 _

theorem runs_pgDescNS {L : Layout} {w : World d} {dv one n0 s0 a0 muv Av : ℕ} {ρ : ℝ} {P : PgSp d}
    (σ : Env d) (hn0 : n0 + 20 ≤ L.NN) (hs0 : s0 + 64 ≤ L.NS) (ha0 : a0 + 32 ≤ L.NA) (hdv : dv < L.NN)
    (hone : one < L.NN) (hdvb : dv < n0 ∨ n0 + 20 ≤ dv) (honeb : one < n0 ∨ n0 + 20 ≤ one) (hd : σ.nat dv = d)
    (h1 : σ.nat one = 1) (hmuv : muv < L.NA) (hAv : Av < L.NA) (hmub : muv < a0 ∨ a0 + 32 ≤ muv)
    (hAb : Av < a0 ∨ a0 + 32 ≤ Av) (hd1 : 1 ≤ d) (hρ1 : 1 ≤ ρ) (hV : PgStageVars σ n0 s0 ρ)
    (hP : PgAt σ muv Av P) :
    Runs L w (pgDescNS L dv one n0 s0 a0 muv Av) σ (kDescNS d (pgJb d ρ) (pgNs d ρ) (nsK d ρ) (Nat.clog 2 (3 * nsK d ρ + 3)) (nsCount (nsK d ρ)))
      (fun σ' => PgAt σ' (a0 + 2) (a0 + 3) (pgDescentN clampNSRoutine (pgKi w.K (σ.sc (s0 + 42)) P) ρ
            (fun k => WithLp.toLp 2 fun c => w.gs (σ.draws + k * d + c))) ∧
        σ'.draws = σ.draws + pgNs d ρ * d ∧
        Env.Frame σ { σ' with draws := σ.draws } (pgTmpN n0 ++ [n0 + 13])
          (pgTmpS s0 ++ [s0 + 31, s0 + 33, s0 + 34, s0 + 35, s0 + 36, s0 + 45])
          [a0, a0 + 1, a0 + 2, a0 + 3, a0 + 4, a0 + 5, a0 + 6, a0 + 7, a0 + 8, a0 + 9, a0 + 10, a0 + 11, a0 + 12,
            a0 + 13, a0 + 14]) := by
  have hV0 := hV
  obtain ⟨hdd, -, hNs, -, -, htmin, -, -, -, -, -, -⟩ := hV0
  set K' := pgKi w.K (σ.sc (s0 + 42)) P with hK'
  set a : ℕ → EuclideanSpace ℝ (Fin d) := fun k => WithLp.toLp 2 fun c => w.gs (σ.draws + k * d + c) with ha
  set it : ℕ → PgSp d := sgdIter (pgProjR clampNSRoutine d ρ) (pgV K' ρ) (pgStepSize d ρ) (pgX1 d ρ) a with hit
  have hsub : ∀ {ns ss as : List ℕ} {σ' : Env d}, Env.Frame σ { σ' with draws := σ.draws } ns ss as →
      (∀ i ∈ ns, i ∈ pgTmpN n0 ++ [n0 + 13]) →
      (∀ x ∈ ss, x ∈ pgTmpS s0 ++ [s0 + 31, s0 + 33, s0 + 34, s0 + 35, s0 + 36, s0 + 45]) →
      (∀ b ∈ as, b ∈ [a0, a0 + 1, a0 + 2, a0 + 3, a0 + 4, a0 + 5, a0 + 6, a0 + 7, a0 + 8, a0 + 9, a0 + 10, a0 + 11,
        a0 + 12, a0 + 13, a0 + 14]) →
      Env.Frame σ { σ' with draws := σ.draws } (pgTmpN n0 ++ [n0 + 13])
        (pgTmpS s0 ++ [s0 + 31, s0 + 33, s0 + 34, s0 + 35, s0 + 36, s0 + 45])
        [a0, a0 + 1, a0 + 2, a0 + 3, a0 + 4, a0 + 5, a0 + 6, a0 + 7, a0 + 8, a0 + 9, a0 + 10, a0 + 11, a0 + 12,
          a0 + 13, a0 + 14] := fun h hn hs ha => Env.Frame.mono h hn hs ha
  -- the invariant of the loop
  let J : ℕ → Env d → Prop := fun t σ' => PgStageVars σ' n0 s0 ρ ∧ PgAt σ' muv Av P ∧
    σ'.sc (s0 + 42) = σ.sc (s0 + 42) ∧ σ'.nat dv = d ∧ PgAt σ' a0 (a0 + 1) (it t) ∧
    PgAt σ' (a0 + 2) (a0 + 3) (∑ t' ∈ Finset.range t, it t') ∧ σ'.draws = σ.draws + t * d ∧
    Env.Frame σ { σ' with draws := σ.draws } (pgTmpN n0 ++ [n0 + 13])
      (pgTmpS s0 ++ [s0 + 31, s0 + 33, s0 + 34, s0 + 35, s0 + 36, s0 + 45])
      [a0, a0 + 1, a0 + 2, a0 + 3, a0 + 4, a0 + 5, a0 + 6, a0 + 7, a0 + 8, a0 + 9, a0 + 10, a0 + 11, a0 + 12,
        a0 + 13, a0 + 14]
  unfold pgDescNS kDescNS
  -- the start: `x := (0, t_min I)`, the sums `:= 0`
  refine runs_seq_eq (runs_sconst (by omega) 0) ?_
  set σ1 := σ.setSc s0 ((0 : ℚ) : ℝ) with hσ1
  have h1z : σ1.sc s0 = 0 := by simp [σ1]
  have hF1 : Env.Frame σ σ1 [] [s0] [] := Env.Frame.setSc (Env.Frame.refl σ [] [s0] []) (by simp) _
  refine runs_seq (runs_vfill σ1 hdv hone (by omega) (by omega) (by omega) (by omega) (by omega)
    (by simp [σ1, hd]) (by simp [σ1, h1])) fun σ2 h2 => ?_
  obtain ⟨hv2, hF2, -⟩ := h2
  refine runs_seq (runs_mfill σ2 (by omega) hone (by omega) (by omega) (by omega) (by omega) (by omega)
    (by rw [hF2.1 _ (by simp <;> omega)]; simp [σ1, hdd]) (by rw [hF2.1 _ (by simp <;> omega)]; simp [σ1, h1]))
    fun σ3 h3 => ?_
  obtain ⟨hm3, hF3, -⟩ := h3
  refine runs_seq (runs_mdiag σ3 hdv hone (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by rw [hF3.1 _ (by simp <;> omega), hF2.1 _ (by simp <;> omega)]; simp [σ1, hd])
    (by rw [hF3.1 _ (by simp <;> omega), hF2.1 _ (by simp <;> omega)]; simp [σ1, h1])) fun σ4 h4 => ?_
  obtain ⟨hm4, hF4, -⟩ := h4
  have hF14 : Env.Frame σ σ4 [n0, n0 + 2] [s0] [a0, a0 + 1] :=
    Env.Frame.trans (Env.Frame.mono hF1 (by simp) (by simp) (by simp))
      (Env.Frame.trans (Env.Frame.mono hF2 (by simp) (by simp) (by simp))
        (Env.Frame.trans (Env.Frame.mono hF3 (by simp) (by simp) (by simp))
          (Env.Frame.mono hF4 (by simp) (by simp) (by simp))))
  refine runs_seq (runs_vfill σ4 hdv hone (by omega) (by omega) (by omega) (by omega) (by omega)
    (by rw [hF14.1 _ (by simp <;> omega)]; exact hd) (by rw [hF14.1 _ (by simp <;> omega)]; exact h1)) fun σ5 h5 => ?_
  obtain ⟨hv5, hF5, -⟩ := h5
  refine runs_seq (runs_mfill σ5 (by omega) hone (by omega) (by omega) (by omega) (by omega) (by omega)
    (by rw [hF5.1 _ (by simp <;> omega), hF14.1 _ (by simp <;> omega)]; exact hdd)
    (by rw [hF5.1 _ (by simp <;> omega), hF14.1 _ (by simp <;> omega)]; exact h1)) fun σ6 h6 => ?_
  obtain ⟨hm6, hF6, -⟩ := h6
  have hF16 : Env.Frame σ σ6 [n0, n0 + 2] [s0] [a0, a0 + 1, a0 + 2, a0 + 3] :=
    Env.Frame.trans (Env.Frame.mono hF14 (by simp) (by simp) (by simp))
      (Env.Frame.trans (Env.Frame.mono hF5 (by simp) (by simp) (by simp))
        (Env.Frame.mono hF6 (by simp) (by simp) (by simp)))
  have hz4 : σ4.sc s0 = 0 := by rw [hF4.2.1 _ (by simp), hF3.2.1 _ (by simp), hF2.2.1 _ (by simp), h1z]
  have hJ0 : J 0 (σ6.setNat (n0 + 13) 0) := by
    have hF : Env.Frame σ (σ6.setNat (n0 + 13) 0) [n0, n0 + 2, n0 + 13] [s0] [a0, a0 + 1, a0 + 2, a0 + 3] :=
      Env.Frame.setNat (Env.Frame.mono hF16 (by simp) (by simp) (by simp)) (by simp) 0
    refine ⟨hV.of_frame hF (by simp <;> omega) (by simp <;> omega), hP.of_frame hF (by simp <;> omega) (by simp <;> omega),
      hF.2.1 _ (by simp <;> omega), (hF.1 _ (by simp <;> omega)).trans hd, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩
    · show σ6.vec a0 = _
      rw [Env.vec_of_arr (hF6.2.2.1 a0 (by simp <;> omega)), Env.vec_of_arr (hF5.2.2.1 a0 (by simp <;> omega)),
        Env.vec_of_arr (hF4.2.2.1 a0 (by simp <;> omega)), Env.vec_of_arr (hF3.2.2.1 a0 (by simp <;> omega)), hv2, h1z]
      simp [it, sgdIter, pgX1, pgMu_pgPack]
    · show σ6.mat (a0 + 1) = _
      have hz2 : σ2.sc s0 = 0 := by rw [hF2.2.1 s0 (by simp), h1z]
      have e21 : σ3.sc (s0 + 21) = pgTmin d ρ := by
        rw [hF3.2.1 (s0 + 21) (by simp), hF2.2.1 (s0 + 21) (by simp), hσ1, Env.setSc_sc,
          ite_cond_eq_false _ _ (eq_false (show s0 + 21 ≠ s0 by omega)), htmin]
      rw [Env.mat_of_arr (hF6.2.2.1 (a0 + 1) (by simp <;> omega)),
        Env.mat_of_arr (hF5.2.2.1 (a0 + 1) (by simp <;> omega)), hm4, hm3, e21, hz2]
      simp only [it, sgdIter, pgX1, pgMat_pgPack]
      ext i j
      simp [Matrix.one_apply]
    · show σ6.vec (a0 + 2) = _
      rw [Env.vec_of_arr (hF6.2.2.1 _ (by simp <;> omega)), hv5, hz4]
      simp [pgMu_zero]
    · show σ6.mat (a0 + 3) = _
      rw [hm6, hF5.2.1 _ (by simp), hz4]
      ext i j
      simp [pgMat_zero]
    · show σ6.draws = σ.draws + 0 * d
      rw [hF16.2.2.2.1]; simp
    · exact frameD_of_frame (Env.Frame.mono hF (by simp [pgTmpN]) (by simp [pgTmpS]) (by simp))
  -- the loop
  have hnat6 : ∀ k, k ∉ [n0, n0 + 2] → σ6.nat k = σ.nat k := fun k hk => hF16.1 k hk
  refine runs_seq (runs_forN (by omega) (by omega) hone (by omega) (by omega) (pgNs d ρ) (kStepNS d (pgJb d ρ) (nsK d ρ) (Nat.clog 2 (3 * nsK d ρ + 3)) (nsCount (nsK d ρ))) J σ6
    (by rw [hnat6 _ (by simp <;> omega)]; exact hNs) (by rw [hnat6 _ (by simp <;> omega)]; exact h1) hJ0
    ?_) fun σ7 h7 => ?_
  · intro t ht σ' hJ hi hn h1'
    obtain ⟨hV', hP', hR', hd', hX', hS', hdr', hF'⟩ := hJ
    have hstep := runs_pgStepNS (w := w) (X := it t) (S := ∑ t' ∈ Finset.range t, it t') σ' hn0 hs0 ha0 hdv hone
      hdvb honeb hd' h1' hmuv hAv hmub hAb hd1 hρ1 hV' hP' hX' (pgIterN_mem hd1 hρ1 a t) hS'
    refine runs_mono hstep le_rfl fun σ'' ⟨e1, e2, e3, e4⟩ => ?_
    have hF'' : Env.Frame σ' { σ'' with draws := σ'.draws } (pgTmpN n0 ++ [n0 + 13])
        (pgTmpS s0 ++ [s0 + 31, s0 + 33, s0 + 34, s0 + 35, s0 + 36, s0 + 45])
        [a0, a0 + 1, a0 + 2, a0 + 3, a0 + 4, a0 + 5, a0 + 6, a0 + 7, a0 + 8, a0 + 9, a0 + 10, a0 + 11, a0 + 12,
          a0 + 13, a0 + 14] := Env.Frame.mono e4 (fun i hi => List.mem_append_left _ hi)
          (fun x hx => List.mem_append.2 ((List.mem_append.1 hx).imp id (fun h => by simp at h ⊢; omega)))
          (by simp)
    have hσ''n : ∀ k, k ∉ pgTmpN n0 → σ''.nat k = σ'.nat k := fun k hk => e4.1 k hk
    refine ⟨by rw [hσ''n _ (by simp [pgTmpN] <;> omega)]; exact hi, by rw [hσ''n _ (by simp [pgTmpN] <;> omega)]; exact hn,
      by rw [hσ''n _ (by simp [pgTmpN] <;> omega)]; exact h1', ?_⟩
    have hF3' : Env.Frame σ' { (σ''.setNat (n0 + 13) (t + 1)) with draws := σ'.draws }
        (pgTmpN n0 ++ [n0 + 13]) (pgTmpS s0 ++ [s0 + 31, s0 + 33, s0 + 34, s0 + 35, s0 + 36, s0 + 45])
        [a0, a0 + 1, a0 + 2, a0 + 3, a0 + 4, a0 + 5, a0 + 6, a0 + 7, a0 + 8, a0 + 9, a0 + 10, a0 + 11, a0 + 12,
          a0 + 13, a0 + 14] := Env.Frame.setNat hF'' (by simp) _
    have hga : (WithLp.toLp 2 fun c : Fin d => w.gs (σ'.draws + c) : EuclideanSpace ℝ (Fin d)) = a t := by
      simp only [a, hdr']
    rw [hga] at e1
    have hV3 := hV'.of_frame hF3' (by simp [pgTmpN] <;> omega) (by simp [pgTmpS] <;> omega)
    have hP3 := hP'.of_frame hF3' (by simp <;> omega) (by simp <;> omega)
    refine ⟨hV3, hP3, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show σ''.sc (s0 + 42) = _
      rw [hF''.2.1 _ (by simp [pgTmpS] <;> omega)]; exact hR'
    · exact (hF3'.1 dv (by simp [pgTmpN] <;> omega)).trans hd'
    · rw [hR'] at e1
      exact e1
    · show PgAt σ'' (a0 + 2) (a0 + 3) _
      rw [Finset.sum_range_succ]; exact e2
    · show σ''.draws = σ.draws + (t + 1) * d
      rw [e3, hdr']; ring
    · exact frameD_trans hF' hF3'
  -- the average
  obtain ⟨hJ7, -, -, h17⟩ := h7
  obtain ⟨hV7, -, -, hd7, -, hS7, hdr7, hF7⟩ := hJ7
  refine runs_seq_eq (runs_sconst (by omega) 1) ?_
  refine runs_seq_eq (runs_ncast (by omega) (by omega)) ?_
  refine runs_seq_eq (runs_sop2 (by omega) (by omega) (by omega) .div) ?_
  refine runs_seq_eq (runs_sconst (by omega) 0) ?_
  set σ8 := ((((σ7.setSc (s0 + 2) ((1 : ℚ) : ℝ)).setSc (s0 + 45) ((σ7.setSc (s0 + 2) ((1 : ℚ) : ℝ)).nat (n0 + 11))).setSc
    (s0 + 33) (Op2.div.eval (((σ7.setSc (s0 + 2) ((1 : ℚ) : ℝ)).setSc (s0 + 45)
      ((σ7.setSc (s0 + 2) ((1 : ℚ) : ℝ)).nat (n0 + 11))).sc (s0 + 2))
      (((σ7.setSc (s0 + 2) ((1 : ℚ) : ℝ)).setSc (s0 + 45) ((σ7.setSc (s0 + 2) ((1 : ℚ) : ℝ)).nat (n0 + 11))).sc
        (s0 + 45)))).setSc s0 ((0 : ℚ) : ℝ)) with hσ8
  have hF8 : Env.Frame σ7 σ8 [] [s0, s0 + 2, s0 + 33, s0 + 45] [] :=
    Env.Frame.setSc (Env.Frame.setSc (Env.Frame.setSc (Env.Frame.setSc (Env.Frame.refl σ7 _ _ _) (by simp) _)
      (by simp) _) (by simp) _) (by simp) _
  have hinv : σ8.sc (s0 + 33) = ((pgNs d ρ : ℕ) : ℝ)⁻¹ := by
    have hN7 : σ7.nat (n0 + 11) = pgNs d ρ := hV7.2.2.1
    simp [σ8, Op2.eval, hN7, (show s0 + 33 ≠ s0 by omega), (show s0 + 45 ≠ s0 + 2 by omega)]
  refine runs_seq (runs_vscale σ8 hdv hone (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by rw [hF8.1 _ (by simp)]; exact hd7) (by rw [hF8.1 _ (by simp)]; exact h17)) fun σ9 h9 => ?_
  obtain ⟨hv9, hF9, -⟩ := h9
  refine runs_mono (runs_mlin σ9 (by omega) hone (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by rw [hF9.1 _ (by simp <;> omega), hF8.1 _ (by simp)]; exact hV7.1)
    (by rw [hF9.1 _ (by simp <;> omega), hF8.1 _ (by simp)]; exact h17)) le_rfl ?_
  rintro σ' ⟨hm', hF', -⟩
  have hF89 : Env.Frame σ7 σ' [n0] [s0, s0 + 2, s0 + 8, s0 + 9, s0 + 33, s0 + 45] [a0 + 2, a0 + 3] :=
    Env.Frame.trans (Env.Frame.mono hF8 (by simp) (by simp) (by simp))
      (Env.Frame.trans (Env.Frame.mono hF9 (by simp) (by simp) (by simp))
        (Env.Frame.mono hF' (by simp) (by simp) (by simp)))
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [Env.vec_of_arr (hF'.2.2.1 _ (by simp <;> omega)), hv9, hinv,
      Env.vec_of_arr (hF8.2.2.1 _ (by simp)), hS7.1]
    simp only [pgDescentN, sgdAvg, pgMu_smul]
    rfl
  · rw [hm', hF9.2.1 _ (by simp <;> omega), hF9.2.1 _ (by simp <;> omega), Env.mat_of_arr (hF9.2.2.1 _ (by simp <;> omega)),
      hinv, Env.mat_of_arr (hF8.2.2.1 _ (by simp)), hS7.2]
    have hz8 : σ8.sc s0 = 0 := by simp [σ8]
    rw [hz8, zero_smul, add_zero]
    simp only [pgDescentN, sgdAvg, pgMat_smul]
    rfl
  · rw [hF'.2.2.2.1, hF9.2.2.2.1]
    show σ7.draws = _
    rw [hdr7]
  · exact frameD_trans hF7 (frameD_of_frame (Env.Frame.mono hF89 (by simp [pgTmpN]) (by simp [pgTmpS]) (by simp)))

/-! ## The verdict -/

open Classical in
/-- The value the code gives to a basic verdict is its indicator: the pivot test is the third clause (D2e,
`pgVerdictS_iff_pivots`). -/
theorem pgVerdictS_code (K' : Set (EuclideanSpace ℝ (Fin d))) (ρ : ℝ) (X : PgSp d)
    (ws : ℕ → EuclideanSpace ℝ (Fin d)) :
    (if ∀ k : Fin d, 0 < (gjRun (((pgNT d ρ : ℝ))⁻¹ • ∑ i ∈ Finset.range (pgNT d ρ), pgFt K' ρ X (ws i) • pgGG (ws i) -
          ((-5 / 8 : ℝ) * -(pgKappa / d)) • (1 : Matrix (Fin d) (Fin d) ℝ)) k).1 k k
      then (if ((pgNT d ρ : ℝ))⁻¹ * ∑ i ∈ Finset.range (pgNT d ρ), pgFt K' ρ X (ws i) ≤ 43 / 320 ∧
          Real.sqrt ((((pgNT d ρ : ℝ))⁻¹ • ∑ i ∈ Finset.range (pgNT d ρ), pgFt K' ρ X (ws i) • (fun c => ws i c)) ⬝ᵥ
            (((pgNT d ρ : ℝ))⁻¹ • ∑ i ∈ Finset.range (pgNT d ρ), pgFt K' ρ X (ws i) • (fun c => ws i c))) ≤
            3 / 4 * pgTaub d ρ then 1 else 0)
      else (0 : ℝ)) =
      if pgVerdictS K' ρ X ws then 1 else 0 := by
  set n := pgNT d ρ
  have hc : ((-5 / 8 : ℝ) * -(pgKappa / d)) = 5 / 8 * (pgKappa / d) := by ring
  have hA : ∀ x : ℝ, x ≤ 43 / 320 ↔ x ≤ 1.075 * pgKappa := fun x => by norm_num [pgKappa]
  have hB : Real.sqrt ((((n : ℝ))⁻¹ • ∑ i ∈ Finset.range n, pgFt K' ρ X (ws i) • (fun c => ws i c)) ⬝ᵥ
      (((n : ℝ))⁻¹ • ∑ i ∈ Finset.range n, pgFt K' ρ X (ws i) • (fun c => ws i c))) =
      ‖((n : ℝ))⁻¹ • ∑ i ∈ Finset.range n, pgFt K' ρ X (ws i) • ws i‖ := by
    rw [← sqrt_dot_ofLp]
    simp only [WithLp.ofLp_smul, WithLp.ofLp_sum]
  have hiff := pgVerdictS_iff_pivots K' ρ X ws
  simp only [pgKh, pgBh, pgQh] at hiff
  rw [hc, hB]
  by_cases h3 : ∀ k : Fin d, 0 < (gjRun (((n : ℝ))⁻¹ • ∑ i ∈ Finset.range n, pgFt K' ρ X (ws i) • pgGG (ws i) -
      (5 / 8 * (pgKappa / d)) • (1 : Matrix (Fin d) (Fin d) ℝ)) k).1 k k
  · rw [if_pos h3]
    by_cases h12 : ((n : ℝ))⁻¹ * ∑ i ∈ Finset.range n, pgFt K' ρ X (ws i) ≤ 43 / 320 ∧
        ‖((n : ℝ))⁻¹ • ∑ i ∈ Finset.range n, pgFt K' ρ X (ws i) • ws i‖ ≤ 3 / 4 * pgTaub d ρ
    · rw [if_pos h12, if_pos (hiff.2 ⟨(hA _).1 h12.1, h12.2, h3⟩)]
    · rw [if_neg h12, if_neg (fun hv => h12 ⟨(hA _).2 (hiff.1 hv).1, (hiff.1 hv).2.1⟩)]
  · rw [if_neg h3, if_neg (fun hv => h3 (hiff.1 hv).2.2)]

open Classical in
/-- One basic verdict at `x̄ = X`: the count `s0 + 40` grows by the indicator of `pgVerdictS` on the next `n_T` vectors. -/
theorem runs_pgVerdNS {L : Layout} {w : World d} {dv one n0 s0 a0 muv Av : ℕ} {ρ : ℝ} {P X : PgSp d}
    (σ : Env d) (hn0 : n0 + 20 ≤ L.NN) (hs0 : s0 + 64 ≤ L.NS) (ha0 : a0 + 32 ≤ L.NA) (hdv : dv < L.NN)
    (hone : one < L.NN) (hdvb : dv < n0 ∨ n0 + 20 ≤ dv) (honeb : one < n0 ∨ n0 + 20 ≤ one) (hd : σ.nat dv = d)
    (h1 : σ.nat one = 1) (hmuv : muv < L.NA) (hAv : Av < L.NA) (hmub : muv < a0 ∨ a0 + 32 ≤ muv)
    (hAb : Av < a0 ∨ a0 + 32 ≤ Av) (hV : PgStageVars σ n0 s0 ρ) (hP : PgAt σ muv Av P)
    (hX : PgAt σ (a0 + 2) (a0 + 3) X) :
    Runs L w (pgVerdNS L dv one n0 s0 a0 muv Av) σ (kVerdNS d (pgJb d ρ) (pgNT d ρ))
      (fun σ' => σ'.sc (s0 + 40) = σ.sc (s0 + 40) + (if pgVerdictS (pgKi w.K (σ.sc (s0 + 42)) P) ρ X
            (fun k => WithLp.toLp 2 fun c => w.gs (σ.draws + k * d + c)) then 1 else 0) ∧
        σ'.draws = σ.draws + pgNT d ρ * d ∧
        Env.Frame σ { σ' with draws := σ.draws } (pgTmpN n0 ++ [n0 + 13])
          (pgTmpS s0 ++ [s0 + 36, s0 + 37, s0 + 38, s0 + 39, s0 + 40, s0 + 44, s0 + 45, s0 + 46, s0 + 47, s0 + 51])
          [a0 + 4, a0 + 5, a0 + 6, a0 + 7, a0 + 11, a0 + 15, a0 + 16, a0 + 17, a0 + 18]) := by
  have hV0 := hV
  obtain ⟨hdd, -, -, hNT, -, -, -, -, htaub, -, hkd, -⟩ := hV0
  set K' := pgKi w.K (σ.sc (s0 + 42)) P with hK'
  set ws : ℕ → EuclideanSpace ℝ (Fin d) := fun k => WithLp.toLp 2 fun c => w.gs (σ.draws + k * d + c) with hws
  set F : ℕ → ℝ := fun i => pgFt K' ρ X (ws i) with hFdef
  let J : ℕ → Env d → Prop := fun t σ' => PgStageVars σ' n0 s0 ρ ∧ PgAt σ' muv Av P ∧
    PgAt σ' (a0 + 2) (a0 + 3) X ∧ σ'.sc (s0 + 42) = σ.sc (s0 + 42) ∧ σ'.nat dv = d ∧
    σ'.sc (s0 + 40) = σ.sc (s0 + 40) ∧ σ'.sc (s0 + 37) = ∑ i ∈ Finset.range t, F i ∧
    σ'.vec (a0 + 15) = ∑ i ∈ Finset.range t, F i • (fun c => ws i c) ∧
    σ'.mat (a0 + 16) = ∑ i ∈ Finset.range t, F i • pgGG (ws i) ∧ σ'.draws = σ.draws + t * d ∧
    Env.Frame σ { σ' with draws := σ.draws } (pgTmpN n0 ++ [n0 + 13])
      (pgTmpS s0 ++ [s0 + 36, s0 + 37, s0 + 38, s0 + 39, s0 + 40, s0 + 44, s0 + 45, s0 + 46, s0 + 47, s0 + 51])
      [a0 + 4, a0 + 5, a0 + 6, a0 + 7, a0 + 11, a0 + 15, a0 + 16, a0 + 17, a0 + 18]
  unfold pgVerdNS kVerdNS
  -- the accumulators `:= 0`
  refine runs_seq_eq (runs_sconst (by omega) 0) ?_
  refine runs_seq_eq (runs_sconst (by omega) 0) ?_
  set σ1 := (σ.setSc s0 ((0 : ℚ) : ℝ)).setSc (s0 + 37) ((0 : ℚ) : ℝ) with hσ1
  have h1z : σ1.sc s0 = 0 := by simp [σ1]
  have h37 : σ1.sc (s0 + 37) = 0 := by simp [σ1]
  have hF1 : Env.Frame σ σ1 [] [s0, s0 + 37] [] :=
    Env.Frame.setSc (Env.Frame.setSc (Env.Frame.refl σ [] [s0, s0 + 37] []) (by simp) _) (by simp) _
  refine runs_seq (runs_vfill σ1 hdv hone (by omega) (by omega) (by omega) (by omega) (by omega)
    (by rw [hF1.1 _ (by simp)]; exact hd) (by rw [hF1.1 _ (by simp)]; exact h1)) fun σ2 h2 => ?_
  obtain ⟨hv2, hF2, -⟩ := h2
  refine runs_seq (runs_mfill σ2 (by omega) hone (by omega) (by omega) (by omega) (by omega) (by omega)
    (by rw [hF2.1 _ (by simp <;> omega), hF1.1 _ (by simp)]; exact hdd)
    (by rw [hF2.1 _ (by simp <;> omega), hF1.1 _ (by simp)]; exact h1)) fun σ3 h3 => ?_
  obtain ⟨hm3, hF3, -⟩ := h3
  have hF13 : Env.Frame σ σ3 [n0] [s0, s0 + 37] [a0 + 15, a0 + 16] :=
    Env.Frame.trans (Env.Frame.mono hF1 (by simp) (by simp) (by simp))
      (Env.Frame.trans (Env.Frame.mono hF2 (by simp) (by simp) (by simp))
        (Env.Frame.mono hF3 (by simp) (by simp) (by simp)))
  have hJ0 : J 0 (σ3.setNat (n0 + 13) 0) := by
    have hF : Env.Frame σ (σ3.setNat (n0 + 13) 0) [n0, n0 + 13] [s0, s0 + 37] [a0 + 15, a0 + 16] :=
      Env.Frame.setNat (Env.Frame.mono hF13 (by simp) (by simp) (by simp)) (by simp) 0
    refine ⟨hV.of_frame hF (by simp <;> omega) (by simp <;> omega),
      hP.of_frame hF (by simp <;> omega) (by simp <;> omega), hX.of_frame hF (by simp) (by simp),
      hF.2.1 _ (by simp), (hF.1 _ (by simp <;> omega)).trans hd, hF.2.1 _ (by simp), ?_, ?_, ?_, ?_, ?_⟩
    · show σ3.sc (s0 + 37) = _
      rw [hF3.2.1 _ (by simp), hF2.2.1 _ (by simp), h37, Finset.sum_range_zero]
    · show σ3.vec (a0 + 15) = _
      rw [Env.vec_of_arr (hF3.2.2.1 _ (by simp)), hv2, h1z, Finset.sum_range_zero]
      rfl
    · show σ3.mat (a0 + 16) = _
      rw [hm3, hF2.2.1 _ (by simp), h1z, Finset.sum_range_zero]
      ext i j
      simp
    · show σ3.draws = σ.draws + 0 * d
      rw [hF13.2.2.2.1]; simp
    · exact frameD_of_frame (Env.Frame.mono hF (by simp [pgTmpN]) (by simp [pgTmpS]) (by simp))
  -- the samples
  have hnat3 : ∀ k, k ∉ [n0] → σ3.nat k = σ.nat k := fun k hk => hF13.1 k hk
  refine runs_seq (runs_forN (by omega) (by omega) hone (by omega) (by omega) (pgNT d ρ) (kSample d (pgJb d ρ)) J σ3
    (by rw [hnat3 _ (by simp)]; exact hNT) (by rw [hnat3 _ (by simp <;> omega)]; exact h1) hJ0
    ?_) fun σ7 h7 => ?_
  · intro t ht σ' hJ hi hn h1'
    obtain ⟨hV', hP', hX', hR', hd', h40', hk', hb', hQ', hdr', hF'⟩ := hJ
    have hs := runs_pgSample pgLeaves (w := w) σ' hn0 hs0 ha0 hdv hone hdvb honeb hd' h1' hmuv hAv hmub hAb hV' hP' hX'
    refine runs_mono hs le_rfl fun σ'' ⟨e1, e2, e3, e4, e5⟩ => ?_
    have hσ''n : ∀ k, k ∉ pgTmpN n0 → σ''.nat k = σ'.nat k := fun k hk => e5.1 k hk
    refine ⟨by rw [hσ''n _ (by simp [pgTmpN] <;> omega)]; exact hi, by rw [hσ''n _ (by simp [pgTmpN] <;> omega)]; exact hn,
      by rw [hσ''n _ (by simp [pgTmpN] <;> omega)]; exact h1', ?_⟩
    have hF'' : Env.Frame σ' { σ'' with draws := σ'.draws } (pgTmpN n0 ++ [n0 + 13])
        (pgTmpS s0 ++ [s0 + 36, s0 + 37, s0 + 38, s0 + 39, s0 + 40, s0 + 44, s0 + 45, s0 + 46, s0 + 47, s0 + 51])
        [a0 + 4, a0 + 5, a0 + 6, a0 + 7, a0 + 11, a0 + 15, a0 + 16, a0 + 17, a0 + 18] :=
      Env.Frame.mono e5 (fun i hi => List.mem_append_left _ hi)
        (fun x hx => List.mem_append.2 ((List.mem_append.1 hx).imp id (fun h => by simp at h ⊢; omega)))
        (fun b hb => by simp at hb ⊢; omega)
    have hF3' : Env.Frame σ' { (σ''.setNat (n0 + 13) (t + 1)) with draws := σ'.draws }
        (pgTmpN n0 ++ [n0 + 13])
        (pgTmpS s0 ++ [s0 + 36, s0 + 37, s0 + 38, s0 + 39, s0 + 40, s0 + 44, s0 + 45, s0 + 46, s0 + 47, s0 + 51])
        [a0 + 4, a0 + 5, a0 + 6, a0 + 7, a0 + 11, a0 + 15, a0 + 16, a0 + 17, a0 + 18] :=
      Env.Frame.setNat hF'' (by simp) _
    have hga : (WithLp.toLp 2 fun c : Fin d => w.gs (σ'.draws + c) : EuclideanSpace ℝ (Fin d)) = ws t := by
      simp only [ws, hdr']
    have hgf : (fun c : Fin d => w.gs (σ'.draws + c)) = fun c => ws t c := by
      simp only [ws, hdr']
    rw [hga, hR'] at e1 e2 e3
    rw [hgf] at e2
    have hV3 := hV'.of_frame hF3' (by simp [pgTmpN] <;> omega) (by simp [pgTmpS] <;> omega)
    have hP3 := hP'.of_frame hF3' (by simp <;> omega) (by simp <;> omega)
    have hX3 := hX'.of_frame hF3' (by simp) (by simp)
    refine ⟨hV3, hP3, hX3, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show σ''.sc (s0 + 42) = _
      rw [e5.2.1 _ (by simp [pgTmpS] <;> omega)]; exact hR'
    · exact (hF3'.1 dv (by simp [pgTmpN] <;> omega)).trans hd'
    · show σ''.sc (s0 + 40) = _
      rw [e5.2.1 _ (by simp [pgTmpS] <;> omega)]; exact h40'
    · show σ''.sc (s0 + 37) = _
      rw [e1, hk', Finset.sum_range_succ]
    · show σ''.vec (a0 + 15) = _
      rw [e2, hb', Finset.sum_range_succ]
    · show σ''.mat (a0 + 16) = _
      rw [e3, hQ', Finset.sum_range_succ]
    · show σ''.draws = σ.draws + (t + 1) * d
      rw [e4, hdr']; ring
    · exact frameD_trans hF' hF3'
  -- the averages and the three clauses
  obtain ⟨hJ7, -, -, h17⟩ := h7
  obtain ⟨hV7, -, -, -, hd7, h407, hk7, hb7, hQ7, hdr7, hF7⟩ := hJ7
  refine runs_seq (pgLeaves.verdNorm σ7 hn0 hs0 ha0 hdv hone hdvb honeb hd7 h17 hV7.1) fun σ8 h8 => ?_
  obtain ⟨n37, n15, n16, hF8⟩ := h8
  have hd8 : σ8.nat dv = d := by rw [hF8.1 _ (by simp <;> omega)]; exact hd7
  have h18 : σ8.nat one = 1 := by rw [hF8.1 _ (by simp <;> omega)]; exact h17
  refine runs_seq (pgLeaves.verdC12 σ8 hn0 hs0 ha0 hdv hone hdvb honeb hd8 h18) fun σ9 h9 => ?_
  obtain ⟨v9, hF9⟩ := h9
  have hd9 : σ9.nat dv = d := by rw [hF9.1 _ (by simp <;> omega)]; exact hd8
  have h19 : σ9.nat one = 1 := by rw [hF9.1 _ (by simp <;> omega)]; exact h18
  have hdd9 : σ9.nat (n0 + 9) = d * d := by
    rw [hF9.1 _ (by simp), hF8.1 _ (by simp)]; exact hV7.1
  refine runs_seq (runs_pgVerdC3P σ9 hn0 hs0 ha0 hdv hone hdvb honeb hd9 h19 hdd9) fun σ10 h10 => ?_
  obtain ⟨v10, hF10⟩ := h10
  refine runs_mono (runs_sop2 (by omega) (by omega) (by omega) .add) le_rfl ?_
  rintro σ' rfl
  have hn7 : σ7.nat (n0 + 12) = pgNT d ρ := hV7.2.2.2.1
  have hkd9 : σ9.sc (s0 + 32) = -(pgKappa / d) := by
    rw [hF9.2.1 _ (by simp), hF8.2.1 _ (by simp)]; exact hV7.2.2.2.2.2.2.2.2.2.2.1
  have htb8 : σ8.sc (s0 + 28) = pgTaub d ρ := by
    rw [hF8.2.1 _ (by simp)]; exact hV7.2.2.2.2.2.2.2.2.1
  have hm9 : σ9.mat (a0 + 16) = σ8.mat (a0 + 16) := Env.mat_of_arr (hF9.2.2.1 _ (by simp))
  have h409 : σ10.sc (s0 + 40) = σ.sc (s0 + 40) := by
    rw [hF10.2.1 _ (by simp), hF9.2.1 _ (by simp), hF8.2.1 _ (by simp)]; exact h407
  refine ⟨?_, ?_, ?_⟩
  · simp only [Env.setSc_sc, if_true, Op2.eval]
    rw [h409, v10, v9, hkd9, hm9, n16, n37, n15, htb8, hn7, hk7, hb7, hQ7]
    congr 1
    exact pgVerdictS_code K' ρ X ws
  · show σ10.draws = _
    rw [hF10.2.2.2.1, hF9.2.2.2.1, hF8.2.2.2.1, hdr7]
  · have hF810 : Env.Frame σ7 (σ10.setSc (s0 + 40) (Op2.add.eval (σ10.sc (s0 + 40)) (σ10.sc (s0 + 39)))) [n0, n0 + 1, n0 + 2, n0 + 4, n0 + 5, n0 + 6, n0 + 7]
        [s0, s0 + 2, s0 + 8, s0 + 9, s0 + 10, s0 + 12, s0 + 13, s0 + 14, s0 + 36, s0 + 37, s0 + 38, s0 + 39, s0 + 40, s0 + 44, s0 + 45, s0 + 46, s0 + 47,
          s0 + 51] [a0 + 15, a0 + 16, a0 + 17, a0 + 18] :=
      Env.Frame.trans (Env.Frame.mono hF8 (by simp) (by simp) (by simp))
        (Env.Frame.trans (Env.Frame.mono hF9 (by simp) (by simp) (by simp))
          (Env.Frame.trans (Env.Frame.mono hF10 (by simp) (by simp) (by simp))
            (Env.Frame.setSc (Env.Frame.refl σ10 _ _ _) (by simp) _)))
    exact frameD_trans hF7 (frameD_of_frame (Env.Frame.mono hF810 (by simp [pgTmpN]) (by simp [pgTmpS]) (by simp)))

/-! ## The amplified test -/

open Classical in
theorem pgTestS_count (K' : Set (EuclideanSpace ℝ (Fin d))) (ρ δ : ℝ) (X : PgSp d)
    (wsT : ℕ → ℕ → EuclideanSpace ℝ (Fin d)) :
    ((pgMT δ : ℝ) * ((1 : ℚ) / 2 : ℚ) <
        ∑ v ∈ Finset.range (pgMT δ), if pgVerdictS K' ρ X (wsT v) then (1 : ℝ) else 0) ↔ pgTestS K' ρ δ X wsT := by
  rw [pgTestS, Finset.sum_boole]
  push_cast
  constructor <;> intro h <;> linarith

open Classical in
/-- The amplified test at `x̄ = X`: `pass` (`s0 + 49`) is the indicator of `pgTestS` on the next `m_T n_T` vectors. -/
theorem runs_pgTestCNS {L : Layout} {w : World d} {dv one n0 s0 a0 muv Av : ℕ} {ρ δ : ℝ} {P X : PgSp d}
    (σ : Env d) (hn0 : n0 + 20 ≤ L.NN) (hs0 : s0 + 64 ≤ L.NS) (ha0 : a0 + 32 ≤ L.NA) (hdv : dv < L.NN)
    (hone : one < L.NN) (hdvb : dv < n0 ∨ n0 + 20 ≤ dv) (honeb : one < n0 ∨ n0 + 20 ≤ one) (hd : σ.nat dv = d)
    (h1 : σ.nat one = 1) (hmuv : muv < L.NA) (hAv : Av < L.NA) (hmub : muv < a0 ∨ a0 + 32 ≤ muv)
    (hAb : Av < a0 ∨ a0 + 32 ≤ Av) (hV : PgStageVars σ n0 s0 ρ) (hP : PgAt σ muv Av P)
    (hX : PgAt σ (a0 + 2) (a0 + 3) X) (hmT : σ.nat (n0 + 14) = pgMT δ) :
    Runs L w (pgTestCNS L dv one n0 s0 a0 muv Av) σ (kTestNS d (pgJb d ρ) (pgNT d ρ) (pgMT δ))
      (fun σ' => σ'.sc (s0 + 49) = (if pgTestS (pgKi w.K (σ.sc (s0 + 42)) P) ρ δ X
            (fun v k => WithLp.toLp 2 fun c => w.gs (σ.draws + (v * pgNT d ρ + k) * d + c)) then 1 else 0) ∧
        σ'.draws = σ.draws + pgMT δ * (pgNT d ρ * d) ∧
        Env.Frame σ { σ' with draws := σ.draws } (pgTmpN n0 ++ [n0 + 13, n0 + 15])
          (pgTmpS s0 ++ [s0 + 36, s0 + 37, s0 + 38, s0 + 39, s0 + 40, s0 + 44, s0 + 45, s0 + 46, s0 + 47, s0 + 49,
            s0 + 51])
          [a0 + 4, a0 + 5, a0 + 6, a0 + 7, a0 + 11, a0 + 15, a0 + 16, a0 + 17, a0 + 18]) := by
  set K' := pgKi w.K (σ.sc (s0 + 42)) P with hK'
  set wsT : ℕ → ℕ → EuclideanSpace ℝ (Fin d) :=
    fun v k => WithLp.toLp 2 fun c => w.gs (σ.draws + (v * pgNT d ρ + k) * d + c) with hwsT
  set cnt : ℕ → ℝ := fun t => ∑ v ∈ Finset.range t, if pgVerdictS K' ρ X (wsT v) then (1 : ℝ) else 0 with hcnt
  let J : ℕ → Env d → Prop := fun t σ' => PgStageVars σ' n0 s0 ρ ∧ PgAt σ' muv Av P ∧
    PgAt σ' (a0 + 2) (a0 + 3) X ∧ σ'.sc (s0 + 42) = σ.sc (s0 + 42) ∧ σ'.nat dv = d ∧
    σ'.nat (n0 + 14) = pgMT δ ∧ σ'.sc (s0 + 40) = cnt t ∧ σ'.draws = σ.draws + t * (pgNT d ρ * d) ∧
    Env.Frame σ { σ' with draws := σ.draws } (pgTmpN n0 ++ [n0 + 13, n0 + 15])
      (pgTmpS s0 ++ [s0 + 36, s0 + 37, s0 + 38, s0 + 39, s0 + 40, s0 + 44, s0 + 45, s0 + 46, s0 + 47, s0 + 49,
        s0 + 51])
      [a0 + 4, a0 + 5, a0 + 6, a0 + 7, a0 + 11, a0 + 15, a0 + 16, a0 + 17, a0 + 18]
  unfold pgTestCNS kTestNS
  refine runs_seq_eq (runs_sconst (by omega) 0) ?_
  set σ1 := σ.setSc (s0 + 40) ((0 : ℚ) : ℝ) with hσ1
  have hF1 : Env.Frame σ (σ1.setNat (n0 + 15) 0) [n0 + 15] [s0 + 40] [] :=
    Env.Frame.setNat (Env.Frame.setSc (Env.Frame.refl σ [n0 + 15] [s0 + 40] []) (by simp) _) (by simp) 0
  have hJ0 : J 0 (σ1.setNat (n0 + 15) 0) := by
    refine ⟨hV.of_frame hF1 (by simp <;> omega) (by simp <;> omega),
      hP.of_frame hF1 (by simp) (by simp), hX.of_frame hF1 (by simp) (by simp),
      hF1.2.1 _ (by simp), (hF1.1 _ (by simp <;> omega)).trans hd, (hF1.1 _ (by simp)).trans hmT, ?_, ?_, ?_⟩
    · show σ1.sc (s0 + 40) = _
      simp [σ1, cnt]
    · show σ.draws = σ.draws + 0 * (pgNT d ρ * d)
      simp
    · exact frameD_of_frame (Env.Frame.mono hF1 (by simp) (by simp) (by simp))
  have hσ1n : ∀ k, k ≠ n0 + 15 → (σ1.setNat (n0 + 15) 0).nat k = σ.nat k := fun k hk => hF1.1 k (by simpa using hk)
  refine runs_seq (runs_forN (by omega) (by omega) hone (by omega) (by omega) (pgMT δ)
    (kVerdNS d (pgJb d ρ) (pgNT d ρ)) J σ1 (by rw [show σ1.nat (n0 + 14) = σ.nat (n0 + 14) from rfl]; exact hmT)
    (by rw [show σ1.nat one = σ.nat one from rfl]; exact h1) hJ0 ?_) fun σ7 h7 => ?_
  · intro t ht σ' hJ hi hn h1'
    obtain ⟨hV', hP', hX', hR', hd', hm', hc', hdr', hF'⟩ := hJ
    have hs := runs_pgVerdNS (w := w) σ' hn0 hs0 ha0 hdv hone hdvb honeb hd' h1' hmuv hAv hmub hAb hV' hP' hX'
    refine runs_mono hs le_rfl fun σ'' ⟨e1, e2, e3⟩ => ?_
    have hσ''n : ∀ k, k ∉ pgTmpN n0 ++ [n0 + 13] → σ''.nat k = σ'.nat k := fun k hk => e3.1 k hk
    refine ⟨by rw [hσ''n _ (by simp [pgTmpN] <;> omega)]; exact hi, by rw [hσ''n _ (by simp [pgTmpN] <;> omega)]; exact hn,
      by rw [hσ''n _ (by simp [pgTmpN] <;> omega)]; exact h1', ?_⟩
    have hF'' : Env.Frame σ' { σ'' with draws := σ'.draws } (pgTmpN n0 ++ [n0 + 13, n0 + 15])
        (pgTmpS s0 ++ [s0 + 36, s0 + 37, s0 + 38, s0 + 39, s0 + 40, s0 + 44, s0 + 45, s0 + 46, s0 + 47, s0 + 49,
          s0 + 51])
        [a0 + 4, a0 + 5, a0 + 6, a0 + 7, a0 + 11, a0 + 15, a0 + 16, a0 + 17, a0 + 18] :=
      Env.Frame.mono e3 (fun i hi => List.mem_append.2 ((List.mem_append.1 hi).imp id (fun h => by simp at h ⊢; omega)))
        (fun x hx => List.mem_append.2 ((List.mem_append.1 hx).imp id (fun h => by simp at h ⊢; omega)))
        (fun b hb => by simp at hb ⊢; omega)
    have hF3' : Env.Frame σ' { (σ''.setNat (n0 + 15) (t + 1)) with draws := σ'.draws }
        (pgTmpN n0 ++ [n0 + 13, n0 + 15])
        (pgTmpS s0 ++ [s0 + 36, s0 + 37, s0 + 38, s0 + 39, s0 + 40, s0 + 44, s0 + 45, s0 + 46, s0 + 47, s0 + 49,
          s0 + 51])
        [a0 + 4, a0 + 5, a0 + 6, a0 + 7, a0 + 11, a0 + 15, a0 + 16, a0 + 17, a0 + 18] :=
      Env.Frame.setNat hF'' (by simp) _
    have hws : (fun k => WithLp.toLp 2 fun c : Fin d => w.gs (σ'.draws + k * d + c) :
        ℕ → EuclideanSpace ℝ (Fin d)) = wsT t := by
      funext k
      simp only [wsT, hdr']
      congr 1
      funext c
      congr 1
      ring
    rw [hws, hR'] at e1
    have hV3 := hV'.of_frame hF3' (by simp [pgTmpN] <;> omega) (by simp [pgTmpS] <;> omega)
    have hP3 := hP'.of_frame hF3' (by simp <;> omega) (by simp <;> omega)
    have hX3 := hX'.of_frame hF3' (by simp) (by simp)
    refine ⟨hV3, hP3, hX3, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show σ''.sc (s0 + 42) = _
      rw [e3.2.1 _ (by simp [pgTmpS] <;> omega)]; exact hR'
    · exact (hF3'.1 dv (by simp [pgTmpN] <;> omega)).trans hd'
    · exact (hF3'.1 (n0 + 14) (by simp [pgTmpN])).trans hm'
    · show σ''.sc (s0 + 40) = _
      rw [e1, hc', hcnt]
      simp only [Finset.sum_range_succ]
      rfl
    · show σ''.draws = σ.draws + (t + 1) * (pgNT d ρ * d)
      rw [e2, hdr']; ring
    · exact frameD_trans hF' hF3'
  -- the majority
  obtain ⟨hJ7, -, -, h17⟩ := h7
  obtain ⟨-, -, -, -, -, hm7, hc7, hdr7, hF7⟩ := hJ7
  refine runs_seq_eq (runs_ncast (by omega) (by omega)) ?_
  refine runs_seq_eq (runs_sconst (by omega) (1 / 2)) ?_
  refine runs_seq_eq (runs_sop2 (by omega) (by omega) (by omega) .mul) ?_
  refine runs_seq_eq (runs_sconst (by omega) 0) ?_
  set σ8 := (((σ7.setSc (s0 + 45) (σ7.nat (n0 + 14))).setSc (s0 + 1) ((1 / 2 : ℚ) : ℝ)).setSc (s0 + 45)
    (Op2.mul.eval (((σ7.setSc (s0 + 45) (σ7.nat (n0 + 14))).setSc (s0 + 1) ((1 / 2 : ℚ) : ℝ)).sc (s0 + 45))
      (((σ7.setSc (s0 + 45) (σ7.nat (n0 + 14))).setSc (s0 + 1) ((1 / 2 : ℚ) : ℝ)).sc (s0 + 1)))).setSc (s0 + 49)
    ((0 : ℚ) : ℝ) with hσ8
  have hF8 : Env.Frame σ7 σ8 [] [s0 + 1, s0 + 45, s0 + 49] [] :=
    Env.Frame.setSc (Env.Frame.setSc (Env.Frame.setSc (Env.Frame.setSc (Env.Frame.refl σ7 _ _ _) (by simp) _)
      (by simp) _) (by simp) _) (by simp) _
  have h45 : σ8.sc (s0 + 45) = (pgMT δ : ℝ) * ((1 / 2 : ℚ) : ℝ) := by
    simp [σ8, Op2.eval, hm7]
  have h40 : σ8.sc (s0 + 40) = cnt (pgMT δ) := by
    rw [hF8.2.1 _ (by simp)]; exact hc7
  have hfin : ∀ σ' : Env d, Env.Frame σ8 σ' [] [s0 + 49] [] → σ'.sc (s0 + 49) =
      (if pgTestS K' ρ δ X wsT then 1 else 0) → σ'.sc (s0 + 49) = (if pgTestS K' ρ δ X wsT then 1 else 0) ∧
        σ'.draws = σ.draws + pgMT δ * (pgNT d ρ * d) ∧
        Env.Frame σ { σ' with draws := σ.draws } (pgTmpN n0 ++ [n0 + 13, n0 + 15])
          (pgTmpS s0 ++ [s0 + 36, s0 + 37, s0 + 38, s0 + 39, s0 + 40, s0 + 44, s0 + 45, s0 + 46, s0 + 47, s0 + 49,
            s0 + 51])
          [a0 + 4, a0 + 5, a0 + 6, a0 + 7, a0 + 11, a0 + 15, a0 + 16, a0 + 17, a0 + 18] := by
    intro σ' hF hv
    refine ⟨hv, ?_, ?_⟩
    · rw [hF.2.2.2.1, hF8.2.2.2.1, hdr7]
    · have hF8' : Env.Frame σ7 σ' [] [s0 + 1, s0 + 45, s0 + 49] [] :=
        Env.Frame.trans hF8 (Env.Frame.mono hF (by simp) (by simp) (by simp))
      exact frameD_trans hF7 (frameD_of_frame (Env.Frame.mono hF8' (by simp) (by simp [pgTmpS]) (by simp)))
  have hcount := pgTestS_count K' ρ δ X wsT
  by_cases hc : σ8.sc (s0 + 45) < σ8.sc (s0 + 40)
  · refine runs_mono (runs_ifS_t (by omega) (by omega) hc (runs_sconst (by omega) 1)) le_rfl ?_
    rintro σ' rfl
    have hT : pgTestS K' ρ δ X wsT := hcount.1 (by rw [h45, h40] at hc; exact hc)
    exact hfin _ (Env.Frame.setSc (Env.Frame.refl σ8 _ _ _) (by simp) _) (by simp [hT])
  · refine runs_mono (runs_ifS_f (by omega) (by omega) hc (runs_skip σ8)) le_rfl ?_
    rintro σ' rfl
    have hT : ¬ pgTestS K' ρ δ X wsT := fun hT => hc (by rw [h45, h40]; exact hcount.2 hT)
    exact hfin _ (Env.Frame.refl σ8 _ _ _) (by simp [σ8, hT])

/-! ## One repeat -/

open Classical in
theorem runs_pgRepNS {L : Layout} {w : World d} {dv one n0 s0 a0 muv Av : ℕ} {ρ δ : ℝ} {P : PgSp d}
    (σ : Env d) (hn0 : n0 + 20 ≤ L.NN) (hs0 : s0 + 64 ≤ L.NS) (ha0 : a0 + 32 ≤ L.NA) (hdv : dv < L.NN)
    (hone : one < L.NN) (hdvb : dv < n0 ∨ n0 + 20 ≤ dv) (honeb : one < n0 ∨ n0 + 20 ≤ one) (hd : σ.nat dv = d)
    (h1 : σ.nat one = 1) (hmuv : muv < L.NA) (hAv : Av < L.NA) (hmub : muv < a0 ∨ a0 + 32 ≤ muv)
    (hAb : Av < a0 ∨ a0 + 32 ≤ Av) (hd1 : 1 ≤ d) (hρ1 : 1 ≤ ρ) (hV : PgStageVars σ n0 s0 ρ) (hP : PgAt σ muv Av P)
    (hmT : σ.nat (n0 + 14) = pgMT δ) (hf : σ.sc (s0 + 41) = 0 ∨ σ.sc (s0 + 41) = 1) :
    Runs L w (pgRepNS L dv one n0 s0 a0 muv Av) σ
      (kRepNS d (pgJb d ρ) (pgNs d ρ) (pgNT d ρ) (pgMT δ) (nsK d ρ) (Nat.clog 2 (3 * nsK d ρ + 3)) (nsCount (nsK d ρ)))
      (fun σ' =>
        let D := pgDescentN clampNSRoutine (pgKi w.K (σ.sc (s0 + 42)) P) ρ (fun k => WithLp.toLp 2 fun c => w.gs (σ.draws + k * d + c))
        let T := pgTestS (pgKi w.K (σ.sc (s0 + 42)) P) ρ δ D
          (fun v k => WithLp.toLp 2 fun c => w.gs (σ.draws + pgNs d ρ * d + (v * pgNT d ρ + k) * d + c))
        (σ.sc (s0 + 41) = 0 → T → σ'.sc (s0 + 41) = 1 ∧ PgAt σ' (a0 + 19) (a0 + 20) D) ∧
        (¬ (σ.sc (s0 + 41) = 0 ∧ T) → σ'.sc (s0 + 41) = σ.sc (s0 + 41) ∧ σ'.arr (a0 + 19) = σ.arr (a0 + 19) ∧
          σ'.arr (a0 + 20) = σ.arr (a0 + 20)) ∧
        σ'.draws = σ.draws + (pgNs d ρ + pgMT δ * pgNT d ρ) * d ∧
        Env.Frame σ { σ' with draws := σ.draws } (pgTmpN n0 ++ [n0 + 13, n0 + 15])
          (pgTmpS s0 ++ [s0 + 31, s0 + 33, s0 + 34, s0 + 35, s0 + 36, s0 + 37, s0 + 38, s0 + 39, s0 + 40, s0 + 41,
            s0 + 44, s0 + 45, s0 + 46, s0 + 47, s0 + 49, s0 + 51])
          [a0, a0 + 1, a0 + 2, a0 + 3, a0 + 4, a0 + 5, a0 + 6, a0 + 7, a0 + 8, a0 + 9, a0 + 10, a0 + 11, a0 + 12,
            a0 + 13, a0 + 14, a0 + 15, a0 + 16, a0 + 17, a0 + 18, a0 + 19, a0 + 20]) := by
  set K' := pgKi w.K (σ.sc (s0 + 42)) P with hK'
  set D := pgDescentN clampNSRoutine K' ρ (fun k => WithLp.toLp 2 fun c => w.gs (σ.draws + k * d + c)) with hD
  set T := pgTestS K' ρ δ D
    (fun v k => WithLp.toLp 2 fun c => w.gs (σ.draws + pgNs d ρ * d + (v * pgNT d ρ + k) * d + c)) with hT
  unfold pgRepNS kRepNS
  refine runs_seq (runs_pgDescNS σ hn0 hs0 ha0 hdv hone hdvb honeb hd h1 hmuv hAv hmub hAb hd1 hρ1 hV hP)
    fun σ1 h1' => ?_
  obtain ⟨hX1, hdr1, hF1⟩ := h1'
  rw [← hK', ← hD] at hX1
  have hFn1 : ∀ k, k ∉ pgTmpN n0 ++ [n0 + 13] → σ1.nat k = σ.nat k := fun k hk => hF1.1 k hk
  have hFs1 : ∀ x, x ∉ pgTmpS s0 ++ [s0 + 31, s0 + 33, s0 + 34, s0 + 35, s0 + 36, s0 + 45] → σ1.sc x = σ.sc x :=
    fun x hx => hF1.2.1 x hx
  have hV1 := hV.of_frame hF1 (by simp [pgTmpN] <;> omega) (by simp [pgTmpS] <;> omega)
  have hP1 := hP.of_frame hF1 (by simp <;> omega) (by simp <;> omega)
  refine runs_seq (runs_pgTestCNS (δ := δ) σ1 hn0 hs0 ha0 hdv hone hdvb honeb
    ((hFn1 _ (by simp [pgTmpN] <;> omega)).trans hd) ((hFn1 _ (by simp [pgTmpN] <;> omega)).trans h1) hmuv hAv hmub hAb
    hV1 hP1 hX1 ((hFn1 _ (by simp [pgTmpN])).trans hmT)) fun σ2 h2 => ?_
  obtain ⟨hpass, hdr2, hF2⟩ := h2
  rw [hFs1 _ (by simp [pgTmpS]), ← hK', hdr1] at hpass
  rw [← hT] at hpass
  have hF12 : Env.Frame σ { σ2 with draws := σ.draws } (pgTmpN n0 ++ [n0 + 13, n0 + 15])
      (pgTmpS s0 ++ [s0 + 31, s0 + 33, s0 + 34, s0 + 35, s0 + 36, s0 + 37, s0 + 38, s0 + 39, s0 + 40, s0 + 41,
        s0 + 44, s0 + 45, s0 + 46, s0 + 47, s0 + 49, s0 + 51])
      [a0, a0 + 1, a0 + 2, a0 + 3, a0 + 4, a0 + 5, a0 + 6, a0 + 7, a0 + 8, a0 + 9, a0 + 10, a0 + 11, a0 + 12,
        a0 + 13, a0 + 14, a0 + 15, a0 + 16, a0 + 17, a0 + 18, a0 + 19, a0 + 20] :=
    frameD_trans (Env.Frame.mono hF1 (fun i hi => List.mem_append.2 ((List.mem_append.1 hi).imp id (fun h => by simp at h ⊢; omega)))
        (fun x hx => List.mem_append.2 ((List.mem_append.1 hx).imp id (fun h => by simp at h ⊢; omega)))
        (fun b hb => by simp at hb ⊢; omega))
      (Env.Frame.mono hF2 (fun i hi => hi)
        (fun x hx => List.mem_append.2 ((List.mem_append.1 hx).imp id (fun h => by simp at h ⊢; omega)))
        (fun b hb => by simp at hb ⊢; omega))
  have h41 : σ2.sc (s0 + 41) = σ.sc (s0 + 41) := by
    rw [hF2.2.1 _ (by simp [pgTmpS] <;> omega), hFs1 _ (by simp [pgTmpS] <;> omega)]
  have h19 : σ2.arr (a0 + 19) = σ.arr (a0 + 19) := by
    rw [hF2.2.2.1 _ (by simp), hF1.2.2.1 _ (by simp)]
  have h20 : σ2.arr (a0 + 20) = σ.arr (a0 + 20) := by
    rw [hF2.2.2.1 _ (by simp), hF1.2.2.1 _ (by simp)]
  have hX2 := hX1.of_frame hF2 (by simp) (by simp)
  have hdr2' : σ2.draws = σ.draws + (pgNs d ρ + pgMT δ * pgNT d ρ) * d := by rw [hdr2, hdr1]; ring
  have hd2 : σ2.nat dv = d := by
    rw [hF2.1 _ (by simp [pgTmpN] <;> omega), hFn1 _ (by simp [pgTmpN] <;> omega)]; exact hd
  have h12 : σ2.nat one = 1 := by
    rw [hF2.1 _ (by simp [pgTmpN] <;> omega), hFn1 _ (by simp [pgTmpN] <;> omega)]; exact h1
  have hdd2 : σ2.nat (n0 + 9) = d * d := by
    rw [hF2.1 _ (by simp [pgTmpN]), hFn1 _ (by simp [pgTmpN])]; exact hV.1
  -- the keep
  refine runs_seq_eq (runs_sconst (by omega) 0) ?_
  refine runs_seq_eq (runs_sconst (by omega) 1) ?_
  set σ3 := (σ2.setSc s0 ((0 : ℚ) : ℝ)).setSc (s0 + 2) ((1 : ℚ) : ℝ) with hσ3
  have hF3 : Env.Frame σ2 σ3 [] [s0, s0 + 2] [] :=
    Env.Frame.setSc (Env.Frame.setSc (Env.Frame.refl σ2 _ _ _) (by simp) _) (by simp) _
  have e0 : σ3.sc s0 = 0 := by simp [σ3]
  have e2 : σ3.sc (s0 + 2) = 1 := by simp [σ3]
  have e41 : σ3.sc (s0 + 41) = σ.sc (s0 + 41) := by rw [hF3.2.1 _ (by simp), h41]
  have e49 : σ3.sc (s0 + 49) = if T then 1 else 0 := by rw [hF3.2.1 _ (by simp), hpass]
  have hfin : ∀ σ' : Env d, Env.Frame σ3 σ' [n0] [s0 + 8, s0 + 41] [a0 + 19, a0 + 20] →
      (σ.sc (s0 + 41) = 0 → T → σ'.sc (s0 + 41) = 1 ∧ PgAt σ' (a0 + 19) (a0 + 20) D) →
      (¬ (σ.sc (s0 + 41) = 0 ∧ T) → σ'.sc (s0 + 41) = σ.sc (s0 + 41) ∧ σ'.arr (a0 + 19) = σ.arr (a0 + 19) ∧
          σ'.arr (a0 + 20) = σ.arr (a0 + 20)) →
      (σ.sc (s0 + 41) = 0 → T → σ'.sc (s0 + 41) = 1 ∧ PgAt σ' (a0 + 19) (a0 + 20) D) ∧
        (¬ (σ.sc (s0 + 41) = 0 ∧ T) → σ'.sc (s0 + 41) = σ.sc (s0 + 41) ∧ σ'.arr (a0 + 19) = σ.arr (a0 + 19) ∧
          σ'.arr (a0 + 20) = σ.arr (a0 + 20)) ∧
        σ'.draws = σ.draws + (pgNs d ρ + pgMT δ * pgNT d ρ) * d ∧
        Env.Frame σ { σ' with draws := σ.draws } (pgTmpN n0 ++ [n0 + 13, n0 + 15])
          (pgTmpS s0 ++ [s0 + 31, s0 + 33, s0 + 34, s0 + 35, s0 + 36, s0 + 37, s0 + 38, s0 + 39, s0 + 40, s0 + 41,
            s0 + 44, s0 + 45, s0 + 46, s0 + 47, s0 + 49, s0 + 51])
          [a0, a0 + 1, a0 + 2, a0 + 3, a0 + 4, a0 + 5, a0 + 6, a0 + 7, a0 + 8, a0 + 9, a0 + 10, a0 + 11, a0 + 12,
            a0 + 13, a0 + 14, a0 + 15, a0 + 16, a0 + 17, a0 + 18, a0 + 19, a0 + 20] := by
    intro σ' hF hA hB
    refine ⟨hA, hB, ?_, ?_⟩
    · rw [hF.2.2.2.1, hF3.2.2.2.1, hdr2']
    · have hF' : Env.Frame σ2 σ' [n0] [s0, s0 + 2, s0 + 8, s0 + 41] [a0 + 19, a0 + 20] :=
        Env.Frame.trans (Env.Frame.mono hF3 (by simp) (by simp) (by simp)) (Env.Frame.mono hF (by simp) (by simp) (by simp))
      exact frameD_trans hF12 (frameD_of_frame (Env.Frame.mono hF' (by simp [pgTmpN]) (by simp [pgTmpS]) (by simp)))
  have h19' : σ3.arr (a0 + 19) = σ.arr (a0 + 19) := by rw [hF3.2.2.1 _ (by simp), h19]
  have h20' : σ3.arr (a0 + 20) = σ.arr (a0 + 20) := by rw [hF3.2.2.1 _ (by simp), h20]
  rcases hf with hf0 | hf1
  · -- nothing kept before
    have hc1 : σ3.sc (s0 + 41) < σ3.sc (s0 + 2) := by rw [e41, e2, hf0]; norm_num
    by_cases hTp : T
    · have hc2 : σ3.sc s0 < σ3.sc (s0 + 49) := by rw [e0, e49, if_pos hTp]; norm_num
      refine runs_ifS_t (by omega) (by omega) hc1 (runs_ifS_t (by omega) (by omega) hc2
        (runs_seq_eq (runs_sconst (by omega) 1) (runs_seq (runs_vcopy _ hdv hone (by omega) (by omega) (by omega)
          (by omega) (by omega) (by omega) (by rw [Env.setSc_nat, hF3.1 _ (by simp)]; exact hd2)
          (by rw [Env.setSc_nat, hF3.1 _ (by simp)]; exact h12)) fun σ4 h4 => ?_)))
      obtain ⟨hv4, hF4, -⟩ := h4
      refine runs_mono (runs_mcopy σ4 (by omega) hone (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by rw [hF4.1 _ (by simp <;> omega), Env.setSc_nat, hF3.1 _ (by simp)]; exact hdd2)
        (by rw [hF4.1 _ (by simp <;> omega), Env.setSc_nat, hF3.1 _ (by simp)]; exact h12)) le_rfl ?_
      rintro σ5 ⟨hm5, hF5, -⟩
      have hF35 : Env.Frame σ3 σ5 [n0] [s0 + 8, s0 + 41] [a0 + 19, a0 + 20] :=
        Env.Frame.trans (Env.Frame.setSc (Env.Frame.refl σ3 _ _ _) (by simp) _)
          (Env.Frame.trans (Env.Frame.mono hF4 (by simp) (by simp) (by simp))
            (Env.Frame.mono hF5 (by simp) (by simp) (by simp)))
      refine hfin σ5 hF35 (fun _ _ => ⟨?_, ?_, ?_⟩) (fun h => absurd ⟨hf0, hTp⟩ h)
      · rw [hF5.2.1 _ (by simp), hF4.2.1 _ (by simp)]; simp
      · rw [Env.vec_of_arr (hF5.2.2.1 _ (by simp)), hv4]
        exact hX2.1
      · rw [hm5, Env.mat_of_arr (hF4.2.2.1 _ (by simp))]
        exact hX2.2
    · have hc2 : ¬ σ3.sc s0 < σ3.sc (s0 + 49) := by rw [e0, e49, if_neg hTp]; norm_num
      refine runs_mono (runs_ifS_t (by omega) (by omega) hc1 (runs_ifS_f (by omega) (by omega) hc2 (runs_skip σ3)))
        (by omega) ?_
      rintro σ' rfl
      exact hfin σ3 (Env.Frame.refl σ3 _ _ _) (fun _ h => absurd h hTp) (fun _ => ⟨e41, h19', h20'⟩)
  · -- a repeat was kept before
    have hc1 : ¬ σ3.sc (s0 + 41) < σ3.sc (s0 + 2) := by rw [e41, e2, hf1]; norm_num
    refine runs_mono (runs_ifS_f (by omega) (by omega) hc1 (runs_skip σ3)) (by omega) ?_
    rintro σ' rfl
    exact hfin σ3 (Env.Frame.refl σ3 _ _ _) (fun h => by rw [hf1] at h; norm_num at h) (fun _ => ⟨e41, h19', h20'⟩)


end AdversarialBco.Conj1Arith
