/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.MachPGLoops
public import AdversarialBco.Poly.MachGauge

@[expose] public section

/-!
# Procedure PG in VL: the leaves of a stage from their parts

The rules of the step of the descent (`runs_pgStepM`) and of a sample of a verdict (`runs_pgSampleM`), the fields
`stepM` and `sampleM` of `PgLeaves`, from the rules of the gauge (`runs_pgGauge`, through `gaugeBis` with the body of
the stage as invariant), of `T⁻¹` (`runs_pgVinv`) and of the matrix part of `V` (`runs_pgVmat`). The rules these rest
on, the membership code of the body, `g gᵀ - I`, the move and projection, Gauss-Jordan and the three parts of the
verdict, enter through the hypothesis `PgParts`; with `runs_mmul` of MachMat.lean they give `PgLeaves`
(`PgParts.leaves`).
-/

open AdversarialBco AdversarialBco.RealRAM AdversarialBco.Poly AdversarialBco.Poly.Mach AdversarialBco.Poly.Mach.VL
  Matrix

namespace AdversarialBco.Poly.PG

open Classical in
/-- The rules of the parts of a stage that `PgLeaves` rests on. -/
structure PgParts : Prop where
  memQ : ∀ {d : ℕ} {L : Layout} {w : World d} {dv one n0 s0 a0 muv Av : ℕ}
      (σ : Env d) (hn0 : n0 + 20 ≤ L.NN) (hs0 : s0 + 64 ≤ L.NS) (ha0 : a0 + 32 ≤ L.NA) (hdv : dv < L.NN) (hone : one < L.NN)
      (hdvb : dv < n0 ∨ n0 + 20 ≤ dv) (honeb : one < n0 ∨ n0 + 20 ≤ one) (hd : σ.nat dv = d) (h1 : σ.nat one = 1)
      (hmuv : muv < L.NA) (hAv : Av < L.NA) (hmub : muv < a0 ∨ a0 + 32 ≤ muv) (hAb : Av < a0 ∨ a0 + 32 ≤ Av),
      Runs L w (pgMemQ L dv one n0 s0 a0 muv Av) σ (kMemQ d)
        (fun σ' => σ'.sc (s0 + 15) =
            (if WithLp.toLp 2 (σ.vec (a0 + 6)) ∈ pgBodySet w.K (σ.vec muv) (σ.mat Av) (σ.sc (s0 + 42)) then 1 else 0) ∧
          Env.Frame σ σ' [n0, n0 + 1, n0 + 2] [s0 + 8, s0 + 9, s0 + 11, s0 + 15, s0 + 16, s0 + 17] [a0 + 7])
  ggcode : ∀ {d : ℕ} {L : Layout} {w : World d} {dv one n0 s0 a0 : ℕ}
      (σ : Env d) (hn0 : n0 + 20 ≤ L.NN) (hs0 : s0 + 64 ≤ L.NS) (ha0 : a0 + 32 ≤ L.NA) (hdv : dv < L.NN) (hone : one < L.NN)
      (hdvb : dv < n0 ∨ n0 + 20 ≤ dv) (honeb : one < n0 ∨ n0 + 20 ≤ one) (hd : σ.nat dv = d) (h1 : σ.nat one = 1)
      (hdd : σ.nat (n0 + 9) = d * d),
      Runs L w (pgGGcode L dv one n0 s0 a0) σ (kGG d)
        (fun σ' => σ'.mat (a0 + 11) = vecMulVec (σ.vec (a0 + 4)) (σ.vec (a0 + 4)) - 1 ∧ σ'.sc s0 = 0 ∧
          σ'.sc (s0 + 2) = 1 ∧
          Env.Frame σ σ' [n0, n0 + 1, n0 + 2] [s0, s0 + 2, s0 + 8, s0 + 9, s0 + 10, s0 + 36] [a0 + 11])
  upd : ∀ {d : ℕ} {L : Layout} {w : World d} {dv one n0 s0 a0 : ℕ}
      (σ : Env d) (hn0 : n0 + 20 ≤ L.NN) (hs0 : s0 + 64 ≤ L.NS) (ha0 : a0 + 32 ≤ L.NA) (hdv : dv < L.NN) (hone : one < L.NN)
      (hdvb : dv < n0 ∨ n0 + 20 ≤ dv) (honeb : one < n0 ∨ n0 + 20 ≤ one) (hd : σ.nat dv = d) (h1 : σ.nat one = 1)
      (hdd : σ.nat (n0 + 9) = d * d),
      Runs L w (pgUpd L dv one n0 s0 a0) σ (kUpd d)
        (fun σ' => WithLp.toLp 2 (σ'.vec a0) =
            ballClip (σ.sc (s0 + 23)) (WithLp.toLp 2 (σ.vec a0 + σ.sc (s0 + 30) • σ.vec (a0 + 10))) ∧
          σ'.mat (a0 + 1) = cfc (Spec.fn .clamp (σ.sc (s0 + 21)) (σ.sc (s0 + 22)))
            (symPart (σ.mat (a0 + 1) + σ.sc (s0 + 30) • σ.mat (a0 + 14))) ∧
          Env.Frame σ σ' [n0] [s0 + 2, s0 + 8, s0 + 9, s0 + 34, s0 + 35] [a0, a0 + 1])
  gjCode : ∀ {d : ℕ} {L : AdversarialBco.Poly.Mach.Layout}
      {w : AdversarialBco.RealRAM.World d} {dv one dd i j kk ri rk ij kj T A B p ip o z f t1 t2 : ℕ}
      (σ : Env d) (hdv : dv < L.NN) (hone : one < L.NN) (hdd : dd < L.NN)
      (hi : i < L.NN) (hj : j < L.NN) (hkk : kk < L.NN) (hri : ri < L.NN) (hrk : rk < L.NN) (hij : ij < L.NN)
      (hkj : kj < L.NN) (hT : T < L.NA) (hA : A < L.NA) (hB : B < L.NA) (hp : p < L.NS) (hip : ip < L.NS)
      (ho : o < L.NS) (hz : z < L.NS) (hf : f < L.NS) (ht1 : t1 < L.NS) (ht2 : t2 < L.NS)
      (hN : [i, j, kk, ri, rk, ij, kj].Nodup) (hNo : ∀ q ∈ [i, j, kk, ri, rk, ij, kj], q ∉ [dv, one, dd])
      (hAr : [T, A, B].Nodup) (hS : [p, ip, o, z, f, t1, t2].Nodup) (hd : σ.nat dv = d) (h1 : σ.nat one = 1)
      (hddv : σ.nat dd = d * d),
      AdversarialBco.Poly.Mach.Runs L w (gjCode L dv one dd i j kk ri rk ij kj T A B p ip o z f t1 t2) σ
        (d * (d * d * 21 + d * 31 + 17) + d * d * 12 + d * 7 + 16)
        (fun σ' => (σ'.mat A, σ'.mat B) = gjRun (σ.mat T) d ∧
          Env.Frame σ σ' [i, j, kk, ri, rk, ij, kj] [p, ip, o, z, f, t1, t2] [A, B])
  verdNorm : ∀ {d : ℕ} {L : Layout} {w : World d} {dv one n0 s0 a0 : ℕ}
      (σ : Env d) (hn0 : n0 + 20 ≤ L.NN) (hs0 : s0 + 64 ≤ L.NS) (ha0 : a0 + 32 ≤ L.NA) (hdv : dv < L.NN) (hone : one < L.NN)
      (hdvb : dv < n0 ∨ n0 + 20 ≤ dv) (honeb : one < n0 ∨ n0 + 20 ≤ one) (hd : σ.nat dv = d) (h1 : σ.nat one = 1)
      (hdd : σ.nat (n0 + 9) = d * d),
      Runs L w (pgVerdNorm L dv one n0 s0 a0) σ (kVerdNorm d)
        (fun σ' => σ'.sc (s0 + 37) = ((σ.nat (n0 + 12) : ℝ))⁻¹ * σ.sc (s0 + 37) ∧
          σ'.vec (a0 + 15) = ((σ.nat (n0 + 12) : ℝ))⁻¹ • σ.vec (a0 + 15) ∧
          σ'.mat (a0 + 16) = ((σ.nat (n0 + 12) : ℝ))⁻¹ • σ.mat (a0 + 16) ∧
          Env.Frame σ σ' [n0] [s0, s0 + 2, s0 + 8, s0 + 9, s0 + 37, s0 + 45, s0 + 46] [a0 + 15, a0 + 16])
  verdC12 : ∀ {d : ℕ} {L : Layout} {w : World d} {dv one n0 s0 a0 : ℕ}
      (σ : Env d) (hn0 : n0 + 20 ≤ L.NN) (hs0 : s0 + 64 ≤ L.NS) (ha0 : a0 + 32 ≤ L.NA) (hdv : dv < L.NN) (hone : one < L.NN)
      (hdvb : dv < n0 ∨ n0 + 20 ≤ dv) (honeb : one < n0 ∨ n0 + 20 ≤ one) (hd : σ.nat dv = d) (h1 : σ.nat one = 1),
      Runs L w (pgVerdC12 L dv one n0 s0 a0) σ (kVerdC12 d)
        (fun σ' => σ'.sc (s0 + 39) = (if σ.sc (s0 + 37) ≤ 43 / 320 ∧
            Real.sqrt (σ.vec (a0 + 15) ⬝ᵥ σ.vec (a0 + 15)) ≤ 3 / 4 * σ.sc (s0 + 28) then 1 else 0) ∧
          Env.Frame σ σ' [n0] [s0 + 8, s0 + 9, s0 + 38, s0 + 39, s0 + 47] [])
  verdC3 : ∀ {d : ℕ} {L : Layout} {w : World d} {dv one n0 s0 a0 : ℕ}
      (σ : Env d) (hn0 : n0 + 20 ≤ L.NN) (hs0 : s0 + 64 ≤ L.NS) (ha0 : a0 + 32 ≤ L.NA) (hdv : dv < L.NN) (hone : one < L.NN)
      (hdvb : dv < n0 ∨ n0 + 20 ≤ dv) (honeb : one < n0 ∨ n0 + 20 ≤ one) (hd : σ.nat dv = d) (h1 : σ.nat one = 1)
      (hdd : σ.nat (n0 + 9) = d * d),
      Runs L w (pgVerdC3 L dv one n0 s0 a0) σ (kVerdC3 d)
        (fun σ' => σ'.sc (s0 + 39) = (if 0 < (cfc (Spec.fn .step 0 0)
              (symPart (((-5 / 8 : ℝ) * σ.sc (s0 + 32)) • (1 : Matrix (Fin d) (Fin d) ℝ) - σ.mat (a0 + 16)))).trace
            then 0 else σ.sc (s0 + 39)) ∧
          Env.Frame σ σ' [n0, n0 + 2] [s0, s0 + 2, s0 + 8, s0 + 9, s0 + 36, s0 + 39, s0 + 44, s0 + 47, s0 + 51]
            [a0 + 17, a0 + 18])

theorem runs_pgGauge (hP : PgParts) {d : ℕ} {L : Layout} {w : World d} {dv one n0 s0 a0 muv Av xm xT : ℕ}
    (σ : Env d) (hn0 : n0 + 20 ≤ L.NN) (hs0 : s0 + 64 ≤ L.NS) (ha0 : a0 + 32 ≤ L.NA) (hdv : dv < L.NN) (hone : one < L.NN)
    (hdvb : dv < n0 ∨ n0 + 20 ≤ dv) (honeb : one < n0 ∨ n0 + 20 ≤ one) (hd : σ.nat dv = d) (h1 : σ.nat one = 1)
    (hmuv : muv < L.NA) (hAv : Av < L.NA) (hmub : muv < a0 ∨ a0 + 32 ≤ muv) (hAb : Av < a0 ∨ a0 + 32 ≤ Av)
    (hxm : xm < L.NA) (hxT : xT < L.NA) (hxmb : xm ∉ [a0 + 5, a0 + 6, a0 + 7]) (hxTb : xT ∉ [a0 + 5, a0 + 6, a0 + 7]) :
    Runs L w (pgGauge L dv one n0 s0 a0 muv Av xm xT) σ (kGauge d (σ.nat (n0 + 10)))
      (fun σ' => σ'.sc (s0 + 18) = piTilde (pgBodySet w.K (σ.vec muv) (σ.mat Av) (σ.sc (s0 + 42))) (σ.sc (s0 + 19))
            (σ.nat (n0 + 10)) (WithLp.toLp 2 (σ.mat xT *ᵥ σ.vec (a0 + 4) + σ.vec xm)) ∧
        Env.Frame σ σ' [n0, n0 + 1, n0 + 2, n0 + 8] (pgTmpS s0) [a0 + 5, a0 + 6, a0 + 7]) := by
  have hS0 : s0 < L.NS := by omega
  unfold pgGauge kGauge
  refine runs_seq (runs_matvec (i := n0) (j := n0 + 1) (k := n0 + 2) (y := a0 + 5) (A := xT) (x := a0 + 4)
    (s := s0 + 11) (t1 := s0 + 8) (t2 := s0 + 9) σ hdv hone (by omega) (by omega) (by omega) (by omega) hxT
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (fun h => hxTb (by rw [← h]; simp)) (by omega) (by omega) (by omega) hd h1)
    fun σ1 h1' => ?_
  obtain ⟨v1, F1, -⟩ := h1'
  have d1 : σ1.nat dv = d := (F1.1 _ (by simp; omega)).trans hd
  have o1 : σ1.nat one = 1 := (F1.1 _ (by simp; omega)).trans h1
  refine runs_seq_eq (runs_sconst (L := L) (w := w) (σ := σ1) (x := s0 + 2) (by omega) 1) ?_
  set σ2 := σ1.setSc (s0 + 2) ((1 : ℚ) : ℝ) with hσ2
  refine runs_seq (runs_vaxpy (i := n0) (y := a0 + 5) (x := xm) (α := s0 + 2) (t1 := s0 + 8) (t2 := s0 + 9) σ2 hdv
    hone (by omega) (by omega) hxm (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) d1 o1) fun σ3 h3 => ?_
  obtain ⟨v3, F3, -⟩ := h3
  have F03 : Env.Frame σ σ3 [n0, n0 + 1, n0 + 2] [s0 + 2, s0 + 8, s0 + 9, s0 + 11] [a0 + 5] :=
    Env.Frame.trans (Env.Frame.mono F1 (by simp) (by simp) (by simp))
      (Env.Frame.trans (Env.Frame.setSc (Env.Frame.refl σ1 [n0, n0 + 1, n0 + 2] [s0 + 2, s0 + 8, s0 + 9, s0 + 11]
        [a0 + 5]) (by simp) _) (Env.Frame.mono F3 (by simp) (by simp) (by simp)))
  have d3 : σ3.nat dv = d := (F03.1 _ (by simp; omega)).trans hd
  have o3 : σ3.nat one = 1 := (F03.1 _ (by simp; omega)).trans h1
  have j3 : σ3.nat (n0 + 10) = σ.nat (n0 + 10) := F03.1 _ (by simp)
  let Q := pgBodySet w.K (σ.vec muv) (σ.mat Av) (σ.sc (s0 + 42))
  let Iq : Env d → Prop := fun σ' => σ'.vec muv = σ.vec muv ∧ σ'.mat Av = σ.mat Av ∧ σ'.sc (s0 + 42) = σ.sc (s0 + 42)
  have hI3 : Iq σ3 := ⟨Env.vec_of_arr (F03.2.2.1 _ (by simp; omega)), Env.mat_of_arr (F03.2.2.1 _ (by simp; omega)),
    F03.2.1 _ (by simp)⟩
  refine runs_mono (runs_gaugeBis (L := L) (w := w) Q Iq (kMemQ d) [n0, n0 + 1, n0 + 2]
    [s0 + 8, s0 + 9, s0 + 11, s0 + 15, s0 + 16, s0 + 17] [a0 + 7] σ3 hdv hone (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by simp <;> omega) (by simp) (by simp <;> omega) (by simp) (by simp) d3 o3 hI3
    ?_ ?_) (le_of_eq (by rw [j3])) fun σ' h => ?_
  · intro σ' hI hd' h1'
    refine runs_mono (hP.memQ σ' hn0 hs0 ha0 hdv hone hdvb honeb hd' h1' hmuv hAv hmub hAb) le_rfl
      fun σ'' h => ⟨?_, h.2, ?_⟩
    · rw [h.1, hI.1, hI.2.1, hI.2.2]
    · exact ⟨(Env.vec_of_arr (h.2.2.2.1 _ (by simp; omega))).trans hI.1,
        (Env.mat_of_arr (h.2.2.2.1 _ (by simp; omega))).trans hI.2.1, (h.2.2.1 _ (by simp)).trans hI.2.2⟩
  · intro σ' σ'' hI hF
    exact ⟨(Env.vec_of_arr (hF.2.2.1 _ (by simp; omega))).trans hI.1,
      (Env.mat_of_arr (hF.2.2.1 _ (by simp; omega))).trans hI.2.1, (hF.2.1 _ (by simp)).trans hI.2.2⟩
  obtain ⟨hp, hF4, -⟩ := h
  refine ⟨?_, Env.Frame.trans (Env.Frame.mono F03 (by simp) (by simp [pgTmpS]) (by simp))
    (Env.Frame.mono hF4 (by simp) (by simp [pgTmpS]) (by simp))⟩
  rw [hp, F03.2.1 _ (by simp), j3, v3, show σ2.vec (a0 + 5) = σ1.vec (a0 + 5) from rfl, v1,
    show σ2.sc (s0 + 2) = 1 by simp [hσ2], one_smul, show σ2.vec xm = σ1.vec xm from rfl,
    Env.vec_of_arr (F1.2.2.1 xm (fun h => hxmb (by simp at h; simp [h])))]

theorem runs_pgVinv (hP : PgParts) {d : ℕ} {L : Layout} {w : World d} {dv one n0 s0 a0 : ℕ}
    (σ : Env d) (hn0 : n0 + 20 ≤ L.NN) (hs0 : s0 + 64 ≤ L.NS) (ha0 : a0 + 32 ≤ L.NA) (hdv : dv < L.NN) (hone : one < L.NN)
    (hdvb : dv < n0 ∨ n0 + 20 ≤ dv) (honeb : one < n0 ∨ n0 + 20 ≤ one) (hd : σ.nat dv = d) (h1 : σ.nat one = 1)
    (hdd : σ.nat (n0 + 9) = d * d) :
    Runs L w (pgVinv L dv one n0 s0 a0) σ (kVinv d)
      (fun σ' => σ'.mat (a0 + 8) = (gjRun (σ.mat (a0 + 1)) d).2 ∧
        σ'.vec (a0 + 10) = σ.sc (s0 + 18) • ((gjRun (σ.mat (a0 + 1)) d).2 *ᵥ σ.vec (a0 + 4)) ∧
        Env.Frame σ σ' [n0, n0 + 1, n0 + 2, n0 + 4, n0 + 5, n0 + 6, n0 + 7]
          [s0, s0 + 2, s0 + 8, s0 + 9, s0 + 11, s0 + 12, s0 + 13, s0 + 14] [a0 + 8, a0 + 9, a0 + 10]) := by
  unfold pgVinv kVinv kGJ
  refine runs_seq (hP.gjCode σ hdv hone (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by simp <;> omega) (by simp <;> omega) (by simp <;> omega) (by simp <;> omega) hd h1 hdd)
    fun σ1 h1' => ?_
  obtain ⟨g1, F1⟩ := h1'
  have m18 : σ1.mat (a0 + 8) = (gjRun (σ.mat (a0 + 1)) d).2 := congrArg Prod.snd g1
  have d1 : σ1.nat dv = d := (F1.1 _ (by simp <;> omega)).trans hd
  have o1 : σ1.nat one = 1 := (F1.1 _ (by simp <;> omega)).trans h1
  refine runs_seq (runs_matvec (i := n0) (j := n0 + 1) (k := n0 + 2) (y := a0 + 10) (A := a0 + 8) (x := a0 + 4)
    (s := s0 + 11) (t1 := s0 + 8) (t2 := s0 + 9) σ1 hdv hone (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) d1 o1) fun σ2 h2 => ?_
  obtain ⟨v2, F2, -⟩ := h2
  refine runs_mono (runs_vscale (i := n0) (y := a0 + 10) (α := s0 + 18) (t := s0 + 8) σ2 hdv hone (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) ((F2.1 _ (by simp <;> omega)).trans d1)
    ((F2.1 _ (by simp <;> omega)).trans o1)) le_rfl fun σ3 h3 => ?_
  obtain ⟨v3, F3, -⟩ := h3
  refine ⟨?_, ?_, Env.Frame.trans (Env.Frame.mono F1 (by simp) (by simp) (by simp))
    (Env.Frame.trans (Env.Frame.mono F2 (by simp) (by simp) (by simp)) (Env.Frame.mono F3 (by simp) (by simp) (by simp)))⟩
  · rw [Env.mat_of_arr (F3.2.2.1 _ (by simp)), Env.mat_of_arr (F2.2.2.1 _ (by simp)), m18]
  · rw [v3, v2, m18, F2.2.1 _ (by simp), F1.2.1 _ (by simp), Env.vec_of_arr (F1.2.2.1 _ (by simp))]

theorem runs_pgVmat (hP : PgParts) {d : ℕ} {L : Layout} {w : World d} {dv one n0 s0 a0 : ℕ}
    (σ : Env d) (hn0 : n0 + 20 ≤ L.NN) (hs0 : s0 + 64 ≤ L.NS) (ha0 : a0 + 32 ≤ L.NA) (hdv : dv < L.NN) (hone : one < L.NN)
    (hdvb : dv < n0 ∨ n0 + 20 ≤ dv) (honeb : one < n0 ∨ n0 + 20 ≤ one) (hd : σ.nat dv = d) (h1 : σ.nat one = 1)
    (hdd : σ.nat (n0 + 9) = d * d) :
    Runs L w (pgVmat L dv one n0 s0 a0) σ (kVmat d)
      (fun σ' => σ'.mat (a0 + 14) =
          (σ.sc (s0 + 18) / 2) • (σ.mat (a0 + 8) * (vecMulVec (σ.vec (a0 + 4)) (σ.vec (a0 + 4)) - 1) +
            (σ.mat (a0 + 8) * (vecMulVec (σ.vec (a0 + 4)) (σ.vec (a0 + 4)) - 1))ᵀ) + σ.sc (s0 + 32) • σ.mat (a0 + 8) ∧
        Env.Frame σ σ' [n0, n0 + 1, n0 + 2, n0 + 3, n0 + 4, n0 + 5, n0 + 6]
          [s0, s0 + 1, s0 + 2, s0 + 8, s0 + 9, s0 + 10, s0 + 11, s0 + 31, s0 + 36]
          [a0 + 11, a0 + 12, a0 + 13, a0 + 14]) := by
  unfold pgVmat kVmat
  refine runs_seq (hP.ggcode σ hn0 hs0 ha0 hdv hone hdvb honeb hd h1 hdd) fun σ1 h1' => ?_
  obtain ⟨m1, -, e12, F1⟩ := h1'
  have d1 : σ1.nat dv = d := (F1.1 _ (by simp <;> omega)).trans hd
  have o1 : σ1.nat one = 1 := (F1.1 _ (by simp <;> omega)).trans h1
  refine runs_seq (runs_mmul (i := n0) (j := n0 + 1) (l := n0 + 3) (kA := n0 + 4) (kB := n0 + 5) (kC := n0 + 6)
    (C := a0 + 12) (A := a0 + 8) (B := a0 + 11) (s := s0 + 11) (t1 := s0 + 8) (t2 := s0 + 9) σ1 hdv hone
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by simp <;> omega) (by simp <;> omega) (by simp <;> omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) d1 o1) fun σ2 h2 => ?_
  obtain ⟨m2, F2, -⟩ := h2
  have d2 : σ2.nat dv = d := (F2.1 _ (by simp <;> omega)).trans d1
  have o2 : σ2.nat one = 1 := (F2.1 _ (by simp <;> omega)).trans o1
  refine runs_seq (runs_mtransp (i := n0) (j := n0 + 1) (kA := n0 + 4) (kB := n0 + 5) (B := a0 + 13) (A := a0 + 12)
    (t := s0 + 8) σ2 hdv hone (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by simp <;> omega) (by simp <;> omega) (by simp <;> omega) d2 o2) fun σ3 h3 => ?_
  obtain ⟨m3, F3, -⟩ := h3
  refine runs_seq_eq (runs_sconst (L := L) (w := w) (σ := σ3) (x := s0 + 1) (by omega) (1 / 2)) ?_
  refine runs_seq_eq (runs_sop2 (L := L) (w := w) (σ := σ3.setSc (s0 + 1) (((1 / 2 : ℚ)) : ℝ)) (x := s0 + 31)
    (by omega) (by omega) (by omega) .mul) ?_
  set σ5 := (σ3.setSc (s0 + 1) (((1 / 2 : ℚ)) : ℝ)).setSc (s0 + 31)
    (Op2.mul.eval ((σ3.setSc (s0 + 1) (((1 / 2 : ℚ)) : ℝ)).sc (s0 + 18)) ((σ3.setSc (s0 + 1) (((1 / 2 : ℚ)) : ℝ)).sc
      (s0 + 1))) with hσ5
  have F35 : Env.Frame σ3 σ5 [] [s0 + 1, s0 + 31] [] :=
    Env.Frame.setSc (Env.Frame.setSc (Env.Frame.refl σ3 [] [s0 + 1, s0 + 31] []) (by simp) _) (by simp) _
  have F05 : Env.Frame σ σ5 [n0, n0 + 1, n0 + 2, n0 + 3, n0 + 4, n0 + 5, n0 + 6]
      [s0, s0 + 1, s0 + 2, s0 + 8, s0 + 9, s0 + 10, s0 + 11, s0 + 31, s0 + 36] [a0 + 11, a0 + 12, a0 + 13] :=
    Env.Frame.trans (Env.Frame.mono F1 (by simp) (by simp) (by simp))
      (Env.Frame.trans (Env.Frame.mono F2 (by simp) (by simp) (by simp))
        (Env.Frame.trans (Env.Frame.mono F3 (by simp) (by simp) (by simp))
          (Env.Frame.mono F35 (by simp) (by simp) (by simp))))
  have d5 : σ5.nat dv = d := (F05.1 _ (by simp <;> omega)).trans hd
  have o5 : σ5.nat one = 1 := (F05.1 _ (by simp <;> omega)).trans h1
  have dd5 : σ5.nat (n0 + 9) = d * d := (F05.1 _ (by simp)).trans hdd
  refine runs_seq (runs_mlin (m := n0) (C := a0 + 14) (A := a0 + 12) (B := a0 + 13) (α := s0 + 31) (β := s0 + 31)
    (t1 := s0 + 8) (t2 := s0 + 9) σ5 (by omega) hone (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    dd5 o5) fun σ6 h6 => ?_
  obtain ⟨m6, F6, -⟩ := h6
  refine runs_mono (runs_mlin (m := n0) (C := a0 + 14) (A := a0 + 14) (B := a0 + 8) (α := s0 + 2) (β := s0 + 32)
    (t1 := s0 + 8) (t2 := s0 + 9) σ6 (by omega) hone (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    ((F6.1 _ (by simp)).trans dd5) ((F6.1 _ (by simp <;> omega)).trans o5)) le_rfl fun σ7 h7 => ?_
  obtain ⟨m7, F7, -⟩ := h7
  refine ⟨?_, Env.Frame.trans (Env.Frame.mono F05 (by simp) (by simp) (by simp)) (Env.Frame.trans (Env.Frame.mono F6 (by simp) (by simp) (by simp))
    (Env.Frame.mono F7 (by simp) (by simp) (by simp)))⟩
  have e62 : σ6.sc (s0 + 2) = 1 := by
    rw [F6.2.1 _ (by simp), F35.2.1 _ (by simp), F3.2.1 _ (by simp), F2.2.1 _ (by simp)]; exact e12
  have e632 : σ6.sc (s0 + 32) = σ.sc (s0 + 32) := by
    rw [F6.2.1 _ (by simp)]; exact F05.2.1 _ (by simp)
  have e68 : σ6.mat (a0 + 8) = σ.mat (a0 + 8) := by
    rw [Env.mat_of_arr (F6.2.2.1 _ (by simp))]; exact Env.mat_of_arr (F05.2.2.1 _ (by simp))
  have e531 : σ5.sc (s0 + 31) = σ.sc (s0 + 18) / 2 := by
    rw [hσ5, Env.setSc_sc, if_pos rfl, Env.setSc_sc, if_neg (by omega), Env.setSc_sc, if_pos rfl,
      F3.2.1 _ (by simp), F2.2.1 _ (by simp), F1.2.1 _ (by simp)]
    simp only [Op2.eval]; push_cast; ring
  have e512 : σ5.mat (a0 + 12) = σ.mat (a0 + 8) * (vecMulVec (σ.vec (a0 + 4)) (σ.vec (a0 + 4)) - 1) := by
    rw [Env.mat_of_arr (F35.2.2.1 _ (by simp)), Env.mat_of_arr (F3.2.2.1 _ (by simp)), m2, m1,
      Env.mat_of_arr (F1.2.2.1 _ (by simp))]
  have e513 : σ5.mat (a0 + 13) = (σ.mat (a0 + 8) * (vecMulVec (σ.vec (a0 + 4)) (σ.vec (a0 + 4)) - 1))ᵀ := by
    rw [Env.mat_of_arr (F35.2.2.1 _ (by simp)), m3, m2, m1, Env.mat_of_arr (F1.2.2.1 _ (by simp))]
  rw [m7, e62, one_smul, m6, e632, e68, e531, e512, e513, smul_add]


set_option maxHeartbeats 1000000 in
theorem runs_pgStepM (hP : PgParts) {d : ℕ} {L : Layout} {w : World d} {dv one n0 s0 a0 muv Av : ℕ}
    (σ : Env d) (hn0 : n0 + 20 ≤ L.NN) (hs0 : s0 + 64 ≤ L.NS) (ha0 : a0 + 32 ≤ L.NA) (hdv : dv < L.NN) (hone : one < L.NN)
    (hdvb : dv < n0 ∨ n0 + 20 ≤ dv) (honeb : one < n0 ∨ n0 + 20 ≤ one) (hd : σ.nat dv = d) (h1 : σ.nat one = 1)
    (hmuv : muv < L.NA) (hAv : Av < L.NA) (hmub : muv < a0 ∨ a0 + 32 ≤ muv) (hAb : Av < a0 ∨ a0 + 32 ≤ Av) (hdd : σ.nat (n0 + 9) = d * d) :
    Runs L w (pgStep L dv one n0 s0 a0 muv Av) σ (kStep d (σ.nat (n0 + 10)))
      (fun σ' =>
        let g : Fin d → ℝ := fun c => w.gs (σ.draws + c)
        let F := piTilde (pgBodySet w.K (σ.vec muv) (σ.mat Av) (σ.sc (s0 + 42))) (σ.sc (s0 + 19)) (σ.nat (n0 + 10))
          (WithLp.toLp 2 (σ.mat (a0 + 1) *ᵥ g + σ.vec a0))
        let B := (gjRun (σ.mat (a0 + 1)) d).2
        let G := vecMulVec g g - 1
        WithLp.toLp 2 (σ'.vec a0) =
            ballClip (σ.sc (s0 + 23)) (WithLp.toLp 2 (σ.vec a0 + σ.sc (s0 + 30) • (F • (B *ᵥ g)))) ∧
          σ'.mat (a0 + 1) = cfc (Spec.fn .clamp (σ.sc (s0 + 21)) (σ.sc (s0 + 22)))
            (symPart (σ.mat (a0 + 1) + σ.sc (s0 + 30) • ((F / 2) • (B * G + (B * G)ᵀ) + σ.sc (s0 + 32) • B))) ∧
          σ'.vec (a0 + 2) = σ.vec (a0 + 2) + σ.vec a0 ∧ σ'.mat (a0 + 3) = σ.mat (a0 + 3) + σ.mat (a0 + 1) ∧
          σ'.draws = σ.draws + d ∧
          Env.Frame σ { σ' with draws := σ.draws } (pgTmpN n0) (pgTmpS s0 ++ [s0 + 31, s0 + 34, s0 + 35, s0 + 36])
            [a0, a0 + 1, a0 + 2, a0 + 3, a0 + 4, a0 + 5, a0 + 6, a0 + 7, a0 + 8, a0 + 9, a0 + 10, a0 + 11, a0 + 12,
              a0 + 13, a0 + 14]) := by
  have nd : dv ∉ [n0, n0 + 1, n0 + 2, n0 + 3, n0 + 4, n0 + 5, n0 + 6, n0 + 7, n0 + 8] := by simp; omega
  have no : one ∉ [n0, n0 + 1, n0 + 2, n0 + 3, n0 + 4, n0 + 5, n0 + 6, n0 + 7, n0 + 8] := by simp; omega
  unfold pgStep kStep
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
  refine runs_seq (runs_mono (runs_pgGauge hP (xm := a0) (xT := a0 + 1) σ4 hn0 hs0 ha0 hdv hone hdvb honeb d4 o4 hmuv
    hAv hmub hAb (by omega) (by omega) (by simp) (by simp)) (by rw [j4]) (fun σ' h => h)) fun σ5 h5 => ?_
  obtain ⟨e518, F5⟩ := h5
  have d5 : σ5.nat dv = d := (F5.1 _ (by simp; omega)).trans d4
  have o5 : σ5.nat one = 1 := (F5.1 _ (by simp; omega)).trans o4
  have dd5 : σ5.nat (n0 + 9) = d * d := (F5.1 _ (by simp)).trans ((F04.1 _ (by simp)).trans hdd)
  refine runs_seq (runs_pgVinv hP σ5 hn0 hs0 ha0 hdv hone hdvb honeb d5 o5 dd5) fun σ6 h6 => ?_
  obtain ⟨m6, v6, F6⟩ := h6
  have d6 : σ6.nat dv = d := (F6.1 _ (by simp; omega)).trans d5
  have o6 : σ6.nat one = 1 := (F6.1 _ (by simp; omega)).trans o5
  have dd6 : σ6.nat (n0 + 9) = d * d := (F6.1 _ (by simp)).trans dd5
  refine runs_seq (runs_pgVmat hP σ6 hn0 hs0 ha0 hdv hone hdvb honeb d6 o6 dd6) fun σ7 h7 => ?_
  obtain ⟨m7, F7⟩ := h7
  have d7 : σ7.nat dv = d := (F7.1 _ (by simp; omega)).trans d6
  have o7 : σ7.nat one = 1 := (F7.1 _ (by simp; omega)).trans o6
  have dd7 : σ7.nat (n0 + 9) = d * d := (F7.1 _ (by simp)).trans dd6
  refine runs_mono (hP.upd σ7 hn0 hs0 ha0 hdv hone hdvb honeb d7 o7 dd7) le_rfl fun σ8 h8 => ?_
  obtain ⟨v8, m8, F8⟩ := h8
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
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [v8, s47 23 (by omega) (by omega) (by omega), s47 30 (by omega) (by omega) (by omega), Env.vec_of_arr a7,
      Env.vec_of_arr (F7.2.2.1 _ (by simp)), v6, hF, Env.mat_of_arr a51, a54]
  · rw [m8, s47 21 (by omega) (by omega) (by omega), s47 22 (by omega) (by omega) (by omega),
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

set_option maxHeartbeats 1000000 in
theorem runs_pgSampleM (hP : PgParts) {d : ℕ} {L : Layout} {w : World d} {dv one n0 s0 a0 muv Av : ℕ}
    (σ : Env d) (hn0 : n0 + 20 ≤ L.NN) (hs0 : s0 + 64 ≤ L.NS) (ha0 : a0 + 32 ≤ L.NA) (hdv : dv < L.NN) (hone : one < L.NN)
    (hdvb : dv < n0 ∨ n0 + 20 ≤ dv) (honeb : one < n0 ∨ n0 + 20 ≤ one) (hd : σ.nat dv = d) (h1 : σ.nat one = 1)
    (hmuv : muv < L.NA) (hAv : Av < L.NA) (hmub : muv < a0 ∨ a0 + 32 ≤ muv) (hAb : Av < a0 ∨ a0 + 32 ≤ Av) (hdd : σ.nat (n0 + 9) = d * d) :
    Runs L w (pgSample L dv one n0 s0 a0 muv Av) σ (kSample d (σ.nat (n0 + 10)))
      (fun σ' =>
        let g : Fin d → ℝ := fun c => w.gs (σ.draws + c)
        let F := piTilde (pgBodySet w.K (σ.vec muv) (σ.mat Av) (σ.sc (s0 + 42))) (σ.sc (s0 + 19)) (σ.nat (n0 + 10))
          (WithLp.toLp 2 (σ.mat (a0 + 3) *ᵥ g + σ.vec (a0 + 2)))
        σ'.sc (s0 + 37) = σ.sc (s0 + 37) + F ∧ σ'.vec (a0 + 15) = σ.vec (a0 + 15) + F • g ∧
          σ'.mat (a0 + 16) = σ.mat (a0 + 16) + F • (vecMulVec g g - 1) ∧ σ'.draws = σ.draws + d ∧
          Env.Frame σ { σ' with draws := σ.draws } (pgTmpN n0) (pgTmpS s0 ++ [s0 + 36, s0 + 37])
            [a0 + 4, a0 + 5, a0 + 6, a0 + 7, a0 + 11, a0 + 15, a0 + 16]) := by
  unfold pgSample kSample
  refine runs_seq (runs_vgauss (y := a0 + 4) (t := s0 + 8) σ hdv hone (by omega) (by omega) (by omega) (by omega)
    (by omega) hd h1) fun σ1 h1' => ?_
  obtain ⟨v1, dr1, n1, s1, a1, r1, p1, -⟩ := h1'
  have F01 : Env.Frame σ { σ1 with draws := σ.draws } [n0] [s0 + 8] [a0 + 4] :=
    ⟨fun j hj => n1 j (by simpa using hj), fun z hz => s1 z (by simpa using hz), fun b hb => a1 b (by simpa using hb),
      rfl, r1, p1⟩
  have n01 : ∀ i ∉ [n0], σ1.nat i = σ.nat i := F01.1
  have s01 : ∀ x ∉ [s0 + 8], σ1.sc x = σ.sc x := F01.2.1
  have a01 : ∀ a ∉ [a0 + 4], σ1.arr a = σ.arr a := F01.2.2.1
  have d1 : σ1.nat dv = d := (n01 _ (by simp; omega)).trans hd
  have o1 : σ1.nat one = 1 := (n01 _ (by simp; omega)).trans h1
  have j1 : σ1.nat (n0 + 10) = σ.nat (n0 + 10) := n01 _ (by simp)
  refine runs_seq (runs_mono (runs_pgGauge hP (xm := a0 + 2) (xT := a0 + 3) σ1 hn0 hs0 ha0 hdv hone hdvb honeb d1 o1
    hmuv hAv hmub hAb (by omega) (by omega) (by simp) (by simp)) (by rw [j1]) (fun σ' h => h)) fun σ2 h2 => ?_
  obtain ⟨e218, F2⟩ := h2
  have hF : σ2.sc (s0 + 18) = piTilde (pgBodySet w.K (σ.vec muv) (σ.mat Av) (σ.sc (s0 + 42))) (σ.sc (s0 + 19))
      (σ.nat (n0 + 10)) (WithLp.toLp 2 (σ.mat (a0 + 3) *ᵥ (fun c : Fin d => w.gs (σ.draws + c)) + σ.vec (a0 + 2))) := by
    rw [e218, Env.vec_of_arr (a01 muv (by simp; omega)), Env.mat_of_arr (a01 Av (by simp; omega)),
      s01 (s0 + 42) (by simp), s01 (s0 + 19) (by simp), j1, Env.mat_of_arr (a01 (a0 + 3) (by simp)),
      Env.vec_of_arr (a01 (a0 + 2) (by simp)), v1]
  refine runs_seq_eq (runs_sop2 (L := L) (w := w) (σ := σ2) (x := s0 + 37) (by omega) (by omega) (by omega) .add) ?_
  set σ3 := σ2.setSc (s0 + 37) (Op2.add.eval (σ2.sc (s0 + 37)) (σ2.sc (s0 + 18))) with hσ3
  have d3 : σ3.nat dv = d := (F2.1 _ (by simp; omega)).trans d1
  have o3 : σ3.nat one = 1 := (F2.1 _ (by simp; omega)).trans o1
  refine runs_seq (runs_vaxpy (y := a0 + 15) (x := a0 + 4) (α := s0 + 18) (t1 := s0 + 8) (t2 := s0 + 9) σ3 hdv hone
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) d3 o3) fun σ4 h4 => ?_
  obtain ⟨v4, F4, -⟩ := h4
  have d4 : σ4.nat dv = d := (F4.1 _ (by simp; omega)).trans d3
  have o4 : σ4.nat one = 1 := (F4.1 _ (by simp; omega)).trans o3
  have dd4 : σ4.nat (n0 + 9) = d * d := by
    rw [F4.1 _ (by simp), show σ3.nat = σ2.nat from rfl, F2.1 _ (by simp), n01 _ (by simp)]; exact hdd
  refine runs_seq (hP.ggcode σ4 hn0 hs0 ha0 hdv hone hdvb honeb d4 o4 dd4) fun σ5 h5 => ?_
  obtain ⟨m5, e5s0, e52, F5⟩ := h5
  have d5 : σ5.nat dv = d := (F5.1 _ (by simp; omega)).trans d4
  have o5 : σ5.nat one = 1 := (F5.1 _ (by simp; omega)).trans o4
  have dd5 : σ5.nat (n0 + 9) = d * d := (F5.1 _ (by simp)).trans dd4
  refine runs_mono (runs_mlin (C := a0 + 16) (A := a0 + 16) (B := a0 + 11) (α := s0 + 2) (β := s0 + 18)
    (t1 := s0 + 8) (t2 := s0 + 9) σ5 (by omega) hone (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    dd5 o5) le_rfl fun σ6 h6 => ?_
  obtain ⟨m6, F6, -⟩ := h6
  have e3v : ∀ a, σ3.vec a = σ2.vec a := fun _ => rfl
  have e3m : ∀ a, σ3.mat a = σ2.mat a := fun _ => rfl
  have e318 : σ3.sc (s0 + 18) = σ2.sc (s0 + 18) := by rw [hσ3, Env.setSc_sc, if_neg (by omega)]
  have g4 : σ4.vec (a0 + 4) = fun c : Fin d => w.gs (σ.draws + c) := by
    rw [Env.vec_of_arr (F4.2.2.1 _ (by simp)), e3v, Env.vec_of_arr (F2.2.2.1 _ (by simp)), v1]
  have e518 : σ5.sc (s0 + 18) = σ2.sc (s0 + 18) := by
    rw [F5.2.1 _ (by simp), F4.2.1 _ (by simp), hσ3, Env.setSc_sc, if_neg (by omega)]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [F6.2.1 _ (by simp), F5.2.1 _ (by simp), F4.2.1 _ (by simp), hσ3, Env.setSc_sc, if_pos rfl, hF,
      F2.2.1 _ (by simp [pgTmpS]), s01 _ (by simp)]
    rfl
  · rw [Env.vec_of_arr (F6.2.2.1 _ (by simp)), Env.vec_of_arr (F5.2.2.1 _ (by simp)), v4, e3v, e3v, e318, hF,
      Env.vec_of_arr (F2.2.2.1 (a0 + 15) (by simp)), Env.vec_of_arr (a01 (a0 + 15) (by simp)),
      Env.vec_of_arr (F2.2.2.1 (a0 + 4) (by simp)), v1]
  · rw [m6, e52, one_smul, m5, g4, e518, hF, Env.mat_of_arr (F5.2.2.1 (a0 + 16) (by simp)),
      Env.mat_of_arr (F4.2.2.1 (a0 + 16) (by simp)), e3m, Env.mat_of_arr (F2.2.2.1 (a0 + 16) (by simp)),
      Env.mat_of_arr (a01 (a0 + 16) (by simp))]
  · rw [F6.2.2.2.1, F5.2.2.2.1, F4.2.2.2.1, show σ3.draws = σ2.draws from rfl, F2.2.2.2.1, dr1]
  · have F16 : Env.Frame σ1 σ6 (pgTmpN n0) (pgTmpS s0 ++ [s0 + 36, s0 + 37])
        [a0 + 4, a0 + 5, a0 + 6, a0 + 7, a0 + 11, a0 + 15, a0 + 16] :=
      Env.Frame.trans (Env.Frame.mono F2 (by simp [pgTmpN]) (by simp [pgTmpS]) (by simp))
        (Env.Frame.trans (Env.Frame.setSc (Env.Frame.refl σ2 (pgTmpN n0) (pgTmpS s0 ++ [s0 + 36, s0 + 37])
            [a0 + 4, a0 + 5, a0 + 6, a0 + 7, a0 + 11, a0 + 15, a0 + 16]) (by simp) _)
          (Env.Frame.trans (Env.Frame.mono F4 (by simp [pgTmpN]) (by simp [pgTmpS]) (by simp))
            (Env.Frame.trans (Env.Frame.mono F5 (by simp [pgTmpN]) (by simp [pgTmpS]) (by simp))
              (Env.Frame.mono F6 (by simp [pgTmpN]) (by simp [pgTmpS]) (by simp)))))
    exact frameD_trans (Env.Frame.mono F01 (by simp [pgTmpN]) (by simp [pgTmpS]) (by simp)) (frameD_of_frame F16)

/-- The leaves of a stage from the rules of their parts and the matrix product of MachMat.lean. -/
theorem PgParts.leaves (hP : PgParts) : PgLeaves where
  stepM := runs_pgStepM hP
  sampleM := runs_pgSampleM hP
  verdNorm := hP.verdNorm
  verdC12 := hP.verdC12
  verdC3 := hP.verdC3
  mmul := runs_mmul

end AdversarialBco.Poly.PG
