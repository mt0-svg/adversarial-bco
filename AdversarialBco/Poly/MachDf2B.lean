/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.MachDf2
public import AdversarialBco.Poly.MachProg
public import AdversarialBco.Poly.MachPG
public import AdversarialBco.Poly.MachSetup

@[expose] public section

/-!
# Part B of a round of DF2-O in VL, and the whole program

The rules of the stages of part B of a round (`phiTest`, `nx3` to `nx8`, `nxCommit`, `stInit`, `yCode`), their
compositions (`runs_nxC6` down to `runs_nextCode`, then `runs_df2B`), the round invariants `RndI`, `RndJ` with the
rules `runs_rndA`, `runs_rndB`, the code before the rounds (`preCode`: parameters, PG, first mode), and the program
`df2Prog` with `df2Prog_spec`: its cost bounds and its plays are those of DF2-O, given the rules of PG
(`PG.PgLeaves`) and of the two calls of AP in each round (`ApRules`).
-/

namespace AdversarialBco.Poly.Mach.VL

open AdversarialBco AdversarialBco.RealRAM AdversarialBco.Poly Matrix

variable {d : ℕ} {w : World d}

open Classical in
theorem runs_phiTest {Pa ba kv thr : ℕ} (P : Prop) (σ : Env d)
    (hPa : Pa < 96) (hba : ba < 96) (hkv : kv < 320) (hthr : thr < 320) (hPa95 : Pa ≠ 95) (hba95 : ba ≠ 95)
    (hkvL : kv ∉ [113, 114, 115, 116, 117, 118, 119])
    (hthrL : thr ∉ [113, 114, 115, 116, 117, 118, 119]) (hd : σ.nat 0 = d) (h1 : σ.nat 2 = 1) (h19 : σ.sc 19 = 1 / 2)
    (h40 : σ.sc 40 = if P then 1 else 0) :
    Runs df2L w (phiTest Pa ba kv thr) σ (d * (d * 10 + 9) + d * 18 + 18) (fun σ' =>
      σ'.sc 116 = (if P ∧ df2Phi (σ.mat Pa) (σ.vec ba) (σ.sc kv) (σ.vec 93) ≤ σ.sc thr then 1 else 0) ∧
        Env.Frame σ σ' [3, 4, 5] [113, 114, 115, 116, 117, 118, 119] [95]) := by
  have hkv113 : kv ≠ 113 := fun e => hkvL (by simp [e])
  have hthr113 : thr ≠ 113 := fun e => hthrL (by simp [e])
  let l : List SI := [SI.op2 .mul 113 114 19, SI.op2 .sub 113 113 115, SI.op2 .add 113 113 kv]
  have hl : l.all (SI.ok df2L) = true := by
    simp only [l, List.all_cons, List.all_nil, SI.ok, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨by decide, by decide, ⟨by decide, by decide, hkv⟩⟩
  refine runs_mono (K := (d * (d * 10 + 9) + 4) + ((d * 9 + 4) + ((d * 9 + 4) + (sCost l + 3))))
    (runs_seq (runs_matvec (L := df2L) (w := w) σ (dv := 0) (one := 2) (i := 3) (j := 4) (k := 5) (y := 95)
      (A := Pa) (x := 93) (s := 117) (t1 := 118) (t2 := 119) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) hPa (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (Ne.symm hPa95) (by decide) (by decide) (by decide) hd h1) (fun σ1 h1' => ?_))
    (by simp only [l, sCost, List.map, SI.cost, List.sum_cons, List.sum_nil]; ring_nf; omega) (fun σ' h => h)
  obtain ⟨v1, F1, -⟩ := h1'
  refine runs_seq (runs_vdot (L := df2L) (w := w) σ1 (dv := 0) (one := 2) (i := 3) (r := 114) (x := 93) (y := 95)
    (t1 := 118) (t2 := 119) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by rw [F1.1 0 (by decide), hd])
    (by rw [F1.1 2 (by decide), h1])) (fun σ2 h2 => ?_)
  obtain ⟨s114, F2⟩ := h2
  have F12 : Env.Frame σ σ2 [3, 4, 5] [114, 117, 118, 119] [95] :=
    Env.Frame.trans (Env.Frame.mono F1 (by decide) (by decide) (by decide))
      (Env.Frame.mono F2 (by decide) (by decide) (by decide))
  refine runs_seq (runs_vdot (L := df2L) (w := w) σ2 (dv := 0) (one := 2) (i := 3) (r := 115) (x := ba) (y := 93)
    (t1 := 118) (t2 := 119) (by decide) (by decide) (by decide) (by decide) hba (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by rw [F12.1 0 (by decide), hd])
    (by rw [F12.1 2 (by decide), h1])) (fun σ3 h3 => ?_)
  obtain ⟨s115, F3⟩ := h3
  have F13 : Env.Frame σ σ3 [3, 4, 5] [113, 114, 115, 116, 117, 118, 119] [95] :=
    Env.Frame.trans (Env.Frame.mono F12 (by decide) (by decide) (by decide))
      (Env.Frame.mono F3 (by decide) (by decide) (by decide))
  refine runs_seq (runs_sprog (L := df2L) (w := w) l hl σ3) (fun σ4 e4 => ?_)
  have hba95' : ba ∉ [95] := by simpa using hba95
  have a114 : σ3.sc 114 = σ.vec 93 ⬝ᵥ (σ.mat Pa *ᵥ σ.vec 93) := by
    rw [F3.2.1 114 (by decide), s114, v1, Env.Frame.vec_eq F1 (a := 93) (by decide)]
  have a115 : σ3.sc 115 = σ.vec ba ⬝ᵥ σ.vec 93 := by
    rw [s115, Env.Frame.vec_eq F12 (a := ba) hba95', Env.Frame.vec_eq F12 (a := 93) (by decide)]
  have a113 : σ4.sc 113 = df2Phi (σ.mat Pa) (σ.vec ba) (σ.sc kv) (σ.vec 93) := by
    rw [e4]
    simp only [l, sEval, List.foldl, SI.step, SI.dst, SI.val, Op2.eval, Function.update_apply, hkv113,
      show (115 : ℕ) ≠ 113 by decide, ↓reduceIte]
    rw [a114, a115, F13.2.1 kv hkvL, F13.2.1 19 (by decide), h19]
    unfold df2Phi; ring
  have hthr4 : σ4.sc thr = σ.sc thr := by
    rw [e4]; show sEval σ3.nat l σ3.sc thr = _
    rw [sEval_frame σ3.nat l σ3.sc (by simpa [l, SI.dst] using hthr113), F13.2.1 thr hthrL]
  have h40' : σ4.sc 40 = σ.sc 40 := by
    rw [e4]; show sEval σ3.nat l σ3.sc 40 = _
    rw [sEval_frame σ3.nat l σ3.sc (by simp [l, SI.dst]), F13.2.1 40 (by decide)]
  have F4 : Env.Frame σ σ4 [3, 4, 5] [113, 114, 115, 116, 117, 118, 119] [95] := by
    subst e4
    refine ⟨fun i hi => F13.1 i hi, fun x hx => ?_, fun a ha => F13.2.2.1 a ha, F13.2.2.2.1, F13.2.2.2.2.1,
      F13.2.2.2.2.2⟩
    have hx113 : x ≠ 113 := fun h => hx (by simp [h])
    show sEval σ3.nat l σ3.sc x = _
    rw [sEval_frame σ3.nat l σ3.sc (by simpa [l, SI.dst] using hx113), F13.2.1 x hx]
  by_cases hc : σ4.sc thr < σ4.sc 113
  · refine runs_mono (runs_ifS_t (L := df2L) (w := w) hthr (by decide) hc (runs_sconst (σ := σ4) (by decide) 0))
      (by omega) (fun σ' e => ?_)
    subst e
    refine ⟨?_, Env.Frame.setSc F4 (by decide) _⟩
    rw [hthr4, a113] at hc
    have hn : ¬ (P ∧ df2Phi (σ.mat Pa) (σ.vec ba) (σ.sc kv) (σ.vec 93) ≤ σ.sc thr) :=
      fun h => absurd h.2 (not_le.2 hc)
    simp [hn]
  · refine runs_mono (runs_ifS_f (L := df2L) (w := w) hthr (by decide) hc (runs_smov (σ := σ4) (x := 116) (y := 40)
      (by decide) (by decide))) le_rfl (fun σ' e => ?_)
    subst e
    refine ⟨?_, Env.Frame.setSc F4 (by decide) _⟩
    rw [hthr4, a113, not_lt] at hc
    simp only [Env.setSc_sc, ↓reduceIte, h40', h40, hc, and_true]

open Classical in
/-- The rule of `memRm`: the membership code of the region `R⁻` of the first call of AP. -/
theorem runs_memRm (p : Df2OPar) (Ps : PgSp d) (st : Df2St d) :
    AP.MemRule df2L w memRm apV1 (nxRm p (df2Keps w.K Ps p.R p.eps) st) (Iq1 p Ps st) (kMemR d) [3, 4, 5] memS
      [12, 13, 95] := by
  intro σ hI hd h1
  dsimp only [apV1] at hd h1 ⊢
  have hI' := hI
  obtain ⟨hP, h17, h110, h19, h21, h23, h3, h6, h24, h111⟩ := hI'
  refine runs_seq (runs_memKeps (w := w) Ps σ hd h1 hP) (fun σ1 h1' => ?_)
  obtain ⟨o1, F1⟩ := h1'
  have hK : σ1.sc 40 = if σ.vec 93 ∈ df2Keps w.K Ps p.R p.eps then 1 else 0 := by rw [o1, h110, h17]; rfl
  have v93 : σ1.vec 93 = σ.vec 93 := Env.Frame.vec_eq F1 (by decide)
  have hd1 : σ1.nat 0 = d := by rw [F1.1 0 (by decide), hd]
  have h11 : σ1.nat 2 = 1 := by rw [F1.1 2 (by decide), h1]
  have hI1 : Iq1 p Ps st σ1 := hI.frame F1 (by decide) (by decide)
  cases hf : st.first
  · have hc : ¬ σ1.sc 21 < σ1.sc 23 := by
      rw [F1.2.1 21 (by decide), F1.2.1 23 (by decide), h21, h23, hf]; simp
    refine runs_mono (runs_ifS_f (by decide) (by decide) hc (runs_phiTest (w := w) _ σ1 (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hd1 h11
      (by rw [F1.2.1 19 (by decide), h19]) hK)) (by omega) (fun σ2 h2 => ?_)
    obtain ⟨o2, F2⟩ := h2
    refine ⟨?_, Env.Frame.trans (Env.Frame.mono F1 (by simp) (by intro x hx; simp [memS] at hx ⊢; omega) (by simp))
      (Env.Frame.mono F2 (by simp) (by intro x hx; simp [memS] at hx ⊢; omega) (by simp)),
      hI1.frame F2 (by decide) (by decide)⟩
    rw [o2, v93, Env.Frame.mat_eq F1 (by decide), Env.Frame.vec_eq F1 (by decide), F1.2.1 24 (by decide),
      F1.2.1 111 (by decide), h3, h6, h24, h111]
    simp only [nxRm, hf, Bool.false_eq_true, ite_false]
    rfl
  · have hc : σ1.sc 21 < σ1.sc 23 := by
      rw [F1.2.1 21 (by decide), F1.2.1 23 (by decide), h21, h23, hf]; simp
    refine runs_mono (runs_ifS_t (by decide) (by decide) hc (runs_smov (L := df2L) (w := w) (σ := σ1) (x := 116)
      (y := 40) (by decide) (by decide))) (by omega) (fun σ2 e2 => ?_)
    subst e2
    refine ⟨?_, Env.Frame.trans (Env.Frame.mono F1 (by simp) (by intro x hx; simp [memS] at hx ⊢; omega) (by simp))
      (Env.Frame.setSc (Env.Frame.refl σ1 [3, 4, 5] memS [12, 13, 95]) (by decide) _),
      hI1.frame (Env.Frame.setSc (Env.Frame.refl σ1 [] [116] []) (by simp) _) (by decide) (by decide)⟩
    simp only [Env.setSc_sc, nxRm, hf, ite_true]
    exact hK

open Classical in
/-- The rule of `memRp`: the membership code of the region `R_{t+1}` of the second call of AP. -/
theorem runs_memRp (p : Df2OPar) (Ps : PgSp d) (F : NxF d) :
    AP.MemRule df2L w memRp apV2 {y | y ∈ df2Keps w.K Ps p.R p.eps ∧ df2Phi F.P F.b F.k y ≤ p.c1 * p.rho}
      (Iq2 p Ps F) (kMemR d) [3, 4, 5] memS [12, 13, 95] := by
  intro σ hI hd h1
  dsimp only [apV2] at hd h1 ⊢
  have hI' := hI
  obtain ⟨hP, h17, h110, h19, h80, h83, h81, h112⟩ := hI'
  refine runs_mono (K := kMemKeps d + (d * (d * 10 + 9) + d * 18 + 18))
    (runs_seq (runs_memKeps (w := w) Ps σ hd h1 hP) (fun σ1 h1' => ?_)) (by unfold kMemR; omega)
    (fun σ' h => h)
  obtain ⟨o1, F1⟩ := h1'
  have hK : σ1.sc 40 = if σ.vec 93 ∈ df2Keps w.K Ps p.R p.eps then 1 else 0 := by rw [o1, h110, h17]; rfl
  have hd1 : σ1.nat 0 = d := by rw [F1.1 0 (by decide), hd]
  have h11 : σ1.nat 2 = 1 := by rw [F1.1 2 (by decide), h1]
  refine runs_mono (runs_phiTest (w := w) _ σ1 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) hd1 h11 (by rw [F1.2.1 19 (by decide), h19]) hK) le_rfl
    (fun σ2 h2 => ?_)
  obtain ⟨o2, F2⟩ := h2
  refine ⟨?_, Env.Frame.trans (Env.Frame.mono F1 (by simp) (by intro x hx; simp [memS] at hx ⊢; omega) (by simp))
    (Env.Frame.mono F2 (by simp) (by intro x hx; simp [memS] at hx ⊢; omega) (by simp)),
    (hI.frame F1 (by decide) (by decide)).frame F2 (by decide) (by decide)⟩
  rw [o2, Env.Frame.vec_eq F1 (by decide), Env.Frame.mat_eq F1 (by decide), Env.Frame.vec_eq F1 (by decide),
    F1.2.1 81 (by decide), F1.2.1 112 (by decide), h80, h83, h81, h112]
  congr 1


/-! stubs (scratch only) -/

theorem runs_nx3 (σ : Env d) (hd : σ.nat 0 = d)
    (h1 : σ.nat 2 = 1) :
    Runs df2L w nx3 σ (d * 16 + 12) (fun σ' =>
      σ'.sc 85 = (σ.mat 80).trace ∧ σ'.sc 86 = (σ.mat 81).trace ∧ σ'.sc 87 = (d : ℝ) / σ.sc 4 ∧
        Env.Frame σ σ' [3, 5] [37, 85, 86, 87] []) := by
  have h_mtrace1 := runs_mtrace (L := df2L) (w := w) σ (dv := 0) (one := 2) (i := 3) (k := 5) (r := 85)
    (A := 80) (t := 37)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hd h1
  refine runs_mono (K := (d * 8 + 5) + ((d * 8 + 5) + 2))
    (runs_seq h_mtrace1 (fun σ1 h1' => ?_))
    (by ring_nf; omega) (fun σ' h => h)
  obtain ⟨e85, F1⟩ := h1'
  have hd1 : σ1.nat 0 = d := by rw [F1.1 0 (by decide), hd]
  have h11 : σ1.nat 2 = 1 := by rw [F1.1 2 (by decide), h1]
  have h_mtrace2 := runs_mtrace (L := df2L) (w := w) σ1 (dv := 0) (one := 2) (i := 3) (k := 5) (r := 86)
    (A := 81) (t := 37)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hd1 h11
  refine runs_seq h_mtrace2 (fun σ2 h2 => ?_)
  obtain ⟨e86, F2⟩ := h2
  have h_sprog := runs_sprog (L := df2L) (w := w) [SI.cast 87 0, SI.op2 .div 87 87 4] (by decide) σ2
  set σ3 : Env d := { σ2 with sc := sEval σ2.nat [SI.cast 87 0, SI.op2 .div 87 87 4] σ2.sc } with hσ3
  have hF3 : Env.Frame σ2 σ3 [] [87] [] := by
    refine ⟨fun i hi => rfl, fun x hx => ?_, fun a ha => rfl, rfl, rfl, rfl⟩
    have hx' : x ≠ 87 := by simpa using hx
    dsimp [σ3]
    simp only [sEval, List.foldl, SI.step, SI.dst, SI.val, Function.update_apply]
    simp [hx']
  have h0 : σ2.nat 0 = d := by
    rw [F2.1 0 (by decide), F1.1 0 (by decide), hd]
  have h4sc : σ2.sc 4 = σ.sc 4 := by
    rw [F2.2.1 4 (by decide), F1.2.1 4 (by decide)]
  have e87 : σ3.sc 87 = (d : ℝ) / σ.sc 4 := by
    dsimp [σ3]
    simp only [sEval, List.foldl, SI.step, SI.dst, SI.val, Function.update_apply, Op2.eval]
    have h4ne87 : (4 : ℕ) ≠ 87 := by decide
    simp [h0, h4sc, h4ne87]
  have e85' : σ3.sc 85 = (σ.mat 80).trace := by
    dsimp [σ3]
    simp only [sEval, List.foldl, SI.step, SI.dst, SI.val, Function.update_apply]
    have h85ne87 : (85 : ℕ) ≠ 87 := by decide
    simp [h85ne87]
    rw [F2.2.1 85 (by decide), e85]
  have e86' : σ3.sc 86 = (σ.mat 81).trace := by
    dsimp [σ3]
    simp only [sEval, List.foldl, SI.step, SI.dst, SI.val, Function.update_apply]
    have h86ne87 : (86 : ℕ) ≠ 87 := by decide
    simp [h86ne87]
    have hmat : σ1.mat 81 = σ.mat 81 := by
      have harr : σ1.arr 81 = σ.arr 81 := F1.2.2.1 81 (by decide)
      ext i j; simp [Env.mat, harr]
    rw [e86, hmat]
  have hF : Env.Frame σ σ3 [3, 5] [37, 85, 86, 87] [] :=
    Env.Frame.trans (Env.Frame.mono F1 (by simp) (by simp) (by simp)) (Env.Frame.trans
      (Env.Frame.mono F2 (by simp) (by simp) (by simp)) (Env.Frame.mono hF3 (by simp) (by simp) (by simp)))
  refine runs_mono h_sprog le_rfl (fun σ4 h_eq => ?_)
  subst h_eq
  exact ⟨e85', e86', e87, hF⟩

theorem runs_nx4 (σ : Env d) (hd : σ.nat 0 = d)
    (h1 : σ.nat 2 = 1) (h19 : σ.sc 19 = 1 / 2) (h21 : σ.sc 21 = 0) :
    Runs df2L w nx4 σ (d * (d * 10 + 9) + d * 27 + 20) (fun σ' =>
      σ'.vec 86 = σ.mat 81 *ᵥ (σ.vec 83 - (σ.sc 7 / 2) • σ.vec 84) ∧
        σ'.sc 89 = oNorm (σ.mat 81 *ᵥ (σ.vec 83 - (σ.sc 7 / 2) • σ.vec 84)) ∧
        σ'.sc 90 = σ.sc 17 / σ.sc 4 ^ 3 ∧ Env.Frame σ σ' [3, 4, 5] [35, 37, 38, 88, 89, 90] [85, 86]) := by
  let l1 : List SI := [SI.op2 .mul 88 7 19, SI.op2 .sub 88 21 88]
  let l2 : List SI := [SI.op2 .mul 90 4 4, SI.op2 .mul 90 90 4, SI.op2 .div 90 17 90]
  refine runs_mono (K := (d * 7 + 3) + (sCost l1 + ((d * 11 + 3) + ((d * (d * 10 + 9) + 4) + ((d * 9 + 5) +
      sCost l2)))))
    (runs_seq (runs_vcopy (L := df2L) (w := w) σ (dv := 0) (one := 2) (i := 3) (y := 85) (x := 83) (t := 37)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hd h1)
      (fun σ1 h1' => ?_))
    (by simp only [l1, l2, sCost, List.map, SI.cost, List.sum_cons, List.sum_nil]; ring_nf; omega) (fun σ' h => h)
  obtain ⟨v1, F1, -⟩ := h1'
  refine runs_seq_eq (runs_sprog (L := df2L) (w := w) l1 (by decide) σ1) ?_
  set σ2 : Env d := { σ1 with sc := sEval σ1.nat l1 σ1.sc } with hσ2
  have F2 : Env.Frame σ1 σ2 [] [88] [] := ⟨fun _ _ => rfl, fun x hx => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    simp only [σ2, l1, sEval, List.foldl, SI.step, SI.dst, SI.val]
    simp [hx], fun _ _ => rfl, rfl, rfl, rfl⟩
  have s88 : σ2.sc 88 = -(σ.sc 7 / 2) := by
    simp only [σ2, l1, sEval, List.foldl, SI.step, SI.dst, SI.val, Op2.eval, Function.update_apply]
    simp only [show (21 : ℕ) ≠ 88 by decide, ↓reduceIte]
    rw [F1.2.1 21 (by decide), F1.2.1 7 (by decide), F1.2.1 19 (by decide), h21, h19]; ring
  have hd2 : σ2.nat 0 = d := by show σ1.nat 0 = d; rw [F1.1 0 (by decide), hd]
  have h12 : σ2.nat 2 = 1 := by show σ1.nat 2 = 1; rw [F1.1 2 (by decide), h1]
  refine runs_seq (runs_vaxpy (L := df2L) (w := w) σ2 (dv := 0) (one := 2) (i := 3) (y := 85) (x := 84) (α := 88)
    (t1 := 37) (t2 := 38) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hd2 h12) (fun σ3 h3 => ?_)
  obtain ⟨v3, F3, -⟩ := h3
  have hd3 : σ3.nat 0 = d := by rw [F3.1 0 (by decide), hd2]
  have h13 : σ3.nat 2 = 1 := by rw [F3.1 2 (by decide), h12]
  refine runs_seq (runs_matvec (L := df2L) (w := w) σ3 (dv := 0) (one := 2) (i := 3) (j := 4) (k := 5) (y := 86)
    (A := 81) (x := 85) (s := 35) (t1 := 37) (t2 := 38) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) hd3 h13) (fun σ4 h4 => ?_)
  obtain ⟨v4, F4, -⟩ := h4
  have hd4 : σ4.nat 0 = d := by rw [F4.1 0 (by decide), hd3]
  have h14 : σ4.nat 2 = 1 := by rw [F4.1 2 (by decide), h13]
  have u4 : σ4.vec 86 = σ.mat 81 *ᵥ (σ.vec 83 - (σ.sc 7 / 2) • σ.vec 84) := by
    rw [v4, v3, s88, Env.Frame.mat_eq F3 (a := 81) (by decide), Env.Frame.vec_eq F2 (a := 84) (by decide),
      Env.Frame.vec_eq F2 (a := 85) (by decide), Env.Frame.vec_eq F1 (a := 84) (by decide), v1, neg_smul,
      ← sub_eq_add_neg]
    show σ1.mat 81 *ᵥ _ = _
    rw [Env.Frame.mat_eq F1 (a := 81) (by decide)]
  refine runs_seq (runs_vnorm (L := df2L) (w := w) σ4 (dv := 0) (one := 2) (i := 3) (r := 89) (x := 86) (t1 := 37)
    (t2 := 38) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) hd4 h14) (fun σ5 h5 => ?_)
  obtain ⟨s5, F5⟩ := h5
  refine runs_mono (runs_sprog (L := df2L) (w := w) l2 (by decide) σ5) le_rfl (fun σ' e => ?_)
  subst e
  have F6 : Env.Frame σ5 { σ5 with sc := sEval σ5.nat l2 σ5.sc } [] [90] [] := ⟨fun _ _ => rfl,
    fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      simp only [l2, sEval, List.foldl, SI.step, SI.dst, SI.val]
      simp [hx], fun _ _ => rfl, rfl, rfl, rfl⟩
  have F15 : Env.Frame σ σ5 [3, 4, 5] [35, 37, 38, 88, 89] [85, 86] :=
    Env.Frame.trans (Env.Frame.mono F1 (by decide) (by decide) (by decide)) (Env.Frame.trans
      (Env.Frame.mono F2 (by decide) (by decide) (by decide)) (Env.Frame.trans
        (Env.Frame.mono F3 (by decide) (by decide) (by decide)) (Env.Frame.trans
          (Env.Frame.mono F4 (by decide) (by decide) (by decide)) (Env.Frame.mono F5 (by decide) (by decide)
            (by decide)))))
  refine ⟨by rw [Env.Frame.vec_eq F6 (by decide), Env.Frame.vec_eq F5 (by decide), u4],
    by rw [F6.2.1 89 (by decide), s5, u4]; rfl, ?_,
    Env.Frame.trans (Env.Frame.mono F15 (by decide) (by decide) (by decide))
      (Env.Frame.mono F6 (by decide) (by decide) (by decide))⟩
  simp only [l2, sEval, List.foldl, SI.step, SI.dst, SI.val, Op2.eval, Function.update_apply]
  simp only [show (4 : ℕ) ≠ 90 by decide, show (17 : ℕ) ≠ 90 by decide, ↓reduceIte]
  rw [F15.2.1 4 (by decide), F15.2.1 17 (by decide)]; ring

theorem runs_nx5 (σ : Env d) (h19 : σ.sc 19 = 1 / 2)
    (h27 : σ.sc 27 = 1) :
    Runs df2L w nx5 σ 10 (fun σ' =>
      σ'.sc 110 = 1 / (1 - σ.sc 10) ∧ σ'.sc 111 = (σ.sc 14 - σ.sc 15) * σ.sc 9 ∧ σ'.sc 112 = σ.sc 14 * σ.sc 9 ∧
        σ'.sc 91 = min 1 (σ.sc 13 * σ.sc 9 / 2) ∧ Env.Frame σ σ' [] [91, 110, 111, 112] []) := by
  let l : List SI := [SI.op2 .sub 110 27 10, SI.op2 .div 110 27 110, SI.op2 .sub 111 14 15, SI.op2 .mul 111 111 9,
    SI.op2 .mul 112 14 9,
    SI.op2 .mul 91 13 9, SI.op2 .mul 91 91 19, .smin 91 27 91]
  have hl : l.all (SI.ok df2L) = true := by decide
  have hcost : sCost l = 10 := by
    simp [l, sCost, List.map, SI.cost, List.sum_cons, List.sum_nil]
  have hrun := runs_sprog (L := df2L) (w := w) l hl σ
  have hrun' : Runs df2L w nx5 σ 10 (· = { σ with sc := sEval σ.nat l σ.sc }) := by
    rw [show nx5 = sprog df2L l from rfl]
    exact runs_mono hrun (by rw [hcost]) (fun σ' h => h)
  refine runs_mono hrun' le_rfl (fun σ' h => ?_)
  have h_eq : σ' = { σ with sc := sEval σ.nat l σ.sc } := by simpa using h
  subst h_eq
  set σ1 : Env d := { σ with sc := sEval σ.nat l σ.sc } with hσ1
  have h110 : σ1.sc 110 = 1 / (1 - σ.sc 10) := by
    simp only [σ1, l, sEval, List.foldl, SI.step, SI.dst, SI.val, Function.update_apply, Op2.eval]
    simp [h27]
  have h111 : σ1.sc 111 = (σ.sc 14 - σ.sc 15) * σ.sc 9 := by
    simp only [σ1, l, sEval, List.foldl, SI.step, SI.dst, SI.val, Function.update_apply, Op2.eval]
    simp
  have h112 : σ1.sc 112 = σ.sc 14 * σ.sc 9 := by
    simp only [σ1, l, sEval, List.foldl, SI.step, SI.dst, SI.val, Function.update_apply, Op2.eval]
    simp
  have h91 : σ1.sc 91 = min 1 (σ.sc 13 * σ.sc 9 / 2) := by
    simp only [σ1, l, sEval, List.foldl, SI.step, SI.dst, SI.val, Function.update_apply, Op2.eval]
    simp [h19, h27]
    ring_nf
  have hframe : Env.Frame σ σ1 [] [91, 110, 111, 112] [] := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i hi; simp [σ1]
    · intro x hx
      have hx_dst : x ∉ l.map SI.dst := by
        intro hx_map
        apply hx
        have : l.map SI.dst = [110, 110, 111, 111, 112, 91, 91, 91] := by decide
        rw [this] at hx_map
        simpa [or_comm, or_assoc, or_left_comm] using hx_map
      simp [σ1, sEval_frame σ.nat l σ.sc hx_dst]
    · intro a ha; simp [σ1]
    · simp [σ1]
    · simp [σ1]
    · simp [σ1]
  exact ⟨h110, h111, h112, h91, hframe⟩

theorem runs_nx6 (σ : Env d) (hd : σ.nat 0 = d)
    (h1 : σ.nat 2 = 1) (h19 : σ.sc 19 = 1 / 2) (h21 : σ.sc 21 = 0) :
    Runs df2L w nx6 σ (d * (d * 10 + 9) + d * 27 + 26) (fun σ' =>
      σ'.sc 96 = σ.sc 7 * (σ.sc 84 - σ.vec 84 ⬝ᵥ σ.vec 87) - 2 * df2Phi (σ.mat 80) (σ.vec 83) (σ.sc 81) (σ.vec 87) ∧
        σ'.sc 98 = -(σ.sc 12 * σ.sc 9) ∧
        Env.Frame σ σ' [3, 4, 5] [35, 37, 38, 93, 94, 95, 96, 97, 98, 102] [88]) := by
  let l : List SI := [SI.op2 .sub 96 84 93, SI.op2 .mul 96 7 96, SI.op2 .mul 97 94 19, SI.op2 .sub 97 97 95,
    SI.op2 .add 97 97 81, SI.const 102 2, SI.op2 .mul 97 102 97, SI.op2 .sub 96 96 97, SI.op2 .mul 98 12 9,
    SI.op2 .sub 98 21 98]
  refine runs_mono (K := (d * 9 + 4) + ((d * (d * 10 + 9) + 4) + ((d * 9 + 4) + ((d * 9 + 4) + sCost l))))
    (runs_seq (runs_vdot (L := df2L) (w := w) σ (dv := 0) (one := 2) (i := 3) (r := 93) (x := 84) (y := 87)
      (t1 := 37) (t2 := 38) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hd h1) (fun σ1 h1' => ?_))
    (by simp only [l, sCost, List.map, SI.cost, List.sum_cons, List.sum_nil]; ring_nf; omega) (fun σ' h => h)
  obtain ⟨s93, F1⟩ := h1'
  refine runs_seq (runs_matvec (L := df2L) (w := w) σ1 (dv := 0) (one := 2) (i := 3) (j := 4) (k := 5) (y := 88)
    (A := 80) (x := 87) (s := 35) (t1 := 37) (t2 := 38) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [F1.1 0 (by decide), hd]) (by rw [F1.1 2 (by decide), h1])) (fun σ2 h2 => ?_)
  obtain ⟨v2, F2, -⟩ := h2
  have F12 : Env.Frame σ σ2 [3, 4, 5] [35, 37, 38, 93] [88] :=
    Env.Frame.trans (Env.Frame.mono F1 (by decide) (by decide) (by decide))
      (Env.Frame.mono F2 (by decide) (by decide) (by decide))
  refine runs_seq (runs_vdot (L := df2L) (w := w) σ2 (dv := 0) (one := 2) (i := 3) (r := 94) (x := 87) (y := 88)
    (t1 := 37) (t2 := 38) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by rw [F12.1 0 (by decide), hd])
    (by rw [F12.1 2 (by decide), h1])) (fun σ3 h3 => ?_)
  obtain ⟨s94, F3⟩ := h3
  refine runs_seq (runs_vdot (L := df2L) (w := w) σ3 (dv := 0) (one := 2) (i := 3) (r := 95) (x := 83) (y := 87)
    (t1 := 37) (t2 := 38) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [F3.1 0 (by decide), F12.1 0 (by decide), hd]) (by rw [F3.1 2 (by decide), F12.1 2 (by decide), h1]))
    (fun σ4 h4 => ?_)
  obtain ⟨s95, F4⟩ := h4
  have F14 : Env.Frame σ σ4 [3, 4, 5] [35, 37, 38, 93, 94, 95] [88] :=
    Env.Frame.trans (Env.Frame.mono F12 (by decide) (by decide) (by decide)) (Env.Frame.trans
      (Env.Frame.mono F3 (by decide) (by decide) (by decide)) (Env.Frame.mono F4 (by decide) (by decide)
        (by decide)))
  refine runs_mono (runs_sprog (L := df2L) (w := w) l (by decide) σ4) le_rfl (fun σ' e => ?_)
  subst e
  have F5 : Env.Frame σ4 { σ4 with sc := sEval σ4.nat l σ4.sc } [] [96, 97, 98, 102] [] := ⟨fun _ _ => rfl,
    fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
      simp only [l, sEval, List.foldl, SI.step, SI.dst, SI.val]
      simp [hx.1, hx.2.1, hx.2.2.1, hx.2.2.2], fun _ _ => rfl, rfl, rfl, rfl⟩
  have e : ∀ x ∈ [7, 9, 12, 19, 21, 81, 84], σ4.sc x = σ.sc x := fun x hx => F14.2.1 x (by revert x; decide)
  have a93 : σ4.sc 93 = σ.vec 84 ⬝ᵥ σ.vec 87 := by
    rw [F4.2.1 93 (by decide), F3.2.1 93 (by decide), F2.2.1 93 (by decide), s93]
  have a94 : σ4.sc 94 = σ.vec 87 ⬝ᵥ (σ.mat 80 *ᵥ σ.vec 87) := by
    rw [F4.2.1 94 (by decide), s94, v2, Env.Frame.vec_eq F2 (a := 87) (by decide), Env.Frame.vec_eq F1 (a := 87)
      (by decide), Env.Frame.mat_eq F1 (a := 80) (by decide)]
  have a95 : σ4.sc 95 = σ.vec 83 ⬝ᵥ σ.vec 87 := by
    rw [s95, Env.Frame.vec_eq F3 (a := 83) (by decide), Env.Frame.vec_eq F3 (a := 87) (by decide),
      Env.Frame.vec_eq F12 (a := 83) (by decide), Env.Frame.vec_eq F12 (a := 87) (by decide)]
  refine ⟨?_, ?_, Env.Frame.trans (Env.Frame.mono F14 (by decide) (by decide) (by decide))
    (Env.Frame.mono F5 (by decide) (by decide) (by decide))⟩
  · simp only [l, sEval, List.foldl, SI.step, SI.dst, SI.val, Op2.eval, Function.update_apply]
    simp only [show (7 : ℕ) ≠ 96 by decide, show (94 : ℕ) ≠ 96 by decide, show (19 : ℕ) ≠ 96 by decide,
      show (95 : ℕ) ≠ 97 by decide, show (95 : ℕ) ≠ 96 by decide, show (81 : ℕ) ≠ 97 by decide,
      show (81 : ℕ) ≠ 96 by decide, show (96 : ℕ) ≠ 97 by decide, show (97 : ℕ) ≠ 102 by decide,
      show (96 : ℕ) ≠ 102 by decide, show (96 : ℕ) ≠ 98 by decide, ↓reduceIte]
    rw [e 84 (by simp), e 7 (by simp), e 19 (by simp), e 81 (by simp), a93, a94, a95, h19]
    unfold df2Phi; push_cast; ring
  · simp only [l, sEval, List.foldl, SI.step, SI.dst, SI.val, Op2.eval, Function.update_apply]
    simp only [show (21 : ℕ) ≠ 98 by decide,
      show (12 : ℕ) ≠ 96 by decide, show (12 : ℕ) ≠ 97 by decide, show (12 : ℕ) ≠ 102 by decide,
      show (9 : ℕ) ≠ 96 by decide, show (9 : ℕ) ≠ 97 by decide, show (9 : ℕ) ≠ 102 by decide,
      show (21 : ℕ) ≠ 96 by decide, show (21 : ℕ) ≠ 97 by decide, show (21 : ℕ) ≠ 102 by decide, ↓reduceIte]
    rw [e 12 (by simp), e 9 (by simp), e 21 (by simp), h21]; ring

theorem runs_nx7 (σ : Env d) (hd : σ.nat 0 = d)
    (h1 : σ.nat 2 = 1) (h21 : σ.sc 21 = 0) (h27 : σ.sc 27 = 1) :
    Runs df2L w nx7 σ (d * 44 + 34) (fun σ' =>
      σ'.vec 90 = (1 - σ.sc 18) • σ.vec 87 ∧ σ'.sc 100 = σ.sc 18 * (1 - σ.sc 10) ∧
        σ'.vec 91 = σ.vec 2 - (σ.sc 7 * σ.sc 31 / (σ.sc 64 * σ.sc 67)) • σ.vec 10 ∧
        σ'.sc 103 = oNorm (σ.vec 2 - (σ.sc 7 * σ.sc 31 / (σ.sc 64 * σ.sc 67)) • σ.vec 10) ∧
        σ'.sc 104 = σ.sc 17 + σ.sc 7 * Real.sqrt (16 * d * (σ.nat 1 : ℝ) * σ.sc 5 / σ.sc 4) ∧
        Env.Frame σ σ' [3] [37, 38, 99, 100, 101, 102, 103, 104, 105] [90, 91]) := by
  let l1 : List SI := [SI.op2 .sub 99 27 18, SI.op2 .sub 100 27 10, SI.op2 .mul 100 18 100, SI.op2 .mul 101 7 31,
    SI.op2 .mul 102 64 67, SI.op2 .div 101 101 102, SI.op2 .sub 101 21 101]
  let l2 : List SI := [SI.const 104 16, SI.cast 105 0, SI.op2 .mul 104 104 105, SI.cast 105 1,
    SI.op2 .mul 104 104 105, SI.op2 .mul 104 104 5, SI.op2 .div 104 104 4, SI.op1 .sqrt 104 104,
    SI.op2 .mul 104 7 104, SI.op2 .add 104 17 104]
  refine runs_mono (K := sCost l1 + ((d * 7 + 3) + ((d * 8 + 3) + ((d * 7 + 3) + ((d * 11 + 3) + ((d * 9 + 5) +
      sCost l2))))))
    (runs_seq_eq (runs_sprog (L := df2L) (w := w) l1 (by decide) σ) ?_)
    (by simp only [l1, l2, sCost, List.map, SI.cost, List.sum_cons, List.sum_nil]; omega) (fun σ' h => h)
  set σ1 : Env d := { σ with sc := sEval σ.nat l1 σ.sc } with hσ1
  have F1 : Env.Frame σ σ1 [] [99, 100, 101, 102] [] := ⟨fun _ _ => rfl, fun x hx => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    simp only [σ1, l1, sEval, List.foldl, SI.step, SI.dst, SI.val]
    simp [hx.1, hx.2.1, hx.2.2.1, hx.2.2.2], fun _ _ => rfl, rfl, rfl, rfl⟩
  have s99 : σ1.sc 99 = 1 - σ.sc 18 := by
    simp [σ1, l1, sEval, SI.step, SI.dst, SI.val, Op2.eval, h27]
  have s100 : σ1.sc 100 = σ.sc 18 * (1 - σ.sc 10) := by
    simp [σ1, l1, sEval, SI.step, SI.dst, SI.val, Op2.eval, h27]
  have s101 : σ1.sc 101 = -(σ.sc 7 * σ.sc 31 / (σ.sc 64 * σ.sc 67)) := by
    simp [σ1, l1, sEval, SI.step, SI.dst, SI.val, Op2.eval, h21]
  have hd1 : σ1.nat 0 = d := hd
  have h11 : σ1.nat 2 = 1 := h1
  refine runs_seq (runs_vcopy (L := df2L) (w := w) σ1 (dv := 0) (one := 2) (i := 3) (y := 90) (x := 87) (t := 37)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hd1 h11)
    (fun σ2 h2 => ?_)
  obtain ⟨v2, F2, -⟩ := h2
  have hd2 : σ2.nat 0 = d := by rw [F2.1 0 (by decide), hd1]
  have h12 : σ2.nat 2 = 1 := by rw [F2.1 2 (by decide), h11]
  refine runs_seq (runs_vscale (L := df2L) (w := w) σ2 (dv := 0) (one := 2) (i := 3) (y := 90) (α := 99) (t := 37)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hd2
    h12) (fun σ3 h3 => ?_)
  obtain ⟨v3, F3, -⟩ := h3
  have hd3 : σ3.nat 0 = d := by rw [F3.1 0 (by decide), hd2]
  have h13 : σ3.nat 2 = 1 := by rw [F3.1 2 (by decide), h12]
  refine runs_seq (runs_vcopy (L := df2L) (w := w) σ3 (dv := 0) (one := 2) (i := 3) (y := 91) (x := 2) (t := 37)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hd3 h13)
    (fun σ4 h4 => ?_)
  obtain ⟨v4, F4, -⟩ := h4
  have hd4 : σ4.nat 0 = d := by rw [F4.1 0 (by decide), hd3]
  have h14 : σ4.nat 2 = 1 := by rw [F4.1 2 (by decide), h13]
  refine runs_seq (runs_vaxpy (L := df2L) (w := w) σ4 (dv := 0) (one := 2) (i := 3) (y := 91) (x := 10) (α := 101)
    (t1 := 37) (t2 := 38) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hd4 h14) (fun σ5 h5 => ?_)
  obtain ⟨v5, F5, -⟩ := h5
  have hd5 : σ5.nat 0 = d := by rw [F5.1 0 (by decide), hd4]
  have h15 : σ5.nat 2 = 1 := by rw [F5.1 2 (by decide), h14]
  refine runs_seq (runs_vnorm (L := df2L) (w := w) σ5 (dv := 0) (one := 2) (i := 3) (r := 103) (x := 91) (t1 := 37)
    (t2 := 38) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) hd5 h15) (fun σ6 h6 => ?_)
  obtain ⟨s6, F6⟩ := h6
  have F16 : Env.Frame σ1 σ6 [3] [37, 38, 103] [90, 91] :=
    Env.Frame.trans (Env.Frame.mono F2 (by decide) (by decide) (by decide)) (Env.Frame.trans
      (Env.Frame.mono F3 (by decide) (by decide) (by decide)) (Env.Frame.trans
        (Env.Frame.mono F4 (by decide) (by decide) (by decide)) (Env.Frame.trans
          (Env.Frame.mono F5 (by decide) (by decide) (by decide)) (Env.Frame.mono F6 (by decide) (by decide)
            (by decide)))))
  have v91 : σ6.vec 91 = σ.vec 2 - (σ.sc 7 * σ.sc 31 / (σ.sc 64 * σ.sc 67)) • σ.vec 10 := by
    rw [Env.Frame.vec_eq F6 (by decide), v5, v4, F4.2.1 101 (by decide), F3.2.1 101 (by decide),
      F2.2.1 101 (by decide), s101, Env.Frame.vec_eq F4 (by decide), Env.Frame.vec_eq F3 (by decide),
      Env.Frame.vec_eq F2 (by decide)]
    rw [neg_smul, ← sub_eq_add_neg, Env.Frame.vec_eq F3 (a := 10) (by decide),
      Env.Frame.vec_eq F2 (a := 10) (by decide)]
    rfl
  refine runs_mono (runs_sprog (L := df2L) (w := w) l2 (by decide) σ6) le_rfl (fun σ' e => ?_)
  subst e
  have F6' : Env.Frame σ6 { σ6 with sc := sEval σ6.nat l2 σ6.sc } [] [104, 105] [] := ⟨fun _ _ => rfl,
    fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
      simp only [l2, sEval, List.foldl, SI.step, SI.dst, SI.val]
      simp [hx.1, hx.2], fun _ _ => rfl, rfl, rfl, rfl⟩
  have n61 : σ6.nat 1 = σ.nat 1 := F16.1 1 (by decide)
  have e6 : ∀ x ∈ [4, 5, 7, 17], σ6.sc x = σ.sc x := fun x hx => by
    rw [F16.2.1 x (by revert x; decide), F1.2.1 x (by revert x; decide)]
  refine ⟨by rw [Env.Frame.vec_eq F6' (by decide), Env.Frame.vec_eq F6 (by decide), Env.Frame.vec_eq F5 (by decide),
      Env.Frame.vec_eq F4 (by decide), v3, F2.2.1 99 (by decide), s99, v2]; rfl,
    by rw [F6'.2.1 100 (by decide), F16.2.1 100 (by decide), s100], by rw [Env.Frame.vec_eq F6' (by decide), v91],
    by rw [F6'.2.1 103 (by decide), s6, ← Env.Frame.vec_eq F6 (by decide), v91]; rfl, ?_, ?_⟩
  · simp only [l2, sEval, List.foldl, SI.step, SI.dst, SI.val, Op2.eval, Op1.eval, Function.update_apply]
    simp only [show (104 : ℕ) ≠ 105 by decide, show (5 : ℕ) ≠ 104 by decide,
      show (5 : ℕ) ≠ 105 by decide, show (4 : ℕ) ≠ 104 by decide, show (4 : ℕ) ≠ 105 by decide,
      show (7 : ℕ) ≠ 104 by decide, show (7 : ℕ) ≠ 105 by decide, show (17 : ℕ) ≠ 104 by decide,
      show (17 : ℕ) ≠ 105 by decide, ↓reduceIte]
    rw [e6 4 (by simp), e6 5 (by simp), e6 7 (by simp), e6 17 (by simp), n61,
      show σ6.nat 0 = d by rw [F6.1 0 (by decide), hd5]]
    push_cast; ring_nf
  · exact Env.Frame.trans (Env.Frame.mono F1 (by decide) (by decide) (by decide)) (Env.Frame.trans
      (Env.Frame.mono F16 (by decide) (by decide) (by decide)) (Env.Frame.mono F6' (by decide) (by decide)
        (by decide)))

private theorem nx8_sEval_eq (l : List SI) (n : ℕ → ℕ) (f : ℕ → ℝ) (x : ℕ) (hx : ∀ c ∈ l, c.dst ≠ x) :
    sEval n l f x = f x := by
  induction l generalizing f with
  | nil => rfl
  | cons c cs ih =>
    simp only [sEval, List.foldl, SI.step]
    have hdst := hx c (by simp)
    have hx' : ∀ c' ∈ cs, c'.dst ≠ x := fun c' hc' => hx c' (by simp [hc'])
    have h := ih (Function.update f c.dst (c.val n f)) hx'
    simpa [sEval] using h.trans ((Function.update_of_ne (Ne.symm hdst)) (c.val n f) f)

theorem runs_nx8 (σ : Env d) (h27 : σ.sc 27 = 1) :
    Runs df2L w nx8 σ 13 (fun σ' =>
      σ'.sc 106 = 1 / (16 * (σ.nat 1 : ℝ) ^ 2 * max 1 (4 * σ.sc 17 ^ 2 * σ.sc 85)) ∧
        Env.Frame σ σ' [] [105, 106, 107] []) := by
  set l : List SI := [SI.const 106 4, SI.op2 .mul 107 17 17, SI.op2 .mul 106 106 107, SI.op2 .mul 106 106 85,
    SI.smax 106 27 106,
    SI.const 107 16, SI.cast 105 1, SI.op2 .mul 105 105 105, SI.op2 .mul 107 107 105, SI.op2 .mul 107 107 106,
    SI.op2 .div 106 27 107] with hl
  have hnx8 : nx8 = sprog df2L l := by
    unfold nx8
    simp [l]
  rw [hnx8]
  have hok : l.all (SI.ok df2L) = true := by
    unfold l
    decide
  have hcost : sCost l = 13 := by
    unfold sCost l SI.cost
    decide
  have h := runs_sprog (L := df2L) (w := w) l hok σ
  rw [hcost] at h
  set σ1 : Env d := { σ with sc := sEval σ.nat l σ.sc } with hσ1
  have hσ1_sc106 : σ1.sc 106 = 1 / (16 * (σ.nat 1 : ℝ) ^ 2 * max 1 (4 * σ.sc 17 ^ 2 * σ.sc 85)) := by
    dsimp [σ1, sEval]
    unfold l
    norm_num [List.foldl, SI.step, SI.dst, SI.val, Function.update_apply, Op2.eval, h27]
    ring_nf
  have hdst_all : ∀ c ∈ l, c.dst ∈ [105, 106, 107] := by
    unfold l
    decide
  have hsc_eq : ∀ x, x ∉ [105, 106, 107] → σ1.sc x = σ.sc x := by
    intro x hx
    dsimp [σ1]
    apply nx8_sEval_eq l σ.nat σ.sc x
    intro c hc
    have hdst := hdst_all c hc
    have hx' : x ≠ 105 ∧ x ≠ 106 ∧ x ≠ 107 := by
      simpa using hx
    simp at hdst
    rcases hdst with (h | h | h)
    · rw [h]; exact hx'.1.symm
    · rw [h]; exact hx'.2.1.symm
    · rw [h]; exact hx'.2.2.symm
  have hframe : Env.Frame σ σ1 [] [105, 106, 107] [] := by
    refine ⟨fun i _ => rfl,
            hsc_eq,
            fun a _ => rfl,
            rfl, rfl, rfl⟩
  refine runs_mono h le_rfl (fun σ' h_eq => ?_)
  subst h_eq
  exact ⟨hσ1_sc106, hframe⟩

theorem runs_nxCommit (σ : Env d) (hd : σ.nat 0 = d)
    (h1 : σ.nat 2 = 1) (h9 : σ.nat 9 = d * d) :
    Runs df2L w nxCommit σ (d * d * 21 + d * 28 + 25) (fun σ' =>
      σ'.sc 23 = 0 ∧ σ'.vec 2 = σ.vec 92 ∧ σ'.mat 3 = σ.mat 80 ∧ σ'.mat 4 = σ.mat 81 ∧ σ'.mat 5 = σ.mat 82 ∧
        σ'.vec 6 = σ.vec 83 ∧ σ'.sc 24 = σ.sc 81 ∧ σ'.vec 7 = σ.vec 84 ∧ σ'.sc 25 = σ.sc 84 ∧
        σ'.vec 8 = σ.vec 90 ∧ σ'.sc 26 = σ.sc 100 ∧
        Env.Frame σ σ' [3] [23, 24, 25, 26, 37] [2, 3, 4, 5, 6, 7, 8]) := by
  have FS : ∀ (τ : Env d) (x : ℕ) (v : ℝ), Env.Frame τ (τ.setSc x v) [] [x] [] :=
    fun τ x v => Env.Frame.setSc (Env.Frame.refl τ [] [x] []) (by simp) v
  refine runs_mono (K := 1 + ((d * 7 + 3) + ((d * d * 7 + 3) + ((d * d * 7 + 3) + ((d * d * 7 + 3) +
      ((d * 7 + 3) + (1 + ((d * 7 + 3) + (1 + ((d * 7 + 3) + 1))))))))))
    (runs_seq_eq (runs_sconst (L := df2L) (w := w) (σ := σ) (x := 23) (by decide) 0) ?_)
    (by ring_nf; omega) (fun σ' h => h)
  set σ1 := σ.setSc 23 ((0 : ℚ) : ℝ) with hσ1
  have G1 : Env.Frame σ σ1 [3] [23, 24, 25, 26, 37] [2, 3, 4, 5, 6, 7, 8] :=
    Env.Frame.mono (FS σ 23 _) (by decide) (by decide) (by decide)
  refine runs_seq (runs_vcopy (L := df2L) (w := w) σ1 (dv := 0) (one := 2) (i := 3) (y := 2) (x := 92) (t := 37)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [G1.1 0 (by decide), hd]) (by rw [G1.1 2 (by decide), h1])) (fun σ2 h2 => ?_)
  obtain ⟨v2, F2, -⟩ := h2
  have G2 : Env.Frame σ σ2 [3] [23, 24, 25, 26, 37] [2, 3, 4, 5, 6, 7, 8] :=
    Env.Frame.trans G1 (Env.Frame.mono F2 (by decide) (by decide) (by decide))
  refine runs_seq (runs_mcopy (L := df2L) (w := w) σ2 (dd := 9) (one := 2) (m := 3) (B := 3) (A := 80) (t := 37)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [G2.1 9 (by decide), h9]) (by rw [G2.1 2 (by decide), h1])) (fun σ3 h3 => ?_)
  obtain ⟨m3, F3, -⟩ := h3
  have G3 : Env.Frame σ σ3 [3] [23, 24, 25, 26, 37] [2, 3, 4, 5, 6, 7, 8] :=
    Env.Frame.trans G2 (Env.Frame.mono F3 (by decide) (by decide) (by decide))
  refine runs_seq (runs_mcopy (L := df2L) (w := w) σ3 (dd := 9) (one := 2) (m := 3) (B := 4) (A := 81) (t := 37)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [G3.1 9 (by decide), h9]) (by rw [G3.1 2 (by decide), h1])) (fun σ4 h4 => ?_)
  obtain ⟨m4, F4, -⟩ := h4
  have G4 : Env.Frame σ σ4 [3] [23, 24, 25, 26, 37] [2, 3, 4, 5, 6, 7, 8] :=
    Env.Frame.trans G3 (Env.Frame.mono F4 (by decide) (by decide) (by decide))
  refine runs_seq (runs_mcopy (L := df2L) (w := w) σ4 (dd := 9) (one := 2) (m := 3) (B := 5) (A := 82) (t := 37)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [G4.1 9 (by decide), h9]) (by rw [G4.1 2 (by decide), h1])) (fun σ5 h5 => ?_)
  obtain ⟨m5, F5, -⟩ := h5
  have G5 : Env.Frame σ σ5 [3] [23, 24, 25, 26, 37] [2, 3, 4, 5, 6, 7, 8] :=
    Env.Frame.trans G4 (Env.Frame.mono F5 (by decide) (by decide) (by decide))
  refine runs_seq (runs_vcopy (L := df2L) (w := w) σ5 (dv := 0) (one := 2) (i := 3) (y := 6) (x := 83) (t := 37)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [G5.1 0 (by decide), hd]) (by rw [G5.1 2 (by decide), h1])) (fun σ6 h6 => ?_)
  obtain ⟨v6, F6, -⟩ := h6
  have G6 : Env.Frame σ σ6 [3] [23, 24, 25, 26, 37] [2, 3, 4, 5, 6, 7, 8] :=
    Env.Frame.trans G5 (Env.Frame.mono F6 (by decide) (by decide) (by decide))
  refine runs_seq_eq (runs_smov (L := df2L) (w := w) (σ := σ6) (x := 24) (y := 81) (by decide) (by decide)) ?_
  set σ7 := σ6.setSc 24 (σ6.sc 81) with hσ7
  have G7 : Env.Frame σ σ7 [3] [23, 24, 25, 26, 37] [2, 3, 4, 5, 6, 7, 8] :=
    Env.Frame.trans G6 (Env.Frame.mono (FS σ6 24 _) (by decide) (by decide) (by decide))
  refine runs_seq (runs_vcopy (L := df2L) (w := w) σ7 (dv := 0) (one := 2) (i := 3) (y := 7) (x := 84) (t := 37)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [G7.1 0 (by decide), hd]) (by rw [G7.1 2 (by decide), h1])) (fun σ8 h8 => ?_)
  obtain ⟨v8, F8, -⟩ := h8
  have G8 : Env.Frame σ σ8 [3] [23, 24, 25, 26, 37] [2, 3, 4, 5, 6, 7, 8] :=
    Env.Frame.trans G7 (Env.Frame.mono F8 (by decide) (by decide) (by decide))
  refine runs_seq_eq (runs_smov (L := df2L) (w := w) (σ := σ8) (x := 25) (y := 84) (by decide) (by decide)) ?_
  set σ9 := σ8.setSc 25 (σ8.sc 84) with hσ9
  have G9 : Env.Frame σ σ9 [3] [23, 24, 25, 26, 37] [2, 3, 4, 5, 6, 7, 8] :=
    Env.Frame.trans G8 (Env.Frame.mono (FS σ8 25 _) (by decide) (by decide) (by decide))
  refine runs_seq (runs_vcopy (L := df2L) (w := w) σ9 (dv := 0) (one := 2) (i := 3) (y := 8) (x := 90) (t := 37)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [G9.1 0 (by decide), hd]) (by rw [G9.1 2 (by decide), h1])) (fun σ10 h10 => ?_)
  obtain ⟨v10, F10, -⟩ := h10
  have G10 : Env.Frame σ σ10 [3] [23, 24, 25, 26, 37] [2, 3, 4, 5, 6, 7, 8] :=
    Env.Frame.trans G9 (Env.Frame.mono F10 (by decide) (by decide) (by decide))
  refine runs_mono (runs_smov (L := df2L) (w := w) (σ := σ10) (x := 26) (y := 100) (by decide) (by decide)) le_rfl
    (fun σ' e => ?_)
  subst e
  have T10 : Env.Frame σ10 (σ10.setSc 26 (σ10.sc 100)) [3] [26, 37] [] :=
    Env.Frame.mono (FS σ10 26 _) (by decide) (by decide) (by decide)
  have T9 : Env.Frame σ9 (σ10.setSc 26 (σ10.sc 100)) [3] [26, 37] [8] :=
    Env.Frame.trans (Env.Frame.mono F10 (by decide) (by decide) (by decide))
      (Env.Frame.mono T10 (by decide) (by decide) (by decide))
  have T8 : Env.Frame σ8 (σ10.setSc 26 (σ10.sc 100)) [3] [25, 26, 37] [8] :=
    Env.Frame.trans (Env.Frame.mono (FS σ8 25 _) (by decide) (by decide) (by decide))
      (Env.Frame.mono T9 (by decide) (by decide) (by decide))
  have T7 : Env.Frame σ7 (σ10.setSc 26 (σ10.sc 100)) [3] [25, 26, 37] [7, 8] :=
    Env.Frame.trans (Env.Frame.mono F8 (by decide) (by decide) (by decide))
      (Env.Frame.mono T8 (by decide) (by decide) (by decide))
  have T6 : Env.Frame σ6 (σ10.setSc 26 (σ10.sc 100)) [3] [24, 25, 26, 37] [7, 8] :=
    Env.Frame.trans (Env.Frame.mono (FS σ6 24 _) (by decide) (by decide) (by decide))
      (Env.Frame.mono T7 (by decide) (by decide) (by decide))
  have T5 : Env.Frame σ5 (σ10.setSc 26 (σ10.sc 100)) [3] [24, 25, 26, 37] [6, 7, 8] :=
    Env.Frame.trans (Env.Frame.mono F6 (by decide) (by decide) (by decide))
      (Env.Frame.mono T6 (by decide) (by decide) (by decide))
  have T4 : Env.Frame σ4 (σ10.setSc 26 (σ10.sc 100)) [3] [24, 25, 26, 37] [5, 6, 7, 8] :=
    Env.Frame.trans (Env.Frame.mono F5 (by decide) (by decide) (by decide))
      (Env.Frame.mono T5 (by decide) (by decide) (by decide))
  have T3 : Env.Frame σ3 (σ10.setSc 26 (σ10.sc 100)) [3] [24, 25, 26, 37] [4, 5, 6, 7, 8] :=
    Env.Frame.trans (Env.Frame.mono F4 (by decide) (by decide) (by decide))
      (Env.Frame.mono T4 (by decide) (by decide) (by decide))
  have T2 : Env.Frame σ2 (σ10.setSc 26 (σ10.sc 100)) [3] [24, 25, 26, 37] [3, 4, 5, 6, 7, 8] :=
    Env.Frame.trans (Env.Frame.mono F3 (by decide) (by decide) (by decide))
      (Env.Frame.mono T3 (by decide) (by decide) (by decide))
  have T1 : Env.Frame σ1 (σ10.setSc 26 (σ10.sc 100)) [3] [24, 25, 26, 37] [2, 3, 4, 5, 6, 7, 8] :=
    Env.Frame.trans (Env.Frame.mono F2 (by decide) (by decide) (by decide))
      (Env.Frame.mono T2 (by decide) (by decide) (by decide))
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, Env.Frame.trans G10 (Env.Frame.mono (FS σ10 26 _) (by decide)
    (by decide) (by decide))⟩
  · rw [T1.2.1 23 (by decide)]; simp [σ1]
  · rw [Env.Frame.vec_eq T2 (a := 2) (by decide), v2, Env.Frame.vec_eq G1 (a := 92) (by decide)]
  · rw [Env.Frame.mat_eq T3 (a := 3) (by decide), m3, Env.Frame.mat_eq G2 (a := 80) (by decide)]
  · rw [Env.Frame.mat_eq T4 (a := 4) (by decide), m4, Env.Frame.mat_eq G3 (a := 81) (by decide)]
  · rw [Env.Frame.mat_eq T5 (a := 5) (by decide), m5, Env.Frame.mat_eq G4 (a := 82) (by decide)]
  · rw [Env.Frame.vec_eq T6 (a := 6) (by decide), v6, Env.Frame.vec_eq G5 (a := 83) (by decide)]
  · rw [T7.2.1 24 (by decide)]; simp only [σ7, Env.setSc_sc, ↓reduceIte]; rw [G6.2.1 81 (by decide)]
  · rw [Env.Frame.vec_eq T8 (a := 7) (by decide), v8, Env.Frame.vec_eq G7 (a := 84) (by decide)]
  · rw [T9.2.1 25 (by decide)]; simp only [σ9, Env.setSc_sc, ↓reduceIte]; rw [G8.2.1 84 (by decide)]
  · rw [Env.Frame.vec_eq (Env.Frame.mono (FS σ10 26 (σ10.sc 100)) (by decide) (by decide) (by decide) :
      Env.Frame σ10 _ [] [26] []) (a := 8) (by decide), v10, Env.Frame.vec_eq G9 (a := 90) (by decide)]
  · simp only [Env.setSc_sc, ↓reduceIte]; rw [G10.2.1 100 (by decide)]

theorem runs_stInit (σ : Env d) (hd : σ.nat 0 = d)
    (h1 : σ.nat 2 = 1) (h9 : σ.nat 9 = d * d) (h21 : σ.sc 21 = 0) (h27 : σ.sc 27 = 1) :
    Runs df2L w stInit σ (d * d * 15 + d * 41 + 45) (fun σ' =>
      σ'.sc 23 = 1 ∧ σ'.vec 2 = 0 ∧ σ'.mat 3 = (σ.sc 8)⁻¹ • 1 ∧ σ'.mat 4 = σ.sc 8 • 1 ∧
        σ'.mat 5 = Real.sqrt (σ.sc 8) • 1 ∧ σ'.vec 6 = 0 ∧ σ'.sc 24 = 0 ∧ σ'.vec 7 = 0 ∧ σ'.sc 25 = 0 ∧
        σ'.vec 8 = 0 ∧ σ'.sc 26 = 1 - σ.sc 10 ∧
        Env.Frame σ σ' [3, 5] [23, 24, 25, 26, 56, 57] [2, 3, 4, 5, 6, 7, 8]) := by
  let l : List SI := [SI.const 23 1, SI.const 24 0, SI.const 25 0, SI.op2 .sub 26 27 10, SI.op2 .div 56 27 8,
    SI.op1 .sqrt 57 8]
  refine runs_mono (K := sCost l + ((d * 5 + 3) + ((d * 5 + 3) + ((d * 5 + 3) + ((d * 5 + 3) + ((d * d * 5 + 3) +
      ((d * 7 + 4) + ((d * d * 5 + 3) + ((d * 7 + 4) + ((d * d * 5 + 3) + (d * 7 + 4)))))))))))
    (runs_seq_eq (runs_sprog (L := df2L) (w := w) l (by decide) σ) ?_)
    (by simp only [l, sCost, List.map, SI.cost, List.sum_cons, List.sum_nil]; ring_nf; omega) (fun σ' h => h)
  set σ1 : Env d := { σ with sc := sEval σ.nat l σ.sc } with hσ1
  have F1 : Env.Frame σ σ1 [] [23, 24, 25, 26, 56, 57] [] := ⟨fun _ _ => rfl, fun x hx => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    simp only [σ1, l, sEval, List.foldl, SI.step, SI.dst, SI.val]
    simp [hx.1, hx.2.1, hx.2.2.1, hx.2.2.2.1, hx.2.2.2.2.1, hx.2.2.2.2.2], fun _ _ => rfl, rfl, rfl, rfl⟩
  have s23 : σ1.sc 23 = 1 := by simp [σ1, l, sEval, SI.step, SI.dst, SI.val]
  have s24 : σ1.sc 24 = 0 := by simp [σ1, l, sEval, SI.step, SI.dst, SI.val]
  have s25 : σ1.sc 25 = 0 := by simp [σ1, l, sEval, SI.step, SI.dst, SI.val]
  have s26 : σ1.sc 26 = 1 - σ.sc 10 := by simp [σ1, l, sEval, SI.step, SI.dst, SI.val, Op2.eval, h27]
  have s56 : σ1.sc 56 = (σ.sc 8)⁻¹ := by simp [σ1, l, sEval, SI.step, SI.dst, SI.val, Op2.eval, h27]
  have s57 : σ1.sc 57 = Real.sqrt (σ.sc 8) := by simp [σ1, l, sEval, SI.step, SI.dst, SI.val, Op1.eval]
  have s21 : σ1.sc 21 = 0 := by rw [F1.2.1 21 (by decide), h21]
  have s8 : σ1.sc 8 = σ.sc 8 := F1.2.1 8 (by decide)
  have hd1 : σ1.nat 0 = d := hd
  have h11 : σ1.nat 2 = 1 := h1
  have h91 : σ1.nat 9 = d * d := h9
  -- the vectors
  refine runs_seq (runs_vfill (L := df2L) (w := w) σ1 (dv := 0) (one := 2) (i := 3) (y := 2) (z := 21)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hd1 h11) (fun σ2 h2 => ?_)
  obtain ⟨v2, F2, -⟩ := h2
  refine runs_seq (runs_vfill (L := df2L) (w := w) σ2 (dv := 0) (one := 2) (i := 3) (y := 6) (z := 21)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [F2.1 0 (by decide), hd1]) (by rw [F2.1 2 (by decide), h11])) (fun σ3 h3 => ?_)
  obtain ⟨v3, F3, -⟩ := h3
  refine runs_seq (runs_vfill (L := df2L) (w := w) σ3 (dv := 0) (one := 2) (i := 3) (y := 7) (z := 21)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [F3.1 0 (by decide), F2.1 0 (by decide), hd1]) (by rw [F3.1 2 (by decide), F2.1 2 (by decide), h11]))
    (fun σ4 h4 => ?_)
  obtain ⟨v4, F4, -⟩ := h4
  have F14 : Env.Frame σ1 σ4 [3] [] [2, 6, 7] :=
    Env.Frame.trans (Env.Frame.mono F2 (by decide) (by decide) (by decide)) (Env.Frame.trans
      (Env.Frame.mono F3 (by decide) (by decide) (by decide)) (Env.Frame.mono F4 (by decide) (by decide)
        (by decide)))
  refine runs_seq (runs_vfill (L := df2L) (w := w) σ4 (dv := 0) (one := 2) (i := 3) (y := 8) (z := 21)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [F14.1 0 (by decide), hd1]) (by rw [F14.1 2 (by decide), h11])) (fun σ5 h5 => ?_)
  obtain ⟨v5, F5, -⟩ := h5
  have F15 : Env.Frame σ1 σ5 [3] [] [2, 6, 7, 8] :=
    Env.Frame.trans (Env.Frame.mono F14 (by decide) (by decide) (by decide))
      (Env.Frame.mono F5 (by decide) (by decide) (by decide))
  have n5 : ∀ i ∈ [0, 2, 9], σ5.nat i = σ1.nat i := fun i hi => F15.1 i (by revert i; decide)
  -- the matrices
  have hdiag : ∀ (c : ℝ), Matrix.of (fun a b : Fin d => if a = b then c else (Matrix.of fun _ _ => (0 : ℝ)) a b) =
      c • (1 : Matrix (Fin d) (Fin d) ℝ) := fun c => by
    ext a b; by_cases h : a = b <;> simp [h]
  refine runs_seq (runs_mfill (L := df2L) (w := w) σ5 (dd := 9) (one := 2) (m := 3) (A := 3) (z := 21)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [n5 9 (by simp), h91]) (by rw [n5 2 (by simp), h11])) (fun σ6 h6 => ?_)
  obtain ⟨m6, F6, -⟩ := h6
  refine runs_seq (runs_mdiag (L := df2L) (w := w) σ6 (dv := 0) (one := 2) (i := 3) (k := 5) (A := 3) (z := 56)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [F6.1 0 (by decide), n5 0 (by simp), hd1])
    (by rw [F6.1 2 (by decide), n5 2 (by simp), h11])) (fun σ7 h7 => ?_)
  obtain ⟨m7, F7, -⟩ := h7
  have F17 : Env.Frame σ1 σ7 [3, 5] [] [2, 3, 6, 7, 8] :=
    Env.Frame.trans (Env.Frame.mono F15 (by decide) (by decide) (by decide)) (Env.Frame.trans
      (Env.Frame.mono F6 (by decide) (by decide) (by decide)) (Env.Frame.mono F7 (by decide) (by decide)
        (by decide)))
  refine runs_seq (runs_mfill (L := df2L) (w := w) σ7 (dd := 9) (one := 2) (m := 3) (A := 4) (z := 21)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [F17.1 9 (by decide), h91]) (by rw [F17.1 2 (by decide), h11])) (fun σ8 h8 => ?_)
  obtain ⟨m8, F8, -⟩ := h8
  refine runs_seq (runs_mdiag (L := df2L) (w := w) σ8 (dv := 0) (one := 2) (i := 3) (k := 5) (A := 4) (z := 8)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [F8.1 0 (by decide), F17.1 0 (by decide), hd1])
    (by rw [F8.1 2 (by decide), F17.1 2 (by decide), h11])) (fun σ9 h9' => ?_)
  obtain ⟨m9, F9, -⟩ := h9'
  have F19 : Env.Frame σ1 σ9 [3, 5] [] [2, 3, 4, 6, 7, 8] :=
    Env.Frame.trans (Env.Frame.mono F17 (by decide) (by decide) (by decide)) (Env.Frame.trans
      (Env.Frame.mono F8 (by decide) (by decide) (by decide)) (Env.Frame.mono F9 (by decide) (by decide)
        (by decide)))
  refine runs_seq (runs_mfill (L := df2L) (w := w) σ9 (dd := 9) (one := 2) (m := 3) (A := 5) (z := 21)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [F19.1 9 (by decide), h91]) (by rw [F19.1 2 (by decide), h11])) (fun σ10 h10 => ?_)
  obtain ⟨m10, F10, -⟩ := h10
  refine runs_mono (runs_mdiag (L := df2L) (w := w) σ10 (dv := 0) (one := 2) (i := 3) (k := 5) (A := 5) (z := 57)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [F10.1 0 (by decide), F19.1 0 (by decide), hd1])
    (by rw [F10.1 2 (by decide), F19.1 2 (by decide), h11])) le_rfl (fun σ' h => ?_)
  obtain ⟨m11, F11, -⟩ := h
  have F1e : Env.Frame σ1 σ' [3, 5] [] [2, 3, 4, 5, 6, 7, 8] :=
    Env.Frame.trans (Env.Frame.mono F19 (by decide) (by decide) (by decide)) (Env.Frame.trans
      (Env.Frame.mono F10 (by decide) (by decide) (by decide)) (Env.Frame.mono F11 (by decide) (by decide)
        (by decide)))
  have sc' : ∀ x, σ'.sc x = σ1.sc x := fun x => F1e.2.1 x (by simp)
  have e2 : σ2.sc 21 = σ1.sc 21 := F2.2.1 21 (by simp)
  have e3 : σ3.sc 21 = σ1.sc 21 := by rw [F3.2.1 21 (by simp), e2]
  have e4 : σ4.sc 21 = σ1.sc 21 := F14.2.1 21 (by simp)
  have e5 : ∀ x, σ5.sc x = σ1.sc x := fun x => F15.2.1 x (by simp)
  have e6 : ∀ x, σ6.sc x = σ1.sc x := fun x => by rw [F6.2.1 x (by simp), e5]
  have e7 : ∀ x, σ7.sc x = σ1.sc x := fun x => F17.2.1 x (by simp)
  have e8 : ∀ x, σ8.sc x = σ1.sc x := fun x => by rw [F8.2.1 x (by simp), e7]
  have e9 : ∀ x, σ9.sc x = σ1.sc x := fun x => F19.2.1 x (by simp)
  have e10 : ∀ x, σ10.sc x = σ1.sc x := fun x => by rw [F10.2.1 x (by simp), e9]
  have T9 : Env.Frame σ9 σ' [3, 5] [] [5] :=
    Env.Frame.trans (Env.Frame.mono F10 (by decide) (by decide) (by decide))
      (Env.Frame.mono F11 (by decide) (by decide) (by decide))
  have T7 : Env.Frame σ7 σ' [3, 5] [] [4, 5] :=
    Env.Frame.trans (Env.Frame.mono F8 (by decide) (by decide) (by decide)) (Env.Frame.trans
      (Env.Frame.mono F9 (by decide) (by decide) (by decide)) (Env.Frame.mono T9 (by decide) (by decide)
        (by decide)))
  have T5 : Env.Frame σ5 σ' [3, 5] [] [3, 4, 5] :=
    Env.Frame.trans (Env.Frame.mono F6 (by decide) (by decide) (by decide)) (Env.Frame.trans
      (Env.Frame.mono F7 (by decide) (by decide) (by decide)) (Env.Frame.mono T7 (by decide) (by decide)
        (by decide)))
  have T4 : Env.Frame σ4 σ' [3, 5] [] [3, 4, 5, 8] :=
    Env.Frame.trans (Env.Frame.mono F5 (by decide) (by decide) (by decide))
      (Env.Frame.mono T5 (by decide) (by decide) (by decide))
  have T3 : Env.Frame σ3 σ' [3, 5] [] [3, 4, 5, 7, 8] :=
    Env.Frame.trans (Env.Frame.mono F4 (by decide) (by decide) (by decide))
      (Env.Frame.mono T4 (by decide) (by decide) (by decide))
  have T2 : Env.Frame σ2 σ' [3, 5] [] [3, 4, 5, 6, 7, 8] :=
    Env.Frame.trans (Env.Frame.mono F3 (by decide) (by decide) (by decide))
      (Env.Frame.mono T3 (by decide) (by decide) (by decide))
  refine ⟨by rw [sc', s23], ?_, ?_, ?_, ?_, ?_, by rw [sc', s24], ?_, by rw [sc', s25], ?_, by rw [sc', s26],
    Env.Frame.trans (Env.Frame.mono F1 (by decide) (by decide) (by decide))
      (Env.Frame.mono F1e (by decide) (by decide) (by decide))⟩
  · rw [Env.Frame.vec_eq T2 (a := 2) (by decide), v2, s21]; rfl
  · rw [Env.Frame.mat_eq T7 (a := 3) (by decide), m7, m6, e6 56, e5 21, s56, s21]; exact hdiag _
  · rw [Env.Frame.mat_eq T9 (a := 4) (by decide), m9, m8, e8 8, e7 21, s8, s21]; exact hdiag _
  · rw [m11, m10, e10 57, e9 21, s57, s21]; exact hdiag _
  · rw [Env.Frame.vec_eq T3 (a := 6) (by decide), v3, e2, s21]; rfl
  · rw [Env.Frame.vec_eq T4 (a := 7) (by decide), v4, e3, s21]; rfl
  · rw [Env.Frame.vec_eq T5 (a := 8) (by decide), v5, e4, s21]; rfl

theorem runs_yCode (σ : Env d) (h19 : σ.sc 19 = 1 / 2)
    (h27 : σ.sc 27 = 1) :
    Runs df2L w yCode σ 9 (fun σ' =>
      σ'.sc 31 = σ.sc 30 * (σ.sc 32 + σ.sc 29 / 2) / 2 + 2 * (σ.sc 30 - 1) / σ.sc 10 ∧
        Env.Frame σ σ' [] [31, 60, 61, 62] []) := by
  let l : List SI := [SI.op2 .mul 60 29 19, SI.op2 .add 60 32 60, SI.op2 .mul 60 30 60, SI.op2 .mul 60 60 19,
    SI.op2 .sub 61 30 27, SI.const 62 2, SI.op2 .mul 61 62 61, SI.op2 .div 61 61 10, SI.op2 .add 31 60 61]
  have hcost : sCost l ≤ 9 := by
    simp [l, sCost, SI.cost]
  refine runs_mono (runs_sprog (L := df2L) (w := w) l (by decide) σ) hcost (fun σ' e => ?_)
  subst e
  have h31 : ({ σ with sc := sEval σ.nat l σ.sc }).sc 31 =
      σ.sc 30 * (σ.sc 32 + σ.sc 29 / 2) / 2 + 2 * (σ.sc 30 - 1) / σ.sc 10 := by
    simp only [sEval, List.foldl, SI.step, SI.dst, SI.val, Function.update_apply, Op2.eval, l]
    simp [h19, h27]
    ring
  have hframe : Env.Frame σ ({ σ with sc := sEval σ.nat l σ.sc }) [] [31, 60, 61, 62] [] := by
    refine ⟨fun i _ => rfl, fun x hx => ?_, fun a _ => rfl, rfl, rfl, rfl⟩
    simp only [sEval, List.foldl, SI.step, SI.dst, SI.val, Function.update_apply, Op2.eval, l]
    simp at hx
    simp [hx]
  exact And.intro h31 hframe

/-! ## The compositions of part B -/

/-- The natural variables that part B writes. -/
def nsB : List ℕ := [3, 4, 5] ++ List.range' 14 16

/-- The scalars that part B writes. -/
def ssB : List ℕ := 31 :: List.range' 22 5 ++ List.range' 34 86 ++ List.range' 192 128

/-- The arrays that part B writes. -/
def asB : List ℕ := List.range' 2 7 ++ [12, 13, 15] ++ List.range' 16 14 ++ List.range' 80 16

open Classical in
/-- A rule for a call of AP with the variables `V` and the membership code `memQ` of the region `Q`: from every
environment with `I`, the code answers `apCall` on its inputs within `K` steps, and writes only the variables of AP
and of `memQ`. -/
def ApSpec (w : World d) (memQ : Cmd) (V : AP.APVars) (Q : Set (Fin d → ℝ)) (I : Env d → Prop) (K : ℕ) : Prop :=
  ∀ σ, I σ → σ.nat V.dv = d → σ.nat V.one = 1 → Runs df2L w (AP.apCode df2L memQ V) σ K (fun σ' =>
    (match apCall Q (σ.vec V.a0) (σ.sc V.r) (σ.sc V.R) (σ.mat V.P) (σ.vec V.w) (σ.sc V.e) with
      | none => σ'.sc V.ok = 0
      | some x => σ'.sc V.ok = 1 ∧ σ'.vec V.out = x) ∧
      Env.Frame σ σ' (AP.apN V ++ [3, 4, 5]) (AP.apS V ++ memS) (AP.apA V ++ [12, 13, 95]))

/-- The facts that hold through `df2Next`: the constants, the parameters, the position, the state of the epoch, the
mode `run`, the draw `ξ`, `w = A ξ` and `Y`. -/
structure NxPre (p : Df2OPar) (n : ℕ) (Ps : PgSp d) (st : Df2St d) (ξ : Fin d → ℝ) (Y : ℝ) (σ : Env d) : Prop where
  nd : σ.nat 0 = d
  n1 : σ.nat 2 = 1
  n9 : σ.nat 9 = d * d
  nn : σ.nat 1 = n
  c19 : σ.sc 19 = 1 / 2
  c21 : σ.sc 21 = 0
  c27 : σ.sc 27 = 1
  par : ParRep p σ
  pos : PosRep Ps σ
  rep : StRep st σ
  mode : σ.sc 22 = 2
  xi : σ.vec 9 = ξ
  hw : σ.vec 10 = st.A *ᵥ ξ
  hY : σ.sc 31 = Y

/-- `NxPre` and, after `nx1`, `1 - λ` and `q`. -/
structure NxCtx (p : Df2OPar) (n : ℕ) (Ps : PgSp d) (st : Df2St d) (ξ : Fin d → ℝ) (Y : ℝ) (σ : Env d) : Prop where
  pre : NxPre p n Ps st ξ Y σ
  lam : σ.sc 64 = 1 - p.lam
  q : σ.sc 67 = nxQ p ξ Y

theorem NxPre.frameY {p : Df2OPar} {n : ℕ} {Ps : PgSp d} {st : Df2St d} {ξ : Fin d → ℝ} {Y Y' : ℝ}
    {σ σ' : Env d} {ns ss as : List ℕ} (h : NxPre p n Ps st ξ Y σ) (hF : Env.Frame σ σ' ns ss as)
    (hns : ∀ i ∈ ns, i ∉ [0, 1, 2, 7, 9]) (hss : ∀ x ∈ ss, x ∉ List.range' 3 25)
    (has : ∀ a ∈ as, 10 < a) (hY : σ'.sc 31 = Y') : NxPre p n Ps st ξ Y' σ' := by
  have en : ∀ i ∈ [0, 1, 2, 7, 9], σ'.nat i = σ.nat i := fun i hi => hF.1 i (fun h' => hns i h' hi)
  have es : ∀ x ∈ List.range' 3 25, σ'.sc x = σ.sc x :=
    fun x hx => hF.2.1 x (fun h' => hss x h' hx)
  have ea : ∀ a, a ≤ 10 → σ'.arr a = σ.arr a := fun a ha => hF.2.2.1 a (fun h' => by have := has a h'; omega)
  have ev : ∀ a, a ≤ 10 → σ'.vec a = σ.vec a := fun a ha => by unfold Env.vec; rw [ea a ha]
  have em : ∀ a, a ≤ 10 → σ'.mat a = σ.mat a := fun a ha => by unfold Env.mat; rw [ea a ha]
  obtain ⟨hst23, hst2, hst3, hst4, hst5, hst6, hst24, hst7, hst25, hst8, hst26⟩ := h.rep
  refine ⟨by rw [en 0 (by simp), h.nd], by rw [en 2 (by simp), h.n1], by rw [en 9 (by simp), h.n9],
    by rw [en 1 (by simp), h.nn], by rw [es 19 (by simp), h.c19], by rw [es 21 (by simp), h.c21],
    by rw [es 27 (by simp), h.c27], h.par.frame hF (fun h' => hns 7 h' (by simp))
      (fun x hx => by have := hss x hx; simp at this; omega),
    ⟨by rw [ev 0 (by norm_num), h.pos.1], by rw [em 1 (by norm_num), h.pos.2]⟩,
    ⟨by rw [es 23 (by simp), hst23], by rw [ev 2 (by norm_num), hst2], by rw [em 3 (by norm_num), hst3],
      by rw [em 4 (by norm_num), hst4], by rw [em 5 (by norm_num), hst5], by rw [ev 6 (by norm_num), hst6],
      by rw [es 24 (by simp), hst24], by rw [ev 7 (by norm_num), hst7], by rw [es 25 (by simp), hst25],
      by rw [ev 8 (by norm_num), hst8], by rw [es 26 (by simp), hst26]⟩,
    by rw [es 22 (by simp), h.mode], by rw [ev 9 (by norm_num), h.xi], by rw [ev 10 (by norm_num), h.hw], hY⟩

theorem NxPre.frame {p : Df2OPar} {n : ℕ} {Ps : PgSp d} {st : Df2St d} {ξ : Fin d → ℝ} {Y : ℝ} {σ σ' : Env d}
    {ns ss as : List ℕ} (h : NxPre p n Ps st ξ Y σ) (hF : Env.Frame σ σ' ns ss as)
    (hns : ∀ i ∈ ns, i ∉ [0, 1, 2, 7, 9]) (hss : ∀ x ∈ ss, x ∉ List.range' 3 25 ++ [31])
    (has : ∀ a ∈ as, 10 < a) : NxPre p n Ps st ξ Y σ' :=
  h.frameY hF hns (fun x hx h' => hss x hx (List.mem_append_left _ h')) has
    (by rw [hF.2.1 31 (fun h' => hss 31 h' (by simp)), h.hY])

theorem NxCtx.frame {p : Df2OPar} {n : ℕ} {Ps : PgSp d} {st : Df2St d} {ξ : Fin d → ℝ} {Y : ℝ} {σ σ' : Env d}
    {ns ss as : List ℕ} (h : NxCtx p n Ps st ξ Y σ) (hF : Env.Frame σ σ' ns ss as)
    (hns : ∀ i ∈ ns, i ∉ [0, 1, 2, 7, 9]) (hss : ∀ x ∈ ss, x ∉ List.range' 3 25 ++ [31, 64, 67])
    (has : ∀ a ∈ as, 10 < a) : NxCtx p n Ps st ξ Y σ' :=
  ⟨h.pre.frame hF hns (fun x hx h' => hss x hx (by simp at h' ⊢; omega)) has,
    by rw [hF.2.1 64 (fun h' => hss 64 h' (by simp)), h.lam], by rw [hF.2.1 67 (fun h' => hss 67 h' (by simp)), h.q]⟩

/-- `NxRep` survives a frame that keeps the arrays `80` to `84` and the scalars `81`, `84`. -/
theorem NxRep.frame {F : NxF d} {σ σ' : Env d} {ns ss as : List ℕ} (h : NxRep F σ) (hF : Env.Frame σ σ' ns ss as)
    (hss : ∀ x ∈ [81, 84], x ∉ ss) (has : ∀ a ∈ [80, 81, 82, 83, 84], a ∉ as) : NxRep F σ' := by
  obtain ⟨h80, h81, h82, h83, hk, h84, hl⟩ := h
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hss has
  exact ⟨by rw [Env.Frame.mat_eq hF has.1, h80], by rw [Env.Frame.mat_eq hF has.2.1, h81],
    by rw [Env.Frame.mat_eq hF has.2.2.1, h82], by rw [Env.Frame.vec_eq hF has.2.2.2.1, h83],
    by rw [hF.2.1 81 hss.1, hk], by rw [Env.Frame.vec_eq hF has.2.2.2.2, h84], by rw [hF.2.1 84 hss.2, hl]⟩

/-- The rule of `toGuard`. -/
theorem runs_toGuard (σ : Env d) :
    Runs df2L w toGuard σ 1 (fun σ' => ModeRep .guard σ' ∧ Env.Frame σ σ' [] [22] []) :=
  runs_mono (runs_sconst (by decide) 1) le_rfl (fun σ' e => by
    subst e; exact ⟨by simp [ModeRep], Env.Frame.setSc (Env.Frame.refl _ _ _ _) (by simp) _⟩)

/-- What the second call of AP needs: the read set of `memRp` and its inputs. -/
def nxI2 (p : Df2OPar) (n : ℕ) (Ps : PgSp d) (F : NxF d) (pt wmu : Fin d → ℝ) (σ : Env d) : Prop :=
  Iq2 p Ps F σ ∧ σ.vec 90 = (1 - p.sb) • pt ∧ σ.sc 100 = p.sb * (1 - p.eps) ∧ σ.vec 91 = wmu ∧
    σ.sc 106 = 1 / (16 * (n : ℝ) ^ 2 * max 1 (4 * p.R ^ 2 * F.P.trace))

/-- The steps of `nxCommit`. -/
def kCommit (d : ℕ) : ℕ := d * d * 21 + d * 28 + 25

open Classical in
/-- The rule of `nxC6`: the accuracy of the second call of AP, the call, and the commit of the new state. -/
theorem runs_nxC6 (p : Df2OPar) (n : ℕ) (Ps : PgSp d) (st : Df2St d) (ξ : Fin d → ℝ) (Y : ℝ) (F : NxF d)
    (pt wmu : Fin d → ℝ) (K2 : ℕ) (σ : Env d) (hc : NxCtx p n Ps st ξ Y σ) (hF : NxRep F σ)
    (h85 : σ.sc 85 = F.P.trace) (h90 : σ.vec 90 = (1 - p.sb) • pt) (h100 : σ.sc 100 = p.sb * (1 - p.eps))
    (h91 : σ.vec 91 = wmu) (h110 : σ.sc 110 = (1 - p.eps)⁻¹) (h112 : σ.sc 112 = p.c1 * p.rho)
    (hAP : ApSpec w memRp apV2 {y | y ∈ df2Keps w.K Ps p.R p.eps ∧ df2Phi F.P F.b F.k y ≤ p.c1 * p.rho}
      (nxI2 p n Ps F pt wmu) K2) :
    Runs df2L w nxC6 σ (13 + (K2 + (kCommit d + 2))) (fun σ' =>
      ModeRep (nxT6 p n (df2Keps w.K Ps p.R p.eps) F ((1 - p.sb) • pt) (p.sb * (1 - p.eps)) wmu) σ' ∧
        Env.Frame σ σ' nsB ssB asB) := by
  obtain ⟨hP80, hS81, hA82, hP83, hP81, hG84, hl84⟩ := hF
  have h17 : σ.sc 17 = p.R := hc.pre.par.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  refine runs_seq (runs_nx8 σ hc.pre.c27) (fun σ1 h1' => ?_)
  obtain ⟨s106, F1⟩ := h1'
  have k1 : ∀ x ∉ [105, 106, 107], σ1.sc x = σ.sc x := F1.2.1
  have hI : Iq2 p Ps F σ1 ∧ σ1.vec 90 = (1 - p.sb) • pt ∧ σ1.sc 100 = p.sb * (1 - p.eps) ∧ σ1.vec 91 = wmu ∧
      σ1.sc 106 = 1 / (16 * (n : ℝ) ^ 2 * max 1 (4 * p.R ^ 2 * F.P.trace)) := by
    refine ⟨⟨hc.pre.pos.frame F1 (by decide) (by decide), by rw [k1 17 (by decide), h17],
      by rw [k1 110 (by decide), h110], by rw [k1 19 (by decide), hc.pre.c19],
      by rw [Env.Frame.mat_eq F1 (by decide), hP80], by rw [Env.Frame.vec_eq F1 (by decide), hP83],
      by rw [k1 81 (by decide), hP81], by rw [k1 112 (by decide), h112]⟩,
      by rw [Env.Frame.vec_eq F1 (by decide), h90], by rw [k1 100 (by decide), h100],
      by rw [Env.Frame.vec_eq F1 (by decide), h91], ?_⟩
    rw [s106, hc.pre.nn, h17, h85]
  refine runs_seq (hAP σ1 hI (by show σ1.nat 0 = d; rw [F1.1 0 (by decide), hc.pre.nd])
    (by show σ1.nat 2 = 1; rw [F1.1 2 (by decide), hc.pre.n1])) (fun σ2 h2 => ?_)
  obtain ⟨r2, F2⟩ := h2
  obtain ⟨hI2, e90, e100, e91, e106⟩ := hI
  dsimp only [apV2] at r2 F2
  rw [e90, e100, k1 17 (by decide), h17, hI2.2.2.2.2.1, e91, e106] at r2
  have k2 : ∀ x ∈ [21, 22], σ2.sc x = σ.sc x := fun x hx => by
    rw [F2.2.1 x (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> decide),
      k1 x (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> decide)]
  have FB : Env.Frame σ σ2 nsB ssB asB := Env.Frame.trans (Env.Frame.mono F1 (by simp) (by simp [ssB]) (by simp))
    (Env.Frame.mono F2 (by intro x hx; simp [AP.apN, nsB] at hx ⊢; omega)
      (by intro x hx; simp [AP.apS, memS, ssB] at hx ⊢; omega) (by intro x hx; simp [AP.apA, asB] at hx ⊢; omega))
  unfold nxT6
  cases hap : apCall {y | y ∈ df2Keps w.K Ps p.R p.eps ∧ df2Phi F.P F.b F.k y ≤ p.c1 * p.rho} ((1 - p.sb) • pt)
      (p.sb * (1 - p.eps)) p.R F.P wmu (1 / (16 * (n : ℝ) ^ 2 * max 1 (4 * p.R ^ 2 * F.P.trace))) with
  | none =>
    rw [hap] at r2
    have hc2 : ¬ σ2.sc 21 < σ2.sc 108 := by rw [k2 21 (by simp), hc.pre.c21, r2]; simp
    refine runs_mono (runs_ifS_f (by decide) (by decide) hc2 (runs_toGuard σ2)) (by unfold kCommit; omega)
      (fun σ3 h3 => ⟨h3.1, Env.Frame.trans FB (Env.Frame.mono h3.2 (by simp) (by simp [ssB]) (by simp))⟩)
  | some mu' =>
    rw [hap] at r2
    obtain ⟨r108, r92⟩ := r2
    have hc2 : σ2.sc 21 < σ2.sc 108 := by rw [k2 21 (by simp), hc.pre.c21, r108]; norm_num
    refine runs_mono (runs_ifS_t (by decide) (by decide) hc2 (runs_nxCommit σ2
      (by rw [F2.1 0 (by decide), F1.1 0 (by decide), hc.pre.nd])
        (by rw [F2.1 2 (by decide), F1.1 2 (by decide), hc.pre.n1])
      (by rw [F2.1 9 (by decide), F1.1 9 (by decide), hc.pre.n9]))) (by unfold kCommit; omega) (fun σ3 h3 => ?_)
    obtain ⟨c23, c2, c3, c4, c5, c6, c24, c7, c25, c8, c26, F3⟩ := h3
    refine ⟨⟨by rw [F3.2.1 22 (by decide), k2 22 (by simp), hc.pre.mode], by rw [c23]; simp, by rw [c2, r92],
      by rw [c3, Env.Frame.mat_eq F2 (by decide), Env.Frame.mat_eq F1 (by decide), hP80],
      by rw [c4, Env.Frame.mat_eq F2 (by decide), Env.Frame.mat_eq F1 (by decide), hS81],
      by rw [c5, Env.Frame.mat_eq F2 (by decide), Env.Frame.mat_eq F1 (by decide), hA82],
      by rw [c6, Env.Frame.vec_eq F2 (by decide), Env.Frame.vec_eq F1 (by decide), hP83],
      by rw [c24, F2.2.1 81 (by decide), k1 81 (by decide), hP81],
      by rw [c7, Env.Frame.vec_eq F2 (by decide), Env.Frame.vec_eq F1 (by decide), hG84],
      by rw [c25, F2.2.1 84 (by decide), k1 84 (by decide), hl84],
      by rw [c8, Env.Frame.vec_eq F2 (by decide), Env.Frame.vec_eq F1 (by decide), h90],
      by rw [c26, F2.2.1 100 (by decide), k1 100 (by decide), h100]⟩,
      Env.Frame.trans FB (Env.Frame.mono F3 (by decide) (by decide) (by decide))⟩

/-- `w_μ = μ - (η Y/((1 - λ) q)) w`, `w = A ξ`. -/
noncomputable def nxWmu (p : Df2OPar) (st : Df2St d) (ξ : Fin d → ℝ) (Y : ℝ) : Fin d → ℝ :=
  st.mu - (p.eta * Y / ((1 - p.lam) * nxQ p ξ Y)) • (st.A *ᵥ ξ)

/-- The steps of `nxC6`. -/
def kC6 (d K2 : ℕ) : ℕ := 13 + (K2 + (kCommit d + 2))

/-- The tests of `df2Next` passed before its first call of AP: the traces of `P'` and `S'`, and the norm of `z`. -/
def NxG1 (p : Df2OPar) (F : NxF d) : Prop :=
  ¬ (d : ℝ) / p.δe < F.P.trace ∧ ¬ (d : ℝ) / p.δe < F.S.trace ∧
    ¬ p.R / p.δe ^ 3 < oNorm (F.S *ᵥ (F.b - (p.eta / 2) • F.G))

/-- The test of `df2Next` passed before its second call of AP: the norm of `w_μ`. -/
def NxG2 (p : Df2OPar) (n : ℕ) (st : Df2St d) (ξ : Fin d → ℝ) (Y : ℝ) : Prop :=
  ¬ p.R + p.eta * Real.sqrt (16 * d * n * p.Le / p.δe) < oNorm (nxWmu p st ξ Y)

/-- The steps of `nxC5`. -/
def kC5 (d K2 : ℕ) : ℕ := d * 44 + 34 + (kC6 d K2 + 2)

open Classical in
/-- The rule of `nxC5`: the second ball, `w_μ` and its test. -/
theorem runs_nxC5 (p : Df2OPar) (n : ℕ) (Ps : PgSp d) (st : Df2St d) (ξ : Fin d → ℝ) (Y : ℝ) (F : NxF d)
    (pt : Fin d → ℝ) (K2 : ℕ) (σ : Env d) (hc : NxCtx p n Ps st ξ Y σ) (hF : NxRep F σ)
    (h85 : σ.sc 85 = F.P.trace) (h87 : σ.vec 87 = pt) (h110 : σ.sc 110 = (1 - p.eps)⁻¹)
    (h112 : σ.sc 112 = p.c1 * p.rho)
    (hAP : NxG2 p n st ξ Y → ApSpec w memRp apV2
      {y | y ∈ df2Keps w.K Ps p.R p.eps ∧ df2Phi F.P F.b F.k y ≤ p.c1 * p.rho} (nxI2 p n Ps F pt (nxWmu p st ξ Y)) K2) :
    Runs df2L w nxC5 σ (kC5 d K2) (fun σ' =>
      ModeRep (nxT5 p n (df2Keps w.K Ps p.R p.eps) F ((1 - p.sb) • pt) (p.sb * (1 - p.eps)) (nxWmu p st ξ Y)) σ' ∧
        Env.Frame σ σ' nsB ssB asB) := by
  obtain ⟨-, p4, p5, -, p7, -, -, p10, -, -, -, -, -, -, p17, p18, -⟩ := hc.pre.par
  refine runs_seq (runs_nx7 σ hc.pre.nd hc.pre.n1 hc.pre.c21 hc.pre.c27) (fun σ1 h1' => ?_)
  obtain ⟨v90, s100, v91, s103, s104, F1⟩ := h1'
  have ew : σ.vec 2 - (σ.sc 7 * σ.sc 31 / (σ.sc 64 * σ.sc 67)) • σ.vec 10 = nxWmu p st ξ Y := by
    rw [hc.pre.rep.2.1, p7, hc.pre.hY, hc.lam, hc.q, hc.pre.hw]; rfl
  have FB1 : Env.Frame σ σ1 nsB ssB asB := Env.Frame.mono F1 (by decide) (by decide) (by decide)
  unfold nxT5
  by_cases ht : p.R + p.eta * Real.sqrt (16 * d * n * p.Le / p.δe) < oNorm (nxWmu p st ξ Y)
  · simp only [ht, ↓reduceIte]
    have hc1 : σ1.sc 104 < σ1.sc 103 := by rw [s104, s103, ew, p17, p7, hc.pre.nn, p5, p4]; exact ht
    refine runs_mono (runs_ifS_t (by decide) (by decide) hc1 (runs_toGuard σ1)) (by unfold kC6; omega)
      (fun σ2 h2 => ⟨h2.1, Env.Frame.trans FB1 (Env.Frame.mono h2.2 (by decide) (by decide) (by decide))⟩)
  · simp only [ht, ↓reduceIte]
    have hc1 : ¬ σ1.sc 104 < σ1.sc 103 := by rw [s104, s103, ew, p17, p7, hc.pre.nn, p5, p4]; exact ht
    refine runs_mono (runs_ifS_f (by decide) (by decide) hc1 (runs_nxC6 p n Ps st ξ Y F pt (nxWmu p st ξ Y) K2 σ1
      (hc.frame F1 (by decide) (by decide) (by decide)) (hF.frame F1 (by decide) (by decide))
      (by rw [F1.2.1 85 (by decide), h85]) (by rw [v90, p18, h87]) (by rw [s100, p18, p10]) (by rw [v91, ew])
      (by rw [F1.2.1 110 (by decide), h110]) (by rw [F1.2.1 112 (by decide), h112]) (hAP ht))) le_rfl
      (fun σ2 h2 => ⟨h2.1, Env.Frame.trans FB1 h2.2⟩)

/-- The steps of `stInit`. -/
def kInit (d : ℕ) : ℕ := d * d * 15 + d * 41 + 45

/-- The steps of `nxC4`. -/
def kC4 (d K2 : ℕ) : ℕ := d * (d * 10 + 9) + d * 27 + 26 + (kC5 d K2 + kInit d + 2)

open Classical in
/-- The rule of `nxC4`: the restart test from the point `pt` of the first call. -/
theorem runs_nxC4 (p : Df2OPar) (n : ℕ) (Ps : PgSp d) (st : Df2St d) (ξ : Fin d → ℝ) (Y : ℝ) (F : NxF d)
    (pt : Fin d → ℝ) (K2 : ℕ) (σ : Env d) (hc : NxCtx p n Ps st ξ Y σ) (hF : NxRep F σ)
    (h85 : σ.sc 85 = F.P.trace) (h87 : σ.vec 87 = pt) (h110 : σ.sc 110 = (1 - p.eps)⁻¹)
    (h112 : σ.sc 112 = p.c1 * p.rho)
    (hAP : NxG2 p n st ξ Y → ApSpec w memRp apV2
      {y | y ∈ df2Keps w.K Ps p.R p.eps ∧ df2Phi F.P F.b F.k y ≤ p.c1 * p.rho} (nxI2 p n Ps F pt (nxWmu p st ξ Y)) K2) :
    Runs df2L w nxC4 σ (kC4 d K2) (fun σ' =>
      ModeRep (nxT4 p n (df2Keps w.K Ps p.R p.eps) st ξ (st.A *ᵥ ξ) Y F pt) σ' ∧ Env.Frame σ σ' nsB ssB asB) := by
  obtain ⟨-, -, -, -, p7, p8, p9, p10, -, p12, -, -, -, -, -, -, -⟩ := hc.pre.par
  obtain ⟨hP80, hS81, hA82, hP83, hP81, hG84, hl84⟩ := hF
  refine runs_seq (runs_nx6 σ hc.pre.nd hc.pre.n1 hc.pre.c19 hc.pre.c21) (fun σ1 h1' => ?_)
  obtain ⟨s96, s98, F1⟩ := h1'
  have FB1 : Env.Frame σ σ1 nsB ssB asB := Env.Frame.mono F1 (by decide) (by decide) (by decide)
  have e96 : σ1.sc 96 = p.eta * (F.l - F.G ⬝ᵥ pt) - 2 * df2Phi F.P F.b F.k pt := by
    rw [s96, p7, hl84, hG84, h87, hP80, hP83, hP81]
  have e98 : σ1.sc 98 = -(p.theta * p.rho) := by rw [s98, p12, p9]
  unfold nxT4
  by_cases ht : p.eta * (F.l - F.G ⬝ᵥ pt) - 2 * df2Phi F.P F.b F.k pt ≤ -(p.theta * p.rho)
  · simp only [ht, ↓reduceIte]
    have hc1 : ¬ σ1.sc 98 < σ1.sc 96 := by rw [e96, e98]; exact not_lt.2 ht
    have n0 : σ1.nat 0 = d := by rw [F1.1 0 (by decide), hc.pre.nd]
    have n2 : σ1.nat 2 = 1 := by rw [F1.1 2 (by decide), hc.pre.n1]
    have n9 : σ1.nat 9 = d * d := by rw [F1.1 9 (by decide), hc.pre.n9]
    refine runs_mono (runs_ifS_f (by decide) (by decide) hc1 (runs_stInit σ1 n0 n2 n9
      (by rw [F1.2.1 21 (by decide), hc.pre.c21]) (by rw [F1.2.1 27 (by decide), hc.pre.c27]))) (by unfold kInit; omega)
      (fun σ2 h2 => ?_)
    obtain ⟨i23, i2, i3, i4, i5, i6, i24, i7, i25, i8, i26, F2⟩ := h2
    have k8 : σ1.sc 8 = p.sig2 := by rw [F1.2.1 8 (by decide), p8]
    refine ⟨⟨by rw [F2.2.1 22 (by decide), F1.2.1 22 (by decide), hc.pre.mode], by rw [i23]; simp [df2Init],
      by rw [i2]; rfl, by rw [i3, k8]; rfl, by rw [i4, k8]; rfl, by rw [i5, k8]; rfl, by rw [i6]; rfl,
      by rw [i24]; rfl, by rw [i7]; rfl, by rw [i25]; rfl, by rw [i8]; rfl,
      by rw [i26, F1.2.1 10 (by decide), p10]; rfl⟩,
      Env.Frame.trans FB1 (Env.Frame.mono F2 (by decide) (by decide) (by decide))⟩
  · simp only [ht, ↓reduceIte]
    have hc1 : σ1.sc 98 < σ1.sc 96 := by rw [e96, e98]; exact not_le.1 ht
    refine runs_mono (runs_ifS_t (by decide) (by decide) hc1 (runs_nxC5 p n Ps st ξ Y F pt K2 σ1
      (hc.frame F1 (by decide) (by decide) (by decide))
      (NxRep.frame ⟨hP80, hS81, hA82, hP83, hP81, hG84, hl84⟩ F1 (by decide) (by decide))
      (by rw [F1.2.1 85 (by decide), h85]) (by rw [Env.Frame.vec_eq F1 (by decide), h87])
      (by rw [F1.2.1 110 (by decide), h110]) (by rw [F1.2.1 112 (by decide), h112]) hAP))
      (by omega) (fun σ2 h2 => ⟨h2.1, Env.Frame.trans FB1 h2.2⟩)

/-- What the first call of AP needs: the read set of `memRm` and its inputs. -/
def nxI1 (p : Df2OPar) (Ps : PgSp d) (st : Df2St d) (F : NxF d) (σ : Env d) : Prop :=
  Iq1 p Ps st σ ∧ σ.vec 8 = st.ctr ∧ σ.sc 26 = st.r ∧ σ.mat 80 = F.P ∧
    σ.vec 86 = F.S *ᵥ (F.b - (p.eta / 2) • F.G) ∧ σ.sc 91 = min 1 (p.alpha * p.rho / 2)

/-- The steps of `nxC3`. -/
def kC3 (d K1 K2 : ℕ) : ℕ := 10 + (K1 + (kC4 d K2 + 2))

open Classical in
/-- The rule of `nxC3`: the constants of the regions, the first call of AP, and its test. -/
theorem runs_nxC3 (p : Df2OPar) (n : ℕ) (Ps : PgSp d) (st : Df2St d) (ξ : Fin d → ℝ) (Y : ℝ) (F : NxF d)
    (K1 K2 : ℕ) (σ : Env d) (hc : NxCtx p n Ps st ξ Y σ) (hF : NxRep F σ) (h85 : σ.sc 85 = F.P.trace)
    (h86 : σ.vec 86 = F.S *ᵥ (F.b - (p.eta / 2) • F.G))
    (hAP1 : ApSpec w memRm apV1 (nxRm p (df2Keps w.K Ps p.R p.eps) st) (nxI1 p Ps st F) K1)
    (hAP2 : ∀ pt, NxG2 p n st ξ Y → ApSpec w memRp apV2
      {y | y ∈ df2Keps w.K Ps p.R p.eps ∧ df2Phi F.P F.b F.k y ≤ p.c1 * p.rho} (nxI2 p n Ps F pt (nxWmu p st ξ Y)) K2) :
    Runs df2L w nxC3 σ (kC3 d K1 K2) (fun σ' =>
      ModeRep (nxT3 p n (df2Keps w.K Ps p.R p.eps) st ξ (st.A *ᵥ ξ) Y F (F.S *ᵥ (F.b - (p.eta / 2) • F.G))) σ' ∧
        Env.Frame σ σ' nsB ssB asB) := by
  obtain ⟨-, -, -, -, -, -, p9, p10, -, -, p13, p14, p15, -, p17, -, -⟩ := hc.pre.par
  refine runs_seq (runs_nx5 σ hc.pre.c19 hc.pre.c27) (fun σ1 h1' => ?_)
  obtain ⟨s110, s111, s112, s91, F1⟩ := h1'
  have k1 : ∀ x ∉ [91, 110, 111, 112], σ1.sc x = σ.sc x := F1.2.1
  have e110 : σ1.sc 110 = (1 - p.eps)⁻¹ := by rw [s110, p10, one_div]
  have e112 : σ1.sc 112 = p.c1 * p.rho := by rw [s112, p14, p9]
  have hI : nxI1 p Ps st F σ1 := by
    obtain ⟨r23, -, r3, -, -, r6, r24, -, -, r8, r26⟩ := hc.pre.rep
    exact ⟨⟨hc.pre.pos.frame F1 (by decide) (by decide), by rw [k1 17 (by decide), p17], e110,
      by rw [k1 19 (by decide), hc.pre.c19], by rw [k1 21 (by decide), hc.pre.c21], by rw [k1 23 (by decide), r23],
      by rw [Env.Frame.mat_eq F1 (by decide), r3], by rw [Env.Frame.vec_eq F1 (by decide), r6],
      by rw [k1 24 (by decide), r24], by rw [s111, p14, p15, p9]⟩,
      by rw [Env.Frame.vec_eq F1 (by decide), r8], by rw [k1 26 (by decide), r26],
      by rw [Env.Frame.mat_eq F1 (by decide), hF.1], by rw [Env.Frame.vec_eq F1 (by decide), h86],
      by rw [s91, p13, p9]⟩
  refine runs_seq (hAP1 σ1 hI (by show σ1.nat 0 = d; rw [F1.1 0 (by decide), hc.pre.nd])
    (by show σ1.nat 2 = 1; rw [F1.1 2 (by decide), hc.pre.n1])) (fun σ2 h2 => ?_)
  obtain ⟨r2, F2⟩ := h2
  dsimp only [apV1] at r2 F2
  obtain ⟨-, e8, e26, e80, e86, e91⟩ := hI
  rw [e8, e26, k1 17 (by decide), p17, e80, e86, e91] at r2
  have FB2 : Env.Frame σ σ2 nsB ssB asB := Env.Frame.trans (Env.Frame.mono F1 (by decide) (by decide) (by decide))
    (Env.Frame.mono F2 (by intro x hx; simp [AP.apN, nsB] at hx ⊢; omega)
      (by intro x hx; simp [AP.apS, memS, ssB] at hx ⊢; omega) (by intro x hx; simp [AP.apA, asB] at hx ⊢; omega))
  have k21 : σ2.sc 21 = 0 := by rw [F2.2.1 21 (by decide), k1 21 (by decide), hc.pre.c21]
  unfold nxT3
  cases hap : apCall (nxRm p (df2Keps w.K Ps p.R p.eps) st) st.ctr st.r p.R F.P (F.S *ᵥ (F.b - (p.eta / 2) • F.G))
      (min 1 (p.alpha * p.rho / 2)) with
  | none =>
    rw [hap] at r2
    have hc2 : ¬ σ2.sc 21 < σ2.sc 92 := by rw [k21, r2]; simp
    refine runs_mono (runs_ifS_f (by decide) (by decide) hc2 (runs_toGuard σ2)) (by unfold kC4; omega)
      (fun σ3 h3 => ⟨h3.1, Env.Frame.trans FB2 (Env.Frame.mono h3.2 (by decide) (by decide) (by decide))⟩)
  | some pt =>
    rw [hap] at r2
    obtain ⟨r92, r87⟩ := r2
    have hc2 : σ2.sc 21 < σ2.sc 92 := by rw [k21, r92]; norm_num
    refine runs_mono (runs_ifS_t (by decide) (by decide) hc2 (runs_nxC4 p n Ps st ξ Y F pt K2 σ2
      ((hc.frame F1 (by decide) (by decide) (by decide)).frame F2 (by intro i hi; simp [AP.apN] at hi ⊢; omega)
        (by intro x hx; simp [AP.apS, memS] at hx ⊢; omega) (by intro a ha; simp [AP.apA] at ha; omega))
      ((hF.frame F1 (by decide) (by decide)).frame F2 (by simp [AP.apS, memS]) (by simp [AP.apA]))
      (by rw [F2.2.1 85 (by decide), k1 85 (by decide), h85]) r87 (by rw [F2.2.1 110 (by decide), e110])
      (by rw [F2.2.1 112 (by decide), e112]) (hAP2 pt))) (by omega)
      (fun σ3 h3 => ⟨h3.1, Env.Frame.trans FB2 h3.2⟩)

/-- The steps of `nxC2`. -/
def kC2 (d K1 K2 : ℕ) : ℕ := d * (d * 10 + 9) + d * 27 + 20 + (kC3 d K1 K2 + 2)

open Classical in
/-- The rule of `nxC2`: `z` and its test. -/
theorem runs_nxC2 (p : Df2OPar) (n : ℕ) (Ps : PgSp d) (st : Df2St d) (ξ : Fin d → ℝ) (Y : ℝ) (F : NxF d)
    (K1 K2 : ℕ) (σ : Env d) (hc : NxCtx p n Ps st ξ Y σ) (hF : NxRep F σ) (h85 : σ.sc 85 = F.P.trace)
    (htP : ¬ (d : ℝ) / p.δe < F.P.trace) (htS : ¬ (d : ℝ) / p.δe < F.S.trace)
    (hAP1 : NxG1 p F → ApSpec w memRm apV1 (nxRm p (df2Keps w.K Ps p.R p.eps) st) (nxI1 p Ps st F) K1)
    (hAP2 : NxG1 p F → ∀ pt, NxG2 p n st ξ Y → ApSpec w memRp apV2
      {y | y ∈ df2Keps w.K Ps p.R p.eps ∧ df2Phi F.P F.b F.k y ≤ p.c1 * p.rho} (nxI2 p n Ps F pt (nxWmu p st ξ Y)) K2) :
    Runs df2L w nxC2 σ (kC2 d K1 K2) (fun σ' =>
      ModeRep (nxT2 p n (df2Keps w.K Ps p.R p.eps) st ξ (st.A *ᵥ ξ) Y F) σ' ∧ Env.Frame σ σ' nsB ssB asB) := by
  obtain ⟨-, p4, -, -, p7, -, -, -, -, -, -, -, -, -, p17, -, -⟩ := hc.pre.par
  refine runs_seq (runs_nx4 σ hc.pre.nd hc.pre.n1 hc.pre.c19 hc.pre.c21) (fun σ1 h1' => ?_)
  obtain ⟨v86, s89, s90, F1⟩ := h1'
  have FB1 : Env.Frame σ σ1 nsB ssB asB := Env.Frame.mono F1 (by decide) (by decide) (by decide)
  have ez : σ.mat 81 *ᵥ (σ.vec 83 - (σ.sc 7 / 2) • σ.vec 84) = F.S *ᵥ (F.b - (p.eta / 2) • F.G) := by
    rw [hF.2.1, hF.2.2.2.1, p7, hF.2.2.2.2.2.1]
  unfold nxT2
  by_cases ht : p.R / p.δe ^ 3 < oNorm (F.S *ᵥ (F.b - (p.eta / 2) • F.G))
  · simp only [ht, ↓reduceIte]
    have hc1 : σ1.sc 90 < σ1.sc 89 := by rw [s90, s89, ez, p17, p4]; exact ht
    refine runs_mono (runs_ifS_t (by decide) (by decide) hc1 (runs_toGuard σ1)) (by unfold kC3; omega)
      (fun σ2 h2 => ⟨h2.1, Env.Frame.trans FB1 (Env.Frame.mono h2.2 (by decide) (by decide) (by decide))⟩)
  · simp only [ht, ↓reduceIte]
    have hc1 : ¬ σ1.sc 90 < σ1.sc 89 := by rw [s90, s89, ez, p17, p4]; exact ht
    refine runs_mono (runs_ifS_f (by decide) (by decide) hc1 (runs_nxC3 p n Ps st ξ Y F K1 K2 σ1
      (hc.frame F1 (by decide) (by decide) (by decide)) (hF.frame F1 (by decide) (by decide))
      (by rw [F1.2.1 85 (by decide), h85]) (by rw [v86, ez]) (hAP1 ⟨htP, htS, ht⟩) (hAP2 ⟨htP, htS, ht⟩))) le_rfl
      (fun σ2 h2 => ⟨h2.1, Env.Frame.trans FB1 h2.2⟩)

/-- The steps of `nxC1`. -/
def kC1 (d K1 K2 : ℕ) : ℕ := d * d * 79 + d * 92 + 70 + (d * 16 + 12 + (kC2 d K1 K2 + 4))

open Classical in
/-- The rule of `nxC1`: the new fields, their traces and the test on the traces. -/
theorem runs_nxC1 (p : Df2OPar) (n : ℕ) (Ps : PgSp d) (st : Df2St d) (ξ : Fin d → ℝ) (Y : ℝ) (F : NxF d)
    (K1 K2 : ℕ) (σ : Env d) (hFd : F = nxFields p st ξ (st.A *ᵥ ξ) Y) (hc : NxCtx p n Ps st ξ Y σ)
    (h15 : σ.vec 15 = st.P *ᵥ (st.A *ᵥ ξ)) (h65 : σ.sc 65 = nxC p Y) (h66 : σ.sc 66 = 1 - nxC p Y)
    (hAP1 : NxG1 p F → ApSpec w memRm apV1 (nxRm p (df2Keps w.K Ps p.R p.eps) st) (nxI1 p Ps st F) K1)
    (hAP2 : NxG1 p F → ∀ pt, NxG2 p n st ξ Y → ApSpec w memRp apV2
      {y | y ∈ df2Keps w.K Ps p.R p.eps ∧ df2Phi F.P F.b F.k y ≤ p.c1 * p.rho} (nxI2 p n Ps F pt (nxWmu p st ξ Y)) K2) :
    Runs df2L w nxC1 σ (kC1 d K1 K2) (fun σ' =>
      ModeRep (nxT1 p n (df2Keps w.K Ps p.R p.eps) st ξ (st.A *ᵥ ξ) Y F) σ' ∧ Env.Frame σ σ' nsB ssB asB) := by
  obtain ⟨-, p4, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := hc.pre.par
  refine runs_seq (runs_nx2 p st ξ (st.A *ᵥ ξ) Y σ hc.pre.nd hc.pre.n1 hc.pre.n9 hc.pre.c19 hc.pre.c21 hc.pre.c27
    hc.pre.rep hc.pre.xi hc.pre.hw h15 hc.pre.hY hc.lam h65 h66 hc.q) (fun σ1 h1' => ?_)
  obtain ⟨hF1, F1⟩ := h1'
  rw [← hFd] at hF1
  have FB1 : Env.Frame σ σ1 nsB ssB asB := Env.Frame.mono F1 (by decide)
    (by intro x hx; simp [ssB] at hx ⊢; omega) (by decide)
  have hc1 : NxCtx p n Ps st ξ Y σ1 := hc.frame F1 (by decide) (by decide) (by decide)
  refine runs_seq (runs_nx3 σ1 hc1.pre.nd hc1.pre.n1) (fun σ2 h2 => ?_)
  obtain ⟨s85, s86, s87, F2⟩ := h2
  have FB2 : Env.Frame σ σ2 nsB ssB asB := Env.Frame.trans FB1 (Env.Frame.mono F2 (by decide) (by decide) (by decide))
  have e85 : σ2.sc 85 = F.P.trace := by rw [s85, hF1.1]
  have e86 : σ2.sc 86 = F.S.trace := by rw [s86, hF1.2.1]
  have e87 : σ2.sc 87 = (d : ℝ) / p.δe := by rw [s87, F1.2.1 4 (by decide), p4]
  unfold nxT1
  by_cases h1t : (d : ℝ) / p.δe < F.P.trace
  · simp only [h1t, true_or, ↓reduceIte]
    have hc1' : σ2.sc 87 < σ2.sc 85 := by rw [e87, e85]; exact h1t
    refine runs_mono (runs_ifS_t (by decide) (by decide) hc1' (runs_toGuard σ2)) (by omega)
      (fun σ3 h3 => ⟨h3.1, Env.Frame.trans FB2 (Env.Frame.mono h3.2 (by decide) (by decide) (by decide))⟩)
  · have hc1' : ¬ σ2.sc 87 < σ2.sc 85 := by rw [e87, e85]; exact h1t
    by_cases h2t : (d : ℝ) / p.δe < F.S.trace
    · simp only [h2t, or_true, ↓reduceIte]
      have hc2' : σ2.sc 87 < σ2.sc 86 := by rw [e87, e86]; exact h2t
      refine runs_mono (runs_ifS_f (by decide) (by decide) hc1' (runs_ifS_t (by decide) (by decide) hc2'
        (runs_toGuard σ2))) (by omega)
        (fun σ3 h3 => ⟨h3.1, Env.Frame.trans FB2 (Env.Frame.mono h3.2 (by decide) (by decide) (by decide))⟩)
    · simp only [h1t, h2t, or_self, ↓reduceIte]
      have hc2' : ¬ σ2.sc 87 < σ2.sc 86 := by rw [e87, e86]; exact h2t
      refine runs_mono (runs_ifS_f (by decide) (by decide) hc1' (runs_ifS_f (by decide) (by decide) hc2'
        (runs_nxC2 p n Ps st ξ Y F K1 K2 σ2 (hc1.frame F2 (by decide) (by decide) (by decide))
          (hF1.frame F2 (by decide) (by decide)) e85 h1t h2t hAP1 hAP2))) (by omega)
        (fun σ3 h3 => ⟨h3.1, Env.Frame.trans FB2 h3.2⟩)

/-- The first test of `df2Next` passed: `a = 1 - c > 0` and `q > 0`. -/
def NxG0 (p : Df2OPar) (ξ : Fin d → ℝ) (Y : ℝ) : Prop := 0 < 1 - nxC p Y ∧ 0 < nxQ p ξ Y

/-- The rules of the two calls of AP in `df2Next` from the state `st`, the draw `ξ` and `Y`, within `K1` and `K2`
steps, when `df2Next` reaches them: after the tests on `a`, `q` (`NxG0`), on the traces and on `z` (`NxG1`), and for
the second call after the test on `w_μ` (`NxG2`). -/
def ApRules (w : World d) (p : Df2OPar) (n : ℕ) (Ps : PgSp d) (st : Df2St d) (ξ : Fin d → ℝ) (Y : ℝ) (K1 K2 : ℕ) :
    Prop :=
  (NxG0 p ξ Y → NxG1 p (nxFields p st ξ (st.A *ᵥ ξ) Y) →
    ApSpec w memRm apV1 (nxRm p (df2Keps w.K Ps p.R p.eps) st) (nxI1 p Ps st (nxFields p st ξ (st.A *ᵥ ξ) Y)) K1) ∧
  (NxG0 p ξ Y → NxG1 p (nxFields p st ξ (st.A *ᵥ ξ) Y) → ∀ pt, NxG2 p n st ξ Y →
    ApSpec w memRp apV2 {y | y ∈ df2Keps w.K Ps p.R p.eps ∧ df2Phi (nxFields p st ξ (st.A *ᵥ ξ) Y).P
      (nxFields p st ξ (st.A *ᵥ ξ) Y).b (nxFields p st ξ (st.A *ᵥ ξ) Y).k y ≤ p.c1 * p.rho}
      (nxI2 p n Ps (nxFields p st ξ (st.A *ᵥ ξ) Y) pt (nxWmu p st ξ Y)) K2)

/-- The steps of `nextCode`. -/
def kNext (d K1 K2 : ℕ) : ℕ := d * (d * 10 + 9) + 4 + ((d * 9 + 4) + 8) + (kC1 d K1 K2 + 4)

open Classical in
/-- The rule of `nextCode`: `df2Next`, with the two calls of AP by their rules. -/
theorem runs_nextCode (p : Df2OPar) (n : ℕ) (Ps : PgSp d) (st : Df2St d) (ξ : Fin d → ℝ) (Y : ℝ) (K1 K2 : ℕ)
    (σ : Env d) (hc : NxPre p n Ps st ξ Y σ) (hAP : ApRules w p n Ps st ξ Y K1 K2) :
    Runs df2L w nextCode σ (kNext d K1 K2) (fun σ' =>
      ModeRep (df2Next p n (df2Keps w.K Ps p.R p.eps) st ξ (st.A *ᵥ ξ) Y) σ' ∧ Env.Frame σ σ' nsB ssB asB) := by
  refine runs_seq (runs_nx1 p st.P ξ (st.A *ᵥ ξ) Y σ hc.nd hc.n1 hc.c27 hc.par hc.rep.2.2.1 hc.xi hc.hw hc.hY)
    (fun σ1 h1' => ?_)
  obtain ⟨v15, s64, s65, s66, s67, F1⟩ := h1'
  have FB1 : Env.Frame σ σ1 nsB ssB asB := Env.Frame.mono F1 (by decide) (by decide) (by decide)
  have hc1 : NxCtx p n Ps st ξ Y σ1 := ⟨hc.frame F1 (by decide) (by decide) (by decide), s64, s67⟩
  have k21 : σ1.sc 21 = 0 := by rw [F1.2.1 21 (by decide), hc.c21]
  rw [df2Next_eq]
  by_cases ha : 1 - nxC p Y ≤ 0
  · simp only [ha, true_or, ↓reduceIte]
    have hc1' : ¬ σ1.sc 21 < σ1.sc 66 := by rw [k21, s66]; exact not_lt.2 ha
    refine runs_mono (runs_ifS_f (by decide) (by decide) hc1' (runs_toGuard σ1)) (by omega)
      (fun σ2 h2 => ⟨h2.1, Env.Frame.trans FB1 (Env.Frame.mono h2.2 (by decide) (by decide) (by decide))⟩)
  · have hc1' : σ1.sc 21 < σ1.sc 66 := by rw [k21, s66]; exact not_le.1 ha
    by_cases hq : nxQ p ξ Y ≤ 0
    · simp only [hq, or_true, ↓reduceIte]
      have hc2' : ¬ σ1.sc 21 < σ1.sc 67 := by rw [k21, s67]; exact not_lt.2 hq
      refine runs_mono (runs_ifS_t (by decide) (by decide) hc1' (runs_ifS_f (by decide) (by decide) hc2'
        (runs_toGuard σ1))) (by omega)
        (fun σ2 h2 => ⟨h2.1, Env.Frame.trans FB1 (Env.Frame.mono h2.2 (by decide) (by decide) (by decide))⟩)
    · simp only [ha, hq, or_self, ↓reduceIte]
      have hc2' : σ1.sc 21 < σ1.sc 67 := by rw [k21, s67]; exact not_le.1 hq
      refine runs_mono (runs_ifS_t (by decide) (by decide) hc1' (runs_ifS_t (by decide) (by decide) hc2'
        (runs_nxC1 p n Ps st ξ Y _ K1 K2 σ1 rfl hc1 v15 s65 s66 (hAP.1 ⟨not_le.1 ha, not_le.1 hq⟩)
          (hAP.2 ⟨not_le.1 ha, not_le.1 hq⟩)))) (by omega)
        (fun σ2 h2 => ⟨h2.1, Env.Frame.trans FB1 h2.2⟩)


/-- `Y` of a round of DF2 from the state `st`, the draw `ξ`, the loss `ft`, the noise `nt` and the dither `ζ`. -/
noncomputable def df2Y (p : Df2OPar) (K : Set (E d)) (Ps : PgSp d) (ft : E d → ℝ) (nt : ℝ) (st : Df2St d)
    (ξ : Fin d → ℝ) (ζ : ℝ) : ℝ :=
  df2Pt p K Ps st ξ * (ft (df2Pnt p K Ps st ξ) + nt + ζ) / 2 + 2 * (df2Pt p K Ps st ξ - 1) / p.eps

open Classical in
theorem df2Round_run (p : Df2OPar) (n : ℕ) (K : Set (E d)) (Ps : PgSp d) (ft : E d → ℝ) (nt : ℝ) (ξ : Fin d → ℝ)
    (ζ : ℝ) (st : Df2St d) : (df2Round p n K Ps ft nt ξ ζ (.run st)).2 =
      if df2Pnt p K Ps st ξ ∈ K then df2Next p n (df2Keps K Ps p.R p.eps) st ξ (st.A *ᵥ ξ) (df2Y p K Ps ft nt st ξ ζ)
      else .off := by
  unfold df2Round; dsimp only; rw [apply_ite Prod.snd]; rfl

/-- The steps of part B. -/
def kDf2B (d K1 K2 : ℕ) : ℕ := kNext d K1 K2 + 16

open Classical in
/-- The rule of part B, in every mode: after part A and the play (the observation in the scalar `32`), the next mode
of the round. -/
theorem runs_df2B (p : Df2OPar) (n : ℕ) (Ps : PgSp d) (ft : E d → ℝ) (nt : ℝ) (ξ : Fin d → ℝ) (ζ : ℝ)
    (m : Df2Mode d) (K1 K2 : ℕ) (σ : Env d) (hd : σ.nat 0 = d) (h1 : σ.nat 2 = 1) (h9 : σ.nat 9 = d * d)
    (hn : σ.nat 1 = n) (h19 : σ.sc 19 = 1 / 2) (h20 : σ.sc 20 = 3 / 2) (h21 : σ.sc 21 = 0) (h27 : σ.sc 27 = 1)
    (hpar : ParRep p σ) (hP : PosRep Ps σ) (hm : ModeRep m σ) (hA : AOut p w.K Ps ξ m σ) (hξ : σ.vec 9 = ξ)
    (hζ : σ.sc 29 / 2 = ζ) (h14 : WithLp.toLp 2 (σ.vec 14) = (df2Round p n w.K Ps ft nt ξ ζ m).1)
    (hO : σ.sc 32 = ft (WithLp.toLp 2 (σ.vec 14)) + nt)
    (hAP : ∀ st, m = .run st → ApRules w p n Ps st ξ (df2Y p w.K Ps ft nt st ξ ζ) K1 K2) :
    Runs df2L w df2B σ (kDf2B d K1 K2) (fun σ' =>
      ModeRep (df2Round p n w.K Ps ft nt ξ ζ m).2 σ' ∧ Env.Frame σ σ' nsB ssB asB) := by
  have FR : Env.Frame σ σ nsB ssB asB := Env.Frame.refl _ _ _ _
  cases m with
  | off =>
    have hc : σ.sc 22 < σ.sc 19 := by rw [show σ.sc 22 = 0 from hm, h19]; norm_num
    exact runs_mono (runs_ifS_t (by decide) (by decide) hc (runs_skip σ)) (by unfold kDf2B; omega)
      (fun σ' e => by subst e; exact ⟨hm, FR⟩)
  | guard =>
    have hc1 : ¬ σ.sc 22 < σ.sc 19 := by rw [show σ.sc 22 = 1 from hm, h19]; norm_num
    have hc2 : σ.sc 22 < σ.sc 20 := by rw [show σ.sc 22 = 1 from hm, h20]; norm_num
    have h28 : σ.sc 28 = if pgMu Ps + pgOp Ps 0 ∈ w.K then 1 else 0 := hA
    by_cases hK : pgMu Ps + pgOp Ps 0 ∈ w.K
    · have hc3 : σ.sc 21 < σ.sc 28 := by rw [h21, h28]; simp only [hK, ↓reduceIte]; norm_num
      refine runs_mono (runs_ifS_f (by decide) (by decide) hc1 (runs_ifS_t (by decide) (by decide) hc2
        (runs_ifS_t (by decide) (by decide) hc3 (runs_skip σ)))) (by unfold kDf2B; omega) (fun σ' e => ?_)
      subst e
      refine ⟨?_, FR⟩
      simp only [df2Round, hK, ↓reduceIte]
      exact hm
    · have hc3 : ¬ σ.sc 21 < σ.sc 28 := by rw [h21, h28]; simp only [hK, ↓reduceIte]; norm_num
      refine runs_mono (runs_ifS_f (by decide) (by decide) hc1 (runs_ifS_t (by decide) (by decide) hc2
        (runs_ifS_f (by decide) (by decide) hc3 (runs_sconst (by decide) 0)))) (by unfold kDf2B; omega) (fun σ' e => ?_)
      subst e
      refine ⟨?_, Env.Frame.setSc FR (by decide) _⟩
      simp only [df2Round, hK, ↓reduceIte]
      simp [ModeRep]
  | run st =>
    obtain ⟨hm22, hst⟩ := hm
    obtain ⟨h10, h30, h28⟩ := hA
    have hc1 : ¬ σ.sc 22 < σ.sc 19 := by rw [hm22, h19]; norm_num
    have hc2 : ¬ σ.sc 22 < σ.sc 20 := by rw [hm22, h20]; norm_num
    rw [df2Round_run]
    by_cases hK : df2Pnt p w.K Ps st ξ ∈ w.K
    · simp only [hK, ↓reduceIte]
      have hc3 : σ.sc 21 < σ.sc 28 := by rw [h21, h28]; simp [hK]
      refine runs_mono (runs_ifS_f (by decide) (by decide) hc1 (runs_ifS_f (by decide) (by decide) hc2
        (runs_ifS_t (by decide) (by decide) hc3 (runs_seq (K₂ := kNext d K1 K2) (runs_yCode σ h19 h27)
          (fun σ1 h1' => ?_)))))
        (by unfold kDf2B; omega) (fun σ' h => h)
      obtain ⟨s31, F1⟩ := h1'
      have hx : (df2Round p n w.K Ps ft nt ξ ζ (.run st)).1 = df2Pnt p w.K Ps st ξ := by
        rw [df2Round_fst]; simp [hK]
      have hY : σ1.sc 31 = df2Y p w.K Ps ft nt st ξ ζ := by
        rw [s31, h30, hO, h14, hx, ← hζ, hpar.2.2.2.2.2.2.2.1]; unfold df2Y; ring
      have hc : NxPre p n Ps st ξ (df2Y p w.K Ps ft nt st ξ ζ) σ1 :=
        NxPre.frameY (Y := σ.sc 31) ⟨hd, h1, h9, hn, h19, h21, h27, hpar, hP, hst, hm22, hξ, h10, rfl⟩ F1
          (by decide) (by decide) (by decide) hY
      exact runs_mono (runs_nextCode p n Ps st ξ _ K1 K2 σ1 hc (hAP st rfl)) le_rfl
        (fun σ2 h2 => ⟨h2.1, Env.Frame.trans (Env.Frame.mono F1 (by decide) (by decide) (by decide)) h2.2⟩)
    · simp only [hK, ↓reduceIte]
      have hc3 : ¬ σ.sc 21 < σ.sc 28 := by rw [h21, h28]; simp [hK]
      refine runs_mono (runs_ifS_f (by decide) (by decide) hc1 (runs_ifS_f (by decide) (by decide) hc2
        (runs_ifS_f (by decide) (by decide) hc3 (runs_sconst (by decide) 0)))) (by unfold kDf2B; omega)
        (fun σ' e => ?_)
      subst e
      exact ⟨by simp [ModeRep], Env.Frame.setSc FR (by decide) _⟩

/-! ## A round in the form of `prog_spec`

The invariant `RndI` at the start of round `t` and `RndJ` before its play, for a mode `m`, the parameters `p`, the
position `Ps` and the offset `N0` of the draws of the rounds; `runs_rndA` is the rule of part `A`, `runs_rndB` the
rule of part `B` after the play. -/

theorem ModeRep.congr {m : Df2Mode d} {σ σ' : Env d} (h : ModeRep m σ)
    (hs : ∀ x ∈ [22, 23, 24, 25, 26], σ'.sc x = σ.sc x) (ha : ∀ a ∈ [2, 3, 4, 5, 6, 7, 8], σ'.arr a = σ.arr a) :
    ModeRep m σ' := by
  have hv : ∀ a ∈ [2, 3, 4, 5, 6, 7, 8], σ'.vec a = σ.vec a := fun a h => by unfold Env.vec; rw [ha a h]
  have hM : ∀ a ∈ [2, 3, 4, 5, 6, 7, 8], σ'.mat a = σ.mat a := fun a h => by unfold Env.mat; rw [ha a h]
  cases m with
  | off => show σ'.sc 22 = 0; rw [hs 22 (by simp)]; exact h
  | guard => show σ'.sc 22 = 1; rw [hs 22 (by simp)]; exact h
  | run st =>
    obtain ⟨h22, t23, t2, t3, t4, t5, t6, t24, t7, t25, t8, t26⟩ := h
    exact ⟨by rw [hs 22 (by simp), h22], by rw [hs 23 (by simp), t23], by rw [hv 2 (by simp), t2],
      by rw [hM 3 (by simp), t3], by rw [hM 4 (by simp), t4], by rw [hM 5 (by simp), t5], by rw [hv 6 (by simp), t6],
      by rw [hs 24 (by simp), t24], by rw [hv 7 (by simp), t7], by rw [hs 25 (by simp), t25],
      by rw [hv 8 (by simp), t8], by rw [hs 26 (by simp), t26]⟩

open Classical in
theorem AOut.congr {p : Df2OPar} {K : Set (E d)} {Ps : PgSp d} {ξ : Fin d → ℝ} {m : Df2Mode d} {σ σ' : Env d}
    (h : AOut p K Ps ξ m σ) (hs : ∀ x ∈ [28, 30], σ'.sc x = σ.sc x) (ha : σ'.arr 10 = σ.arr 10) :
    AOut p K Ps ξ m σ' := by
  cases m with
  | off => trivial
  | guard => show σ'.sc 28 = _; rw [hs 28 (by simp)]; exact h
  | run st =>
    obtain ⟨h10, h30, h28⟩ := h
    exact ⟨by rw [show σ'.vec 10 = σ.vec 10 by unfold Env.vec; rw [ha]]; exact h10, by rw [hs 30 (by simp), h30],
      by rw [hs 28 (by simp), h28]⟩

/-- What holds at the start of round `t`: `d, n, 1, d²` in the naturals `0, 1, 2, 9`, the parameters, the position,
the mode `m`, and the `N0 + t (d + 1)` draws read. -/
def RndI (n : ℕ) (p : Df2OPar) (Ps : PgSp d) (N0 t : ℕ) (m : Df2Mode d) (σ : Env d) : Prop :=
  σ.nat 0 = d ∧ σ.nat 1 = n ∧ σ.nat 2 = 1 ∧ σ.nat 9 = d * d ∧ ParRep p σ ∧ PosRep Ps σ ∧ ModeRep m σ ∧
    σ.draws = N0 + t * (d + 1)

open Classical in
/-- What holds before the play of round `t`: `RndI` with the draws of the round read, the constants, what part `A`
leaves for part `B`, the draws `ξ_t`, `g = 2 ζ_t` in the array `9` and the scalar `29`, the point of the round in the
array `14`. -/
def RndJ (w : World d) (n : ℕ) (p : Df2OPar) (Ps : PgSp d) (N0 t : ℕ) (m : Df2Mode d) (σ : Env d) : Prop :=
  σ.nat 0 = d ∧ σ.nat 1 = n ∧ σ.nat 2 = 1 ∧ σ.nat 9 = d * d ∧ ParRep p σ ∧ PosRep Ps σ ∧ ModeRep m σ ∧
    CstRep σ ∧ AOut p w.K Ps (df2oXi N0 w.gs t) m σ ∧ σ.vec 9 = df2oXi N0 w.gs t ∧
    σ.sc 29 / 2 = df2oZeta d N0 w.gs t ∧
    WithLp.toLp 2 (σ.vec 14) =
      (df2Round p n w.K Ps (w.f t) (w.noise t) (df2oXi N0 w.gs t) (df2oZeta d N0 w.gs t) m).1 ∧
    σ.draws = N0 + (t + 1) * (d + 1)

open Classical in
/-- The rule of part `A` of round `t`. -/
theorem runs_rndA (n : ℕ) (p : Df2OPar) (Ps : PgSp d) (N0 t : ℕ) (m : Df2Mode d) (σ : Env d)
    (hI : RndI n p Ps N0 t m σ) :
    Runs df2L w df2A σ (kDf2A d p.j) (fun σ' => RndJ w n p Ps N0 t m σ' ∧ σ'.nat 6 = σ.nat 6 ∧
      σ'.rounds = σ.rounds ∧ WithLp.toLp 2 (σ'.vec 14) =
        (df2Round p n w.K Ps (w.f t) (w.noise t) (df2oXi N0 w.gs t) (df2oZeta d N0 w.gs t) m).1) := by
  obtain ⟨hd, hn, h1, h9, hpar, hP, hm, hdr⟩ := hI
  refine runs_mono (runs_df2A Ps p m σ hd h1 hP hpar hm) le_rfl (fun σ' h => ?_)
  obtain ⟨v9, s29, dr, h14, hA, cst, F⟩ := h
  have Fn : ∀ i, i ∉ [3, 4, 5, 8] → σ'.nat i = σ.nat i := F.1
  have Fs : ∀ x, x ∉ [19, 20, 21] ++ List.range' 27 33 → σ'.sc x = σ.sc x := F.2.1
  have Fa : ∀ a, a ∉ [9, 10, 11, 12, 13, 14] → σ'.arr a = σ.arr a := F.2.2.1
  have hξ : σ'.vec 9 = df2oXi N0 w.gs t := by rw [v9, hdr]; rfl
  have hζ : σ'.sc 29 / 2 = df2oZeta d N0 w.gs t := by rw [s29, hdr]; rfl
  have h14' := h14 n (w.f t) (w.noise t) (df2oZeta d N0 w.gs t)
  rw [hξ] at h14' hA
  refine ⟨⟨by rw [Fn 0 (by decide), hd], by rw [Fn 1 (by decide), hn], by rw [Fn 2 (by decide), h1],
    by rw [Fn 9 (by decide), h9], (hpar.frame F (by decide) (by decide) : ParRep p { σ' with draws := σ.draws }),
    (hP.frame F (by decide) (by decide) : PosRep Ps { σ' with draws := σ.draws }),
    ModeRep.congr hm (fun x hx => Fs x (by revert x; decide)) (fun a ha => Fa a (by revert a; decide)), cst, hA,
    hξ, hζ, h14', by rw [dr, hdr]; ring⟩, Fn 6 (by decide), F.2.2.2.2.1, h14'⟩

open Classical in
/-- The rule of part `B` of round `t`, after the play: `RndI` at round `t + 1` in the next mode. The two calls of AP
in run mode by their rules (`ApRules`). -/
theorem runs_rndB (n : ℕ) (p : Df2OPar) (Ps : PgSp d) (N0 t : ℕ) (m : Df2Mode d) (K1 K2 : ℕ) (σ : Env d)
    (hJ : RndJ w n p Ps N0 t m σ) (hr : σ.rounds = t)
    (hAP : ∀ st, m = .run st → ApRules w p n Ps st (df2oXi N0 w.gs t)
      (df2Y p w.K Ps (w.f t) (w.noise t) st (df2oXi N0 w.gs t) (df2oZeta d N0 w.gs t)) K1 K2) :
    Runs df2L w df2B (σ.afterPlay w 32 14) (kDf2B d K1 K2) (fun σ' =>
      RndI n p Ps N0 (t + 1)
        (df2Round p n w.K Ps (w.f t) (w.noise t) (df2oXi N0 w.gs t) (df2oZeta d N0 w.gs t) m).2 σ' ∧
      σ'.nat 6 = σ.nat 6 ∧ σ'.rounds = t + 1) := by
  obtain ⟨hd, hn, h1, h9, hpar, hP, hm, ⟨c19, c20, c21, c27⟩, hA, hξ, hζ, h14, hdr⟩ := hJ
  set σp := σ.afterPlay w 32 14 with hσp
  have ps : ∀ x, x ≠ 32 → σp.sc x = σ.sc x := fun x hx => by simp [σp, Env.afterPlay, hx]
  have Fq := Env.Frame.setSc (Env.Frame.refl σ [] [32] []) (x := 32) (by simp)
    (w.f σ.rounds (WithLp.toLp 2 (σ.vec 14)) + w.noise σ.rounds)
  have hparq := hpar.frame Fq (by simp) (by simp)
  have hparp : ParRep p σp := hparq
  have hPq := hP.frame Fq (by simp) (by simp)
  have hPp : PosRep Ps σp := hPq
  have hmp : ModeRep m σp := ModeRep.congr hm (fun x hx => ps x (by revert x; decide)) (fun _ _ => rfl)
  have hAp : AOut p w.K Ps (df2oXi N0 w.gs t) m σp := AOut.congr hA (fun x hx => ps x (by revert x; decide)) rfl
  have hO : σp.sc 32 = w.f t (WithLp.toLp 2 (σp.vec 14)) + w.noise t := by
    simp only [σp, Env.afterPlay, Env.setSc_sc, ↓reduceIte, hr]; rfl
  refine runs_mono (runs_df2B p n Ps (w.f t) (w.noise t) (df2oXi N0 w.gs t) (df2oZeta d N0 w.gs t) m K1 K2 σp hd h1
    h9 hn (by rw [ps 19 (by decide), c19]) (by rw [ps 20 (by decide), c20]) (by rw [ps 21 (by decide), c21])
    (by rw [ps 27 (by decide), c27]) hparp hPp hmp hAp hξ (by rw [ps 29 (by decide), hζ]) h14 hO hAP) le_rfl
    (fun σ' h => ?_)
  obtain ⟨hm', F⟩ := h
  have Fn : ∀ i, i ∉ nsB → σ'.nat i = σ.nat i := F.1
  refine ⟨⟨by rw [Fn 0 (by decide), hd], by rw [Fn 1 (by decide), hn], by rw [Fn 2 (by decide), h1],
    by rw [Fn 9 (by decide), h9], hparp.frame F (by decide) (fun x hx => by simp [ssB] at hx; omega),
    hPp.frame F (by simp [asB]) (by simp [asB]), hm', by rw [F.2.2.2.1]; exact hdr⟩, Fn 6 (by decide),
    by rw [F.2.2.2.2.1]; show σ.rounds + 1 = _; rw [hr]⟩

/-! ## The mode before round `0` -/

open SI in
/-- The mode before round `0`, from the answer of PG in the scalar `28`: off if PG found no position (the arrays `0`,
`1` then cleared) or if `1/2 < ε`, else the start of an epoch (`stInit`). -/
def mode0Code : Cmd :=
  .seq (sprog df2L [const 19 (1 / 2), const 21 0, const 27 1]) <|
    ifS df2L 21 28 (ifS df2L 19 10 (sconst df2L 22 0) (.seq stInit (sconst df2L 22 2)))
      (.seq (vfill df2L 0 2 3 0 21) (.seq (mfill df2L 9 2 3 1 21) (sconst df2L 22 0)))

open Classical in
/-- The mode before round `0` from the answer `pos` of PG. -/
noncomputable def df2Mode0Of (p : Df2OPar) (d : ℕ) : Option (PgSp d) → Df2Mode d
  | none => .off
  | some _ => if 1 / 2 < p.eps then .off else .run (df2Init p d)

theorem df2oMode0_eq (d n : ℕ) (r0 R0 δ : ℝ) (w : World d) :
    df2oMode0 d n r0 R0 δ w = df2Mode0Of (df2oPar d n δ) d (df2oPos d n r0 R0 δ w) := by
  unfold df2oMode0 df2Mode0Of; cases df2oPos d n r0 R0 δ w <;> rfl

/-- The steps of `mode0Code`. -/
def kMode0 (d : ℕ) : ℕ := 3 + (2 + (d * d * 15 + d * 41 + 45 + 1) + (d * 5 + 3 + (d * d * 5 + 3 + 1)))

open Classical in
/-- The rule of `mode0Code`: the position `pos.getD 0` in the arrays `0`, `1` and the mode `df2Mode0Of p d pos`. -/
theorem runs_mode0 (p : Df2OPar) (pos : Option (PgSp d)) (σ : Env d) (hd : σ.nat 0 = d) (h1 : σ.nat 2 = 1)
    (h9 : σ.nat 9 = d * d) (hpar : ParRep p σ) (hnone : pos = none → σ.sc 28 = 0)
    (hsome : ∀ P, pos = some P → σ.sc 28 = 1 ∧ σ.vec 0 = (fun i => pgMu P i) ∧ σ.mat 1 = pgMat P) :
    Runs df2L w mode0Code σ (kMode0 d) (fun σ' => PosRep (pos.getD 0) σ' ∧ ModeRep (df2Mode0Of p d pos) σ' ∧
      Env.Frame σ σ' [3, 5] [19, 21, 22, 23, 24, 25, 26, 27, 56, 57] [0, 1, 2, 3, 4, 5, 6, 7, 8]) := by
  let l : List SI := [SI.const 19 (1 / 2), SI.const 21 0, SI.const 27 1]
  refine runs_mono (K := sCost l + (kMode0 d - 3))
    (runs_seq_eq (runs_sprog (L := df2L) (w := w) l (by decide) σ) ?_)
    (by simp only [l, sCost, List.map, SI.cost, List.sum_cons, List.sum_nil]; unfold kMode0; omega) (fun σ' h => h)
  set σ1 : Env d := { σ with sc := sEval σ.nat l σ.sc }
  have F1 : Env.Frame σ σ1 [] [19, 21, 27] [] := ⟨fun _ _ => rfl, fun x hx => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    simp only [σ1, l, sEval, List.foldl, SI.step, SI.dst, SI.val]
    simp [hx.1, hx.2.1, hx.2.2], fun _ _ => rfl, rfl, rfl, rfl⟩
  have s19 : σ1.sc 19 = 1 / 2 := by simp [σ1, l, sEval, SI.step, SI.dst, SI.val]
  have s21 : σ1.sc 21 = 0 := by simp [σ1, l, sEval, SI.step, SI.dst, SI.val]
  have s27 : σ1.sc 27 = 1 := by simp [σ1, l, sEval, SI.step, SI.dst, SI.val]
  have e28 : σ1.sc 28 = σ.sc 28 := F1.2.1 28 (by decide)
  have e10 : σ1.sc 10 = p.eps := by rw [F1.2.1 10 (by decide)]; exact hpar.2.2.2.2.2.2.2.1
  have e8 : σ1.sc 8 = p.sig2 := by rw [F1.2.1 8 (by decide)]; exact hpar.2.2.2.2.2.1
  have hd1 : σ1.nat 0 = d := hd
  have h11 : σ1.nat 2 = 1 := h1
  have h91 : σ1.nat 9 = d * d := h9
  have Fend : ∀ σ' (ns ss as : List ℕ), Env.Frame σ1 σ' ns ss as → (∀ i ∈ ns, i ∈ [3, 5]) →
      (∀ x ∈ ss, x ∈ [19, 21, 22, 23, 24, 25, 26, 27, 56, 57]) → (∀ a ∈ as, a ∈ [0, 1, 2, 3, 4, 5, 6, 7, 8]) →
      Env.Frame σ σ' [3, 5] [19, 21, 22, 23, 24, 25, 26, 27, 56, 57] [0, 1, 2, 3, 4, 5, 6, 7, 8] :=
    fun σ' ns ss as F hn hs ha =>
      Env.Frame.trans (Env.Frame.mono F1 (by decide) (by decide) (by decide)) (Env.Frame.mono F hn hs ha)
  cases pos with
  | none =>
    have hc : ¬ σ1.sc 21 < σ1.sc 28 := by rw [s21, e28, hnone rfl]; norm_num
    refine runs_mono (runs_ifS_f (by decide) (by decide) hc (runs_seq (K₂ := d * d * 5 + 3 + 1)
      (runs_vfill (L := df2L) (w := w) σ1
      (dv := 0) (one := 2) (i := 3) (y := 0) (z := 21) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) hd1 h11) (fun σ2 h2 => ?_))) (by unfold kMode0; omega) (fun σ' h => h)
    obtain ⟨v2, F2, -⟩ := h2
    refine runs_seq (runs_mfill (L := df2L) (w := w) σ2 (dd := 9) (one := 2) (m := 3) (A := 1) (z := 21)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by rw [F2.1 9 (by decide)]; exact h91) (by rw [F2.1 2 (by decide)]; exact h11)) (fun σ3 h3 => ?_)
    obtain ⟨m3, F3, -⟩ := h3
    refine runs_mono (runs_sconst (L := df2L) (w := w) (σ := σ3) (x := 22) (by decide) 0) le_rfl (fun σ' e => ?_)
    subst e
    have F13 : Env.Frame σ1 σ3 [3] [22] [0, 1] :=
      Env.Frame.trans (Env.Frame.mono F2 (by decide) (by decide) (by decide))
        (Env.Frame.mono F3 (by decide) (by decide) (by decide))
    have z2 : σ2.sc 21 = 0 := by rw [F2.2.1 21 (by decide), s21]
    refine ⟨⟨?_, ?_⟩, by simp [df2Mode0Of, ModeRep], Fend _ _ _ _ (Env.Frame.setSc F13 (by simp) _)
      (by decide) (by decide) (by decide)⟩
    · show σ3.vec 0 = _
      rw [Env.Frame.vec_eq F3 (by decide), v2, s21]; rfl
    · show σ3.mat 1 = _
      rw [m3, z2]; ext i j; simp [pgMat]
  | some P =>
    obtain ⟨h28, hv0, hm1⟩ := hsome P rfl
    have hc : σ1.sc 21 < σ1.sc 28 := by rw [s21, e28, h28]; norm_num
    have hpos : ∀ σ' (ns ss as : List ℕ), Env.Frame σ1 σ' ns ss as → 0 ∉ as → 1 ∉ as →
        PosRep ((some P).getD 0) σ' := fun σ' ns ss as F h0 h1' => by
      refine ⟨?_, ?_⟩
      · rw [Env.Frame.vec_eq F h0]; show σ.vec 0 = _; rw [hv0]; rfl
      · rw [Env.Frame.mat_eq F h1']; exact hm1
    by_cases he : 1 / 2 < p.eps
    · have hc2 : σ1.sc 19 < σ1.sc 10 := by rw [s19, e10]; exact he
      refine runs_mono (runs_ifS_t (by decide) (by decide) hc (runs_ifS_t (by decide) (by decide) hc2
        (runs_sconst (L := df2L) (w := w) (σ := σ1) (x := 22) (by decide) 0))) (by unfold kMode0; omega)
        (fun σ' e => ?_)
      subst e
      have F := Env.Frame.setSc (Env.Frame.refl σ1 [] [22] []) (x := 22) (by simp) ((0 : ℚ) : ℝ)
      exact ⟨hpos _ _ _ _ F (by simp) (by simp), by simp only [df2Mode0Of, he, ↓reduceIte]; simp [ModeRep],
        Fend _ _ _ _ F (by decide) (by decide) (by decide)⟩
    · have hc2 : ¬ σ1.sc 19 < σ1.sc 10 := by rw [s19, e10]; exact he
      refine runs_mono (runs_ifS_t (by decide) (by decide) hc (runs_ifS_f (by decide) (by decide) hc2
        (runs_seq (K₂ := 1) (runs_stInit σ1 hd1 h11 h91 s21 s27) (fun σ2 h2 => ?_)))) (by unfold kMode0; omega)
        (fun σ' h => h)
      obtain ⟨t23, t2, t3, t4, t5, t6, t24, t7, t25, t8, t26, F2⟩ := h2
      refine runs_mono (runs_sconst (L := df2L) (w := w) (σ := σ2) (x := 22) (by decide) 2) le_rfl
        (fun σ' e => ?_)
      subst e
      have F : Env.Frame σ1 (σ2.setSc 22 ((2 : ℚ) : ℝ)) [3, 5] [22, 23, 24, 25, 26, 56, 57] [2, 3, 4, 5, 6, 7, 8] :=
        Env.Frame.setSc (Env.Frame.mono F2 (by decide) (by decide) (by decide)) (by simp) _
      refine ⟨hpos _ _ _ _ F (by simp) (by simp), ?_, Fend _ _ _ _ F (by decide) (by decide) (by decide)⟩
      simp only [df2Mode0Of, he, ↓reduceIte, ModeRep, StRep, df2Init, Env.setSc_sc]
      refine ⟨by norm_num, by simpa using t23, t2, by show σ2.mat 3 = _; rw [t3, e8],
        by show σ2.mat 4 = _; rw [t4, e8], by show σ2.mat 5 = _; rw [t5, e8], t6,
        by simpa using t24, t7, by simpa using t25, t8, by simp [t26, e10]⟩

/-! ## The preparation -/

/-- The rule of PG at the indices of `df2L`: the answer in the scalar `28`, the position in the arrays `0`, `1`. -/
theorem runs_pgCode_df2 (hL : PG.PgLeaves) {n : ℕ} {r0 R0 δ₁ : ℝ} (σ : Env d) (hd1 : 1 ≤ d) (hd : σ.nat 0 = d)
    (h1 : σ.nat 2 = 1) (hr0 : σ.sc 0 = r0) (hR0 : σ.sc 1 = R0) (hδ : σ.sc 3 = δ₁) (hdr : σ.draws = 0) :
    Runs df2L w (PG.pgCode df2L 0 2 0 1 3 28 0 1 30 128 48) σ (PG.kPG d r0 R0 δ₁) (fun σ' =>
      σ'.draws = df2oN0 d r0 R0 δ₁ ∧ (pg d w.K r0 R0 δ₁ (df2oOmega d n r0 R0 δ₁ w.gs) = none → σ'.sc 28 = 0) ∧
      (∀ P, pg d w.K r0 R0 δ₁ (df2oOmega d n r0 R0 δ₁ w.gs) = some P →
        σ'.sc 28 = 1 ∧ σ'.vec 0 = (fun i => pgMu P i) ∧ σ'.mat 1 = pgMat P) ∧
      Env.Frame σ { σ' with draws := σ.draws } (PG.pgCodeN 30) (28 :: PG.pgCodeS 128) (0 :: 1 :: PG.pgStageA 48)) :=
  PG.runs_pgCode hL σ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) hd1 hd h1 hr0 hR0 hδ hdr

/-- The preparation: the parameters, `d²` in the natural `9`, PG (its answer in the scalar `28`, the position in the
arrays `0`, `1`), the mode before round `0`. -/
def preCode : Cmd :=
  .seq df2Params (.seq (nsq 0 2 3 9) (.seq (PG.pgCode df2L 0 2 0 1 3 28 0 1 30 128 48) mode0Code))

/-- The steps of the preparation. -/
noncomputable def kPre (d n : ℕ) (r0 R0 δ : ℝ) : ℕ :=
  (df2oPar d n δ).j * 4 + 103 + (d * 4 + 4 + (PG.kPG d r0 R0 (df2oPar d n δ).δ1 + kMode0 d))

open Classical in
/-- The rule of the preparation: `RndI` at round `0` in the mode `df2oMode0`, the leaves of PG as a hypothesis. -/
theorem runs_preCode (hL : PG.PgLeaves) (n : ℕ) (r0 R0 δ : ℝ) (hd1 : 1 ≤ d) :
    Runs df2L w preCode (Env.init d n r0 R0 δ) (kPre d n r0 R0 δ) (fun σ =>
      RndI n (df2oPar d n δ) ((df2oPos d n r0 R0 δ w).getD 0) (df2oN0 d r0 R0 (df2oPar d n δ).δ1) 0
        (df2oMode0 d n r0 R0 δ w) σ ∧ σ.rounds = 0) := by
  set σ0 := Env.init d n r0 R0 δ with hσ0
  set p := df2oPar d n δ with hp
  refine runs_seq (runs_df2Params (w := w) σ0 (n := n) (δ := δ) (by simp [σ0, Env.init]) (by simp [σ0, Env.init])
    (by simp [σ0, Env.init])) (fun σ1 h1' => ?_)
  obtain ⟨hpar1, o1, F1⟩ := h1'
  have d1 : σ1.nat 0 = d := by rw [F1.1 0 (by decide)]; simp [σ0, Env.init]
  refine runs_seq (runs_nsq (L := df2L) (w := w) σ1 (dv := 0) (one := 2) (i := 3) (dd := 9) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) d1 o1) (fun σ2 h2' => ?_)
  obtain ⟨n9, F2⟩ := h2'
  have hpar2 : ParRep p σ2 := hpar1.frame F2 (by decide) (by decide)
  have d2 : σ2.nat 0 = d := by rw [F2.1 0 (by decide), d1]
  have o2 : σ2.nat 2 = 1 := by rw [F2.1 2 (by decide), o1]
  have r02 : σ2.sc 0 = r0 := by rw [F2.2.1 0 (by decide), F1.2.1 0 (by decide)]; simp [σ0, Env.init]
  have R02 : σ2.sc 1 = R0 := by rw [F2.2.1 1 (by decide), F1.2.1 1 (by decide)]; simp [σ0, Env.init]
  have dr2 : σ2.draws = 0 := by rw [F2.2.2.2.1, F1.2.2.2.1]; rfl
  refine runs_seq (runs_pgCode_df2 (n := n) hL σ2 hd1 d2 o2 r02 R02 hpar2.1 dr2) (fun σ3 h3' => ?_)
  obtain ⟨dr3, hnone, hsome, F3⟩ := h3'
  have Fn3 : ∀ i, i ∉ PG.pgCodeN 30 → σ3.nat i = σ2.nat i := F3.1
  have d3 : σ3.nat 0 = d := by rw [Fn3 0 (by decide), d2]
  have o3 : σ3.nat 2 = 1 := by rw [Fn3 2 (by decide), o2]
  have n93 : σ3.nat 9 = d * d := by rw [Fn3 9 (by decide), n9]
  have hss3 : ∀ x ∈ 28 :: PG.pgCodeS 128, x < 3 ∨ 18 < x := by
    intro x hx
    by_contra hc
    have hx' : x ∈ PG.pgBodyS 128 := by
      simp only [List.mem_cons, PG.pgCodeS, List.mem_append, List.not_mem_nil, or_false] at hx
      rcases hx with h | h | h | h
      · omega
      · exact h
      · omega
      · omega
    exact PG.pgBodyS_not_mem (Or.inl (by omega)) hx'
  have hpar3 : ParRep p σ3 :=
    (hpar2.frame F3 (by decide) hss3 : ParRep p { σ3 with draws := σ2.draws })
  refine runs_mono (runs_mode0 (w := w) p (df2oPos d n r0 R0 δ w) σ3 d3 o3 n93 hpar3 hnone hsome) le_rfl
    (fun σ4 h4 => ?_)
  obtain ⟨hP4, hm4, F4⟩ := h4
  have n1 : σ3.nat 1 = n := by
    rw [Fn3 1 (by decide), F2.1 1 (by decide), F1.1 1 (by decide)]; simp [σ0, Env.init]
  refine ⟨⟨by rw [F4.1 0 (by decide), d3], by rw [F4.1 1 (by decide), n1], by rw [F4.1 2 (by decide), o3],
    by rw [F4.1 9 (by decide), n93], hpar3.frame F4 (by decide) (by decide), hP4,
    by rw [df2oMode0_eq]; exact hm4, by rw [F4.2.2.2.1, dr3]; simp [p]⟩, ?_⟩
  rw [F4.2.2.2.2.1]
  show ({ σ3 with draws := σ2.draws } : Env d).rounds = 0
  rw [F3.2.2.2.2.1, F2.2.2.2.2.1, F1.2.2.2.2.1]; rfl

/-! ## The program of DF2-O -/

/-- The program of DF2-O: the setup, the preparation, then the rounds `t < n` (round counter in the natural `6`),
each part `A`, the play of the array `14` (the observation in the scalar `32`), part `B`. -/
def df2Prog : Cmd := prog df2L preCode df2A df2B 6 1 2 32 14

theorem df2oMode_zero (d n : ℕ) (r0 R0 δ : ℝ) (w : World d) :
    df2oMode d n r0 R0 δ w 0 = df2oMode0 d n r0 R0 δ w := rfl

theorem df2oMode_succ (d n : ℕ) (r0 R0 δ : ℝ) (w : World d) (t : ℕ) :
    df2oMode d n r0 R0 δ w (t + 1) = (df2oRoundAt d n r0 R0 δ w t (df2oMode d n r0 R0 δ w t)).2 := by
  simp only [df2oMode, df2oFrom, Nat.zero_add]

theorem RndI.setNat6 {n : ℕ} {p : Df2OPar} {Ps : PgSp d} {N0 t : ℕ} {m : Df2Mode d} {σ : Env d}
    (h : RndI n p Ps N0 t m σ) (k : ℕ) : RndI n p Ps N0 t m (σ.setNat 6 k) := by
  obtain ⟨hd, hn, h1, h9, hpar, hP, hm, hdr⟩ := h
  have F : Env.Frame σ (σ.setNat 6 k) [6] [] [] := Env.Frame.setNat (Env.Frame.refl σ [6] [] []) (by simp) k
  exact ⟨by simp [hd], by simp [hn], by simp [h1], by simp [h9], hpar.frame F (by decide) (by decide),
    hP.frame F (by decide) (by decide), ModeRep.congr hm (fun _ _ => rfl) (fun _ _ => rfl), hdr⟩

open Classical in
/-- The program of DF2-O on one run: its cost clause with the bounds of `prog_spec` and its points played those of
`df2oPlay` in the rounds `t < n`. The leaves of PG (`PgLeaves`) and the two calls of AP in each round of DF2
(`ApRules`, steps `K1`, `K2`) enter as hypotheses. -/
theorem df2Prog_spec (hL : PG.PgLeaves) (d n : ℕ) (hd1 : 1 ≤ d) (hn : 1 ≤ n) (r0 R0 δ : ℝ) (w : World d)
    (K1 K2 : ℕ)
    (hAP : ∀ t < n, ∀ st, df2oMode d n r0 R0 δ w t = .run st →
      ApRules w (df2oPar d n δ) n ((df2oPos d n r0 R0 δ w).getD 0) st
        (df2oXi (df2oN0 d r0 R0 (df2oPar d n δ).δ1) w.gs t)
        (df2Y (df2oPar d n δ) w.K ((df2oPos d n r0 R0 δ w).getD 0) (w.f t) (w.noise t) st
          (df2oXi (df2oN0 d r0 R0 (df2oPar d n δ).δ1) w.gs t)
          (df2oZeta d (df2oN0 d r0 R0 (df2oPar d n δ).δ1) w.gs t)) K1 K2) :
    CostOK (df2Prog.compile 0) w (init d n r0 R0 δ) n
        ((df2L.NS + 2 * df2L.NA + 4 * d + 7 + kPre d n r0 R0 δ + kDf2A d (df2oPar d n δ).j + 3 : ℕ) : ℝ)
        ((kDf2A d (df2oPar d n δ).j + kDf2B d K1 K2 + 4 : ℕ) : ℝ) ∧
      ∀ t < n, played (df2Prog.compile 0) w (init d n r0 R0 δ) t = df2oPlay d n r0 R0 δ w t := by
  set p := df2oPar d n δ with hp
  set Ps := (df2oPos d n r0 R0 δ w).getD 0 with hPs
  set N0 := df2oN0 d r0 R0 p.δ1 with hN0
  exact prog_spec df2L (pre := preCode) (A := df2A) (B := df2B) (rt := 6) (rn := 1) (one := 2) (x := 32) (v := 14)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) w n hn r0 R0 δ
    (df2L.NS + 2 * df2L.NA + 4 * d + 7) (kPre d n r0 R0 δ) (kDf2A d p.j) (kDf2B d K1 K2)
    (fun t σ => RndI n p Ps N0 t (df2oMode d n r0 R0 δ w t) σ)
    (fun t σ => RndJ w n p Ps N0 t (df2oMode d n r0 R0 δ w t) σ) (df2oPlay d n r0 R0 δ w)
    (Mach.setup_rep df2L (by decide) (by decide) w n r0 R0 δ)
    (runs_mono (runs_preCode (w := w) hL n r0 R0 δ hd1) le_rfl (fun σ h => ⟨by
      rw [df2oMode_zero]; exact h.1.setNat6 0, h.1.2.1, h.1.2.2.1, h.2⟩))
    (fun t _ σ hI ht _ _ hr => runs_mono (runs_rndA (w := w) n p Ps N0 t _ σ hI) le_rfl
      (fun σ' h => ⟨h.1, by rw [h.2.1, ht], h.1.2.1, h.1.2.2.1, by rw [h.2.2.1, hr], h.2.2.2⟩))
    (fun t htn σ hJ ht _ _ hr => runs_mono (runs_rndB (w := w) n p Ps N0 t _ K1 K2 σ hJ hr (hAP t htn)) le_rfl
      (fun σ' h => ⟨by rw [df2oMode_succ]; exact h.1.setNat6 (t + 1), by rw [h.2.1, ht], h.1.2.1, h.1.2.2.1,
        h.2.2⟩))

end AdversarialBco.Poly.Mach.VL
