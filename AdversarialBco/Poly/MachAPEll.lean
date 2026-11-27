/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.MachAPSep

@[expose] public section

/-!
# The subroutine AP in VL: the central cut and Procedure ELL-cap

The state of ELL-cap: `A` and `a` in the arrays `aB + 9`, `aB + 10`; the recorded point in the array `aB + 11`, its
flag in the scalar `sB + 104` and its value of `F` in `sB + 105`; the flags `sB + 102` (`1` while running) and
`sB + 103` (`0` after a failure); a returned point stays in `aB + 10`. The rules: `runs_cutCode` (the central cut,
`ccUpdate` through `ccUpdate_eq`), the steps, the constants, the start, the end and `runs_ellCapCode`.
-/

namespace AdversarialBco.Poly.AP

open AdversarialBco AdversarialBco.RealRAM AdversarialBco.Poly.Mach AdversarialBco.Poly.Mach.VL Matrix

variable {d : ℕ} {L : Layout} {w : World d} {memQ : Cmd} {V : APVars}

/-- The step bound of the central cut. -/
def kCut (d : ℕ) : ℕ :=
  (d * (d * 10 + 9) + 4) + ((d * 9 + 4) + (1 + (1 + (1 + ((d * 7 + 3) + ((d * 8 + 3) + (1 + (1 + (1 + (1 + (1 +
    (1 + (1 + (1 + (1 + (1 + (1 + (1 + ((d * (d * 16 + 6) + 4) + (d * 11 + 3))))))))))))))))))))

/-- The naturals, scalars and arrays that the central cut writes. -/
abbrev cutN (V : APVars) : List ℕ := [V.nB, V.nB + 1, V.nB + 2]
/-- The scalars of the central cut. -/
abbrev cutS (V : APVars) : List ℕ := List.range' (V.sB + 80) 10
/-- The arrays of the central cut. -/
abbrev cutA (V : APVars) : List ℕ := [V.aB + 7, V.aB + 8, V.aB + 9, V.aB + 10]

set_option maxHeartbeats 8000000 in
/-- The central cut by the array `c`: `ccUpdate` on `A` (the array `aB + 9`) and `a` (the array `aB + 10`). -/
theorem runs_cutCode {nsQ ssQ asQ : List ℕ} (hp : V.Ok L nsQ ssQ asQ) {c : ℕ} (hc : c < L.NA)
    (hc7 : c ≠ V.aB + 7) (σ : Env d) (hd : σ.nat V.dv = d) (h1 : σ.nat V.one = 1) :
    Runs L w (cutCode L V c) σ (kCut d)
      (fun σ' => σ'.mat (V.aB + 9) = (ccUpdate (σ.mat (V.aB + 9)) (σ.vec (V.aB + 10)) (σ.vec c)).1 ∧
        σ'.vec (V.aB + 10) = (ccUpdate (σ.mat (V.aB + 9)) (σ.vec (V.aB + 10)) (σ.vec c)).2 ∧
        Env.Frame σ σ' (cutN V) (cutS V) (cutA V)) := by
  layout_facts
  let F : Env d → Prop := fun σa => Env.Frame σ σa (cutN V) (cutS V) (cutA V)
  have fr : ∀ σa σb (ns ss as : List ℕ), F σa → Env.Frame σa σb ns ss as → (∀ j ∈ ns, j ∈ cutN V) →
      (∀ j ∈ ss, j ∈ cutS V) → (∀ j ∈ as, j ∈ cutA V) → F σb :=
    fun σa σb ns ss as h h' hn hs ha => Env.Frame.trans h (Env.Frame.mono h' hn hs ha)
  have frS : ∀ σa (x : ℕ) (v : ℝ), V.sB + 80 ≤ x → x < V.sB + 90 → F σa → F (σa.setSc x v) :=
    fun σa x v h1 h2 h => Env.Frame.setSc h (by simp only [List.mem_range'_1]; omega) v
  have fN : ∀ σa, F σa → σa.nat V.dv = d ∧ σa.nat V.one = 1 := fun σa h =>
    ⟨by rw [h.1 _ (by nmem_tac), hd], by rw [h.1 _ (by nmem_tac), h1]⟩
  set M := σ.mat (V.aB + 9) with hM
  set a := σ.vec (V.aB + 10) with ha
  set cv := σ.vec c with hcv
  unfold cutCode kCut
  refine runs_seq (runs_matvec σ (by lay) (by lay) (by lay) (by lay) (by lay) (by lay) (by lay) hc (by lay) (by lay)
    (by lay) (by lay) (by lay) (by lay) (by lay) (by lay) (by lay) (by omega) (by omega) (by omega) (Ne.symm hc7)
    (by omega) (by omega) (by omega) (by omega) hd h1) (fun σ1 h1' => ?_)
  obtain ⟨v1, f1, -⟩ := h1'
  have F1 : F σ1 := fr _ _ _ _ _ (Env.Frame.refl _ _ _ _) f1 (fun _ h => h)
    (by intro j hj; simp only [List.mem_cons, List.not_mem_nil, or_false] at hj; simp only [List.mem_range'_1]; omega)
    (by intro j hj; simp only [List.mem_cons, List.not_mem_nil, or_false] at hj ⊢; omega)
  have c1 : σ1.vec c = cv := Env.Frame.vec f1 (by simpa using hc7)
  obtain ⟨d1, o1⟩ := fN σ1 F1
  refine runs_seq (runs_vdot σ1 (by lay) (by lay) (by lay) (by lay) hc (by lay) (by lay) (by lay) (by lay) (by lay)
    (by omega) (by omega) (by omega) d1 o1) (fun σ2 h2' => ?_)
  obtain ⟨s2, f2⟩ := h2'
  have F2 : F σ2 := fr _ _ _ _ _ F1 f2 (by simp)
    (by intro j hj; simp only [List.mem_cons, List.not_mem_nil, or_false] at hj; simp only [List.mem_range'_1]; omega)
    (by simp)
  rw [c1, v1] at s2
  refine runs_seq (runs_sop1 (by lay) (by lay) .sqrt) (fun σ3 e3 => ?_)
  refine runs_seq (runs_sconst (by lay) 1) (fun σ4 e4 => ?_)
  refine runs_seq (runs_sop2 (by lay) (by lay) (by lay) .div) (fun σ5 e5 => ?_)
  have F5 : F σ5 := by
    rw [e5, e4, e3]
    exact frS _ _ _ (by omega) (by omega) (frS _ _ _ (by omega) (by omega) (frS _ _ _ (by omega) (by omega) F2))
  have s5 : σ5.sc (V.sB + 80) = 1 / Real.sqrt (cv ⬝ᵥ (M *ᵥ cv)) := by
    rw [e5, e4, e3]; simp [Op2.eval, Op1.eval, s2, ← hM, ← hcv]
  have v5 : σ5.vec (V.aB + 7) = M *ᵥ cv := by
    rw [e5, e4, e3]; simp only [Env.setSc_vec]; rw [Env.Frame.vec f2 (by simp), v1]
  obtain ⟨d5, o5⟩ := fN σ5 F5
  refine runs_seq (runs_vcopy σ5 (by lay) (by lay) (by lay) (by lay) (by lay) (by lay) (by lay) (by lay) d5 o5)
    (fun σ6 h6' => ?_)
  obtain ⟨v6, f6, -⟩ := h6'
  have F6 : F σ6 := fr _ _ _ _ _ F5 f6 (by simp)
    (by intro j hj; simp only [List.mem_cons, List.not_mem_nil, or_false] at hj; simp only [List.mem_range'_1]; omega)
    (by intro j hj; simp only [List.mem_cons, List.not_mem_nil, or_false] at hj ⊢; omega)
  obtain ⟨d6, o6⟩ := fN σ6 F6
  refine runs_seq (runs_vscale σ6 (by lay) (by lay) (by lay) (by lay) (by lay) (by lay) (by lay) (by lay) (by omega)
    d6 o6) (fun σ7 h7' => ?_)
  obtain ⟨v7, f7, -⟩ := h7'
  have F7 : F σ7 := fr _ _ _ _ _ F6 f7 (by simp)
    (by intro j hj; simp only [List.mem_cons, List.not_mem_nil, or_false] at hj; simp only [List.mem_range'_1]; omega)
    (by intro j hj; simp only [List.mem_cons, List.not_mem_nil, or_false] at hj ⊢; omega)
  have b7 : σ7.vec (V.aB + 8) = (1 / Real.sqrt (cv ⬝ᵥ (M *ᵥ cv))) • (M *ᵥ cv) := by
    rw [v7, v6, v5, f6.2.1 _ (by simp), s5]
  have M7 : σ7.mat (V.aB + 9) = M := by
    rw [Env.Frame.mat f7 (by simp), Env.Frame.mat f6 (by simp), e5, e4, e3]
    simp only [Env.setSc_mat]; rw [Env.Frame.mat f2 (by simp), Env.Frame.mat f1 (by simp)]
  have a7 : σ7.vec (V.aB + 10) = a := by
    rw [Env.Frame.vec f7 (by simp), Env.Frame.vec f6 (by simp), e5, e4, e3]
    simp only [Env.setSc_vec]; rw [Env.Frame.vec f2 (by simp), Env.Frame.vec f1 (by simp)]
  refine runs_seq (runs_ncast (by lay) (by lay)) (fun σ8 e8 => ?_)
  refine runs_seq (runs_sop2 (by lay) (by lay) (by lay) .mul) (fun σ9 e9 => ?_)
  refine runs_seq (runs_sop2 (by lay) (by lay) (by lay) .sub) (fun σ10 e10 => ?_)
  refine runs_seq (runs_sop2 (by lay) (by lay) (by lay) .div) (fun σ11 e11 => ?_)
  refine runs_seq (runs_sop2 (by lay) (by lay) (by lay) .add) (fun σ12 e12 => ?_)
  refine runs_seq (runs_sconst (by lay) 2) (fun σ13 e13 => ?_)
  refine runs_seq (runs_sop2 (by lay) (by lay) (by lay) .div) (fun σ14 e14 => ?_)
  refine runs_seq (runs_sop2 (by lay) (by lay) (by lay) .mul) (fun σ15 e15 => ?_)
  refine runs_seq (runs_sconst (by lay) 0) (fun σ16 e16 => ?_)
  refine runs_seq (runs_sop2 (by lay) (by lay) (by lay) .sub) (fun σ17 e17 => ?_)
  refine runs_seq (runs_sop2 (by lay) (by lay) (by lay) .div) (fun σ18 e18 => ?_)
  refine runs_seq (runs_sop2 (by lay) (by lay) (by lay) .sub) (fun σ19 e19 => ?_)
  have n7 : σ7.nat V.dv = d := (fN σ7 F7).1
  have s81 : σ7.sc (V.sB + 81) = 1 := by
    rw [f7.2.1 _ (by simp), f6.2.1 _ (by simp), e5, e4, e3]; simp
  have F19 : F σ19 := by
    rw [e19, e18, e17, e16, e15, e14, e13, e12, e11, e10, e9, e8]
    exact frS _ _ _ (by omega) (by omega) (frS _ _ _ (by omega) (by omega) (frS _ _ _ (by omega) (by omega)
      (frS _ _ _ (by omega) (by omega) (frS _ _ _ (by omega) (by omega) (frS _ _ _ (by omega) (by omega)
      (frS _ _ _ (by omega) (by omega) (frS _ _ _ (by omega) (by omega) (frS _ _ _ (by omega) (by omega)
      (frS _ _ _ (by omega) (by omega) (frS _ _ _ (by omega) (by omega) (frS _ _ _ (by omega) (by omega) F7)))))))))))
  have h84 : σ19.sc (V.sB + 84) = (d : ℝ) * d / ((d : ℝ) * d - 1) := by
    rw [e19, e18, e17, e16, e15, e14, e13, e12, e11, e10, e9, e8]; simp [Op2.eval, n7, s81]
  have h85 : σ19.sc (V.sB + 85) = 0 - (d : ℝ) * d / ((d : ℝ) * d - 1) * (2 / ((d : ℝ) + 1)) := by
    rw [e19, e18, e17, e16, e15, e14, e13, e12, e11, e10, e9, e8]; simp [Op2.eval, n7, s81]
  have h86 : σ19.sc (V.sB + 86) = 0 - 1 / ((d : ℝ) + 1) := by
    rw [e19, e18, e17, e16, e15, e14, e13, e12, e11, e10, e9, e8]; simp [Op2.eval, n7, s81]
  have b19 : σ19.vec (V.aB + 8) = (1 / Real.sqrt (cv ⬝ᵥ (M *ᵥ cv))) • (M *ᵥ cv) := by
    rw [e19, e18, e17, e16, e15, e14, e13, e12, e11, e10, e9, e8]; simp only [Env.setSc_vec]; exact b7
  have M19 : σ19.mat (V.aB + 9) = M := by
    rw [e19, e18, e17, e16, e15, e14, e13, e12, e11, e10, e9, e8]; simp only [Env.setSc_mat]; exact M7
  have a19 : σ19.vec (V.aB + 10) = a := by
    rw [e19, e18, e17, e16, e15, e14, e13, e12, e11, e10, e9, e8]; simp only [Env.setSc_vec]; exact a7
  obtain ⟨d19, o19⟩ := fN σ19 F19
  refine runs_seq (runs_rankOne σ19 (by lay) (by lay) (by lay) (by lay) (by lay) (by lay) (by lay) (by lay) (by lay)
    (by lay) (by lay) (by lay) (by lay) (by lay) (by lay) (by lay) (by lay) (by lay) (by lay) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) d19 o19) (fun σ20 h20' => ?_)
  obtain ⟨m20, f20, -⟩ := h20'
  have F20 : F σ20 := fr _ _ _ _ _ F19 f20 (fun _ h => h)
    (by intro j hj; simp only [List.mem_cons, List.not_mem_nil, or_false] at hj; simp only [List.mem_range'_1]; omega)
    (by intro j hj; simp only [List.mem_cons, List.not_mem_nil, or_false] at hj ⊢; omega)
  obtain ⟨d20, o20⟩ := fN σ20 F20
  refine runs_mono (runs_vaxpy σ20 (by lay) (by lay) (by lay) (by lay) (by lay) (by lay) (by lay) (by lay) (by lay)
    (by lay) (by omega) (by omega) (by omega) d20 o20) le_rfl (fun σ21 h21' => ?_)
  obtain ⟨v21, f21, -⟩ := h21'
  rw [ccUpdate_eq]
  refine ⟨?_, ?_, fr _ _ _ _ _ F20 f21 (by simp)
    (by intro j hj; simp only [List.mem_cons, List.not_mem_nil, or_false] at hj; simp only [List.mem_range'_1]; omega)
    (by intro j hj; simp only [List.mem_cons, List.not_mem_nil, or_false] at hj ⊢; omega)⟩
  · rw [Env.Frame.mat f21 (by simp), m20, h84, h85, b19, M19]
  · rw [v21, Env.Frame.vec f20 (by simp), a19, f20.2.1 _ (by simp), h86, Env.Frame.vec f20 (by simp), b19]

/-- The recorded point of ELL-cap: none (flag `sB + 104` at `0`), or the point in `aB + 11` with its value of `F`
in `sB + 105`. -/
def BestRel (V : APVars) (P : Matrix (Fin d) (Fin d) ℝ) (w : Fin d → ℝ) : Option (Fin d → ℝ) → Env d → Prop
  | none, σ => σ.sc (V.sB + 104) = 0
  | some b, σ => σ.sc (V.sB + 104) = 1 ∧ σ.vec (V.aB + 11) = b ∧ σ.sc (V.sB + 105) = ellF P w b

/-- The state of ELL-cap: the flags `sB + 103` (`0` after a failure) and `sB + 102` (`1` while running), the
ellipsoid in `aB + 9`, `aB + 10`, the recorded point; a returned point in `aB + 10`. -/
def ERel (V : APVars) (P : Matrix (Fin d) (Fin d) ℝ) (w : Fin d → ℝ) :
    Option (EllSt d ⊕ (Fin d → ℝ)) → Env d → Prop
  | none, σ => σ.sc (V.sB + 103) = 0 ∧ σ.sc (V.sB + 102) = 0
  | some (.inl st), σ => σ.sc (V.sB + 103) = 1 ∧ σ.sc (V.sB + 102) = 1 ∧ σ.mat (V.aB + 9) = st.A ∧
      σ.vec (V.aB + 10) = st.a ∧ BestRel V P w st.best σ
  | some (.inr μ), σ => σ.sc (V.sB + 103) = 1 ∧ σ.sc (V.sB + 102) = 0 ∧ σ.vec (V.aB + 10) = μ

open Classical in
/-- Step 3 of ELL-cap at `a ∈ Q`: record `a`, then return it if `P (a - w) = 0`, else cut by `P (a - w)`. -/
noncomputable def ellStep3F (P : Matrix (Fin d) (Fin d) ℝ) (w : Fin d → ℝ) (st : EllSt d) :
    Option (EllSt d ⊕ (Fin d → ℝ)) :=
  let best := ellRecord P w st.best st.a
  if P *ᵥ (st.a - w) = 0 then some (.inr st.a)
  else
    let u := ccUpdate st.A st.a (P *ᵥ (st.a - w))
    some (.inl ⟨u.1, u.2, best⟩)

/-- The scalars that step 3 writes. -/
abbrev s3S (V : APVars) : List ℕ := List.range' (V.sB + 80) 20 ++ [V.sB + 102, V.sB + 104, V.sB + 105]
/-- The arrays that step 3 writes. -/
abbrev s3A (V : APVars) : List ℕ := List.range' (V.aB + 7) 7

/-- The step bound of step 3. -/
def kS3 (d : ℕ) : ℕ :=
  (d * 7 + 3) + (1 + ((d * 11 + 3) + ((d * (d * 10 + 9) + 4) + ((d * 9 + 4) + (1 + (1 + ((d * 7 + 7) +
    ((d * 9 + 4) + (kCut d + 1)))))))))

/-- Membership in the lists of ELL-cap. -/
macro "inE" : tactic => `(tactic| (simp only [s3S, s3A, cutN, cutS, cutA, List.mem_append, List.mem_cons,
  List.mem_range'_1, List.not_mem_nil, or_false, not_or, not_and, not_lt]; (repeat' apply And.intro); all_goals lay))
/-- Inclusion of lists of ELL-cap. -/
macro "subE" : tactic => `(tactic| (intro j hj; simp only [s3S, s3A, cutN, cutS, cutA, List.mem_append,
  List.mem_cons, List.mem_range'_1, List.not_mem_nil, or_false] at hj ⊢; omega))

set_option maxHeartbeats 8000000 in
open Classical in
/-- The rule of step 3, with `0` in `sB + 91`. -/
theorem runs_ellStep3 {nsQ ssQ asQ : List ℕ} (hp : V.Ok L nsQ ssQ asQ) (σ : Env d) (hd : σ.nat V.dv = d)
    (h1 : σ.nat V.one = 1) (st : EllSt d) (hst : ERel V (σ.mat V.P) (σ.vec V.w) (some (.inl st)) σ)
    (h91 : σ.sc (V.sB + 91) = 0) :
    Runs L w (ellStep3 L V) σ (kS3 d)
      (fun σ' => ERel V (σ.mat V.P) (σ.vec V.w) (ellStep3F (σ.mat V.P) (σ.vec V.w) st) σ' ∧
        Env.Frame σ σ' (cutN V) (s3S V) (s3A V)) := by
  layout_facts
  let F : Env d → Prop := fun σa => Env.Frame σ σa (cutN V) (s3S V) (s3A V)
  let Fp : Env d → Prop := fun σa => Env.Frame σ σa (cutN V) (List.range' (V.sB + 92) 7) [V.aB + 12, V.aB + 13]
  have fr : ∀ σa σb (ns ss as : List ℕ), F σa → Env.Frame σa σb ns ss as → (∀ j ∈ ns, j ∈ cutN V) →
      (∀ j ∈ ss, j ∈ s3S V) → (∀ j ∈ as, j ∈ s3A V) → F σb :=
    fun σa σb ns ss as h h' hn hs ha => Env.Frame.trans h (Env.Frame.mono h' hn hs ha)
  have frp : ∀ σa σb (ns ss as : List ℕ), Fp σa → Env.Frame σa σb ns ss as → (∀ j ∈ ns, j ∈ cutN V) →
      (∀ j ∈ ss, j ∈ List.range' (V.sB + 92) 7) → (∀ j ∈ as, j ∈ [V.aB + 12, V.aB + 13]) → Fp σb :=
    fun σa σb ns ss as h h' hn hs ha => Env.Frame.trans h (Env.Frame.mono h' hn hs ha)
  have frS : ∀ σa (x : ℕ) (v : ℝ), x ∈ s3S V → F σa → F (σa.setSc x v) :=
    fun σa x v hx h => Env.Frame.setSc h hx v
  have frpS : ∀ σa (x : ℕ) (v : ℝ), V.sB + 92 ≤ x → x < V.sB + 99 → Fp σa → Fp (σa.setSc x v) :=
    fun σa x v h1 h2 h => Env.Frame.setSc h (by simp only [List.mem_range'_1]; omega) v
  have fN : ∀ σa, F σa → σa.nat V.dv = d ∧ σa.nat V.one = 1 := fun σa h =>
    ⟨by rw [h.1 _ (by nmem_tac), hd], by rw [h.1 _ (by nmem_tac), h1]⟩
  have fpN : ∀ σa, Fp σa → σa.nat V.dv = d ∧ σa.nat V.one = 1 := fun σa h =>
    ⟨by rw [h.1 _ (by nmem_tac), hd], by rw [h.1 _ (by nmem_tac), h1]⟩
  have fpP : ∀ σa, Fp σa → σa.mat V.P = σ.mat V.P ∧ σa.vec V.w = σ.vec V.w := fun σa h =>
    ⟨Env.Frame.mat h (by nmem_tac), Env.Frame.vec h (by nmem_tac)⟩
  have sub3 : ∀ j ∈ cutS V, j ∈ s3S V := by subE
  have subA : ∀ j ∈ cutA V, j ∈ s3A V := by subE
  obtain ⟨f103, f102, hA, ha, hbest⟩ := hst
  unfold ellStep3 kS3
  refine runs_seq (runs_vcopy σ (by lay) (by lay) (by lay) (by lay) (by lay) (by lay) (by lay) (by lay) hd h1)
    (fun σ1 h1' => ?_)
  obtain ⟨v1, f1, -⟩ := h1'
  have F1 : Fp σ1 := frp _ _ _ _ _ (Env.Frame.refl _ _ _ _) f1 (by subE) (by subE) (by simp)
  refine runs_seq (runs_sconst (by lay) (-1)) (fun σ2 e2 => ?_)
  have F2 : Fp σ2 := by rw [e2]; exact frpS _ _ _ (by omega) (by omega) F1
  obtain ⟨d2, o2⟩ := fpN σ2 F2
  refine runs_seq (runs_vaxpy σ2 (by lay) (by lay) (by lay) (by lay) (by lay) (by lay) (by lay) (by lay) (by lay)
    (by lay) (by omega) (by omega) (by omega) d2 o2) (fun σ3 h3' => ?_)
  obtain ⟨v3, f3, -⟩ := h3'
  have F3 : Fp σ3 := frp _ _ _ _ _ F2 f3 (by subE) (by subE) (by simp)
  have amw : σ3.vec (V.aB + 12) = st.a - σ.vec V.w := by
    rw [v3, e2]; simp only [Env.setSc_vec]; rw [v1, (fpP σ1 F1).2, ha]; simp [sub_eq_add_neg]
  obtain ⟨d3, o3⟩ := fpN σ3 F3
  refine runs_seq (runs_matvec σ3 (by lay) (by lay) (by lay) (by lay) (by lay) (by lay) (by lay) (by lay) (by lay)
    (by lay) (by lay) (by lay) (by lay) (by lay) (by lay) (by lay) (by lay) (by omega) (by omega) (by omega)
    (by omega) (by lay) (by omega) (by omega) (by omega) d3 o3) (fun σ4 h4' => ?_)
  obtain ⟨v4, f4, -⟩ := h4'
  have F4 : Fp σ4 := frp _ _ _ _ _ F3 f4 (by subE) (by subE) (by simp)
  rw [(fpP σ3 F3).1, amw] at v4
  have amw4 : σ4.vec (V.aB + 12) = st.a - σ.vec V.w := by rw [Env.Frame.vec f4 (by simp), amw]
  obtain ⟨d4, o4⟩ := fpN σ4 F4
  refine runs_seq (runs_vdot σ4 (by lay) (by lay) (by lay) (by lay) (by lay) (by lay) (by lay) (by lay) (by lay)
    (by lay) (by omega) (by omega) (by omega) d4 o4) (fun σ5 h5' => ?_)
  obtain ⟨s5, f5⟩ := h5'
  have F5 : Fp σ5 := frp _ _ _ _ _ F4 f5 (by simp) (by subE) (by simp)
  refine runs_seq (runs_sconst (by lay) (1 / 2)) (fun σ6 e6 => ?_)
  refine runs_seq (runs_sop2 (by lay) (by lay) (by lay) .mul) (fun σ7 e7 => ?_)
  have F7p : Fp σ7 := by
    rw [e7, e6]; exact frpS _ _ _ (by omega) (by omega) (frpS _ _ _ (by omega) (by omega) F5)
  have F7 : F σ7 := Env.Frame.mono F7p (fun _ h => h) (by subE) (by subE)
  have pS : ∀ x, ¬ (V.sB + 92 ≤ x ∧ x < V.sB + 99) → σ7.sc x = σ.sc x := fun x hx =>
    F7p.2.1 x (by simpa only [List.mem_range'_1] using hx)
  have hF : σ7.sc (V.sB + 93) = ellF (σ.mat V.P) (σ.vec V.w) st.a := by
    rw [e7, e6, ellF_eq_code]; simp [Op2.eval, s5, amw4, v4, sub_eq_add_neg]
  have a7 : σ7.vec (V.aB + 10) = st.a := by rw [Env.Frame.vec F7p (by simp), ha]
  have q7 : σ7.vec (V.aB + 13) = σ.mat V.P *ᵥ (st.a - σ.vec V.w) := by
    rw [e7, e6]; simp only [Env.setSc_vec]; rw [Env.Frame.vec f5 (by simp), v4]
  have z7 : σ7.sc (V.sB + 91) = 0 := by rw [pS _ (by omega), h91]
  have M7 : σ7.mat (V.aB + 9) = st.A := by rw [Env.Frame.mat F7p (by simp), hA]
  have b7 : BestRel V (σ.mat V.P) (σ.vec V.w) st.best σ7 := by
    rcases hhb : st.best with _ | b
    · rw [hhb] at hbest; show σ7.sc _ = 0; rw [pS _ (by omega), hbest]
    · rw [hhb] at hbest
      obtain ⟨b1, b2, b3⟩ := hbest
      exact ⟨by rw [pS _ (by omega), b1], by rw [Env.Frame.vec F7p (by simp), b2], by rw [pS _ (by omega), b3]⟩
  have r103 : σ7.sc (V.sB + 103) = 1 := by rw [pS _ (by omega), f103]
  have r102 : σ7.sc (V.sB + 102) = 1 := by rw [pS _ (by omega), f102]
  -- the record
  obtain ⟨d7, o7⟩ := fN σ7 F7
  have copy : Runs L w (.seq (vcopy L V.dv V.one V.nB (V.aB + 11) (V.aB + 10) (V.sB + 97))
      (smov L (V.sB + 105) (V.sB + 93))) σ7 (d * 7 + 3 + 1) (fun σ' => σ'.vec (V.aB + 11) = st.a ∧
        σ'.sc (V.sB + 105) = ellF (σ.mat V.P) (σ.vec V.w) st.a ∧ F σ' ∧
        (∀ x, x ≠ V.sB + 97 → x ≠ V.sB + 105 → σ'.sc x = σ7.sc x) ∧
        (∀ a, a ≠ V.aB + 11 → σ'.vec a = σ7.vec a) ∧ σ'.mat (V.aB + 9) = σ7.mat (V.aB + 9)) := by
    refine runs_seq (runs_vcopy σ7 (by lay) (by lay) (by lay) (by lay) (by lay) (by lay) (by lay) (by lay) d7 o7)
      (fun σa ha' => ?_)
    obtain ⟨va, fa, -⟩ := ha'
    refine runs_mono (runs_smov (by lay) (by lay)) le_rfl (fun σb eb => ?_)
    subst eb
    have k93 : σa.sc (V.sB + 93) = σ7.sc (V.sB + 93) := fa.2.1 (V.sB + 93) (by simp)
    refine ⟨by rw [Env.setSc_vec, va, a7], by simp [k93, hF], ?_, fun x h1 h2 => ?_, fun a h => by
        rw [Env.setSc_vec, Env.Frame.vec fa (by simpa using h)], by rw [Env.setSc_mat, Env.Frame.mat fa (by simp)]⟩
    · exact frS _ (V.sB + 105) _ (by simp [s3S]) (fr _ _ _ _ _ F7 fa (by subE) (by subE) (by subE))
    · rw [Env.setSc_sc, if_neg h2]; exact fa.2.1 x (by simpa using h1)
  have hrec : Runs L w (ifS L (V.sB + 91) (V.sB + 104)
      (ifS L (V.sB + 93) (V.sB + 105)
        (.seq (vcopy L V.dv V.one V.nB (V.aB + 11) (V.aB + 10) (V.sB + 97)) (smov L (V.sB + 105) (V.sB + 93)))
        .skip)
      (.seq (vcopy L V.dv V.one V.nB (V.aB + 11) (V.aB + 10) (V.sB + 97)) <|
       .seq (smov L (V.sB + 105) (V.sB + 93)) <|
       sconst L (V.sB + 104) 1)) σ7 (d * 7 + 7)
      (fun σ' => BestRel V (σ.mat V.P) (σ.vec V.w) (ellRecord (σ.mat V.P) (σ.vec V.w) st.best st.a) σ' ∧ F σ' ∧
        σ'.sc (V.sB + 91) = 0 ∧ σ'.sc (V.sB + 103) = 1 ∧ σ'.sc (V.sB + 102) = 1 ∧ σ'.vec (V.aB + 10) = st.a ∧
        σ'.vec (V.aB + 13) = σ.mat V.P *ᵥ (st.a - σ.vec V.w) ∧ σ'.mat (V.aB + 9) = st.A) := by
    rcases hhb : st.best with _ | b
    · rw [hhb] at b7
      refine runs_mono (K := (d * 7 + 3 + (1 + 1)) + 2)
        (runs_ifS_f (by lay) (by lay) (by rw [z7, b7]; exact lt_irrefl 0) ?_) (by omega) (fun _ h => h)
      refine runs_seq (runs_vcopy σ7 (by lay) (by lay) (by lay) (by lay) (by lay) (by lay) (by lay) (by lay) d7 o7)
        (fun σa ha' => ?_)
      obtain ⟨va, fa, -⟩ := ha'
      refine runs_seq (runs_smov (by lay) (by lay)) (fun σb eb => ?_)
      refine runs_mono (runs_sconst (by lay) 1) le_rfl (fun σc ec => ?_)
      subst ec eb
      have k93 : σa.sc (V.sB + 93) = σ7.sc (V.sB + 93) := fa.2.1 (V.sB + 93) (by simp)
      refine ⟨⟨by simp, by rw [Env.setSc_vec, Env.setSc_vec, va, a7], by simp [k93, hF]⟩,
        frS _ (V.sB + 104) _ (by simp [s3S]) (frS _ (V.sB + 105) _ (by simp [s3S]) (fr _ _ _ _ _ F7 fa (by subE) (by subE)
        (by subE))), by simp [fa.2.1 (V.sB + 91) (by simp), z7], by simp [fa.2.1 (V.sB + 103) (by simp), r103],
        by simp [fa.2.1 (V.sB + 102) (by simp), r102],
        by rw [Env.setSc_vec, Env.setSc_vec, Env.Frame.vec fa (by simp), a7],
        by rw [Env.setSc_vec, Env.setSc_vec, Env.Frame.vec fa (by simp), q7],
        by rw [Env.setSc_mat, Env.setSc_mat, Env.Frame.mat fa (by simp), M7]⟩
    · rw [hhb] at b7
      obtain ⟨b1, b2, b3⟩ := b7
      refine runs_mono (K := ((d * 7 + 3 + 1) + 1) + 1)
        (runs_ifS_t (by lay) (by lay) (by rw [z7, b1]; exact one_pos) ?_) (by omega) (fun _ h => h)
      by_cases hlt : ellF (σ.mat V.P) (σ.vec V.w) st.a < ellF (σ.mat V.P) (σ.vec V.w) b
      · refine runs_mono (runs_ifS_t (by lay) (by lay) (by rw [hF, b3]; exact hlt) copy) le_rfl
          (fun σa ha' => ?_)
        obtain ⟨c1, c2, cF, cS, cA, cM⟩ := ha'
        have hr : ellRecord (σ.mat V.P) (σ.vec V.w) (some b) st.a = some st.a := by simp [ellRecord, hlt]
        rw [hr]
        exact ⟨⟨by rw [cS _ (by omega) (by omega), b1], c1, c2⟩, cF, by rw [cS _ (by omega) (by omega), z7],
          by rw [cS _ (by omega) (by omega), r103], by rw [cS _ (by omega) (by omega), r102],
          by rw [cA _ (by omega), a7], by rw [cA _ (by omega), q7], by rw [cM, M7]⟩
      · refine runs_mono (runs_ifS_f (by lay) (by lay) (by rw [hF, b3]; exact hlt) (runs_skip σ7)) (by omega)
          (fun σa ea => ?_)
        subst ea
        have hr : ellRecord (σ.mat V.P) (σ.vec V.w) (some b) st.a = some b := by simp [ellRecord, hlt]
        rw [hr]
        exact ⟨⟨b1, b2, b3⟩, F7, z7, r103, r102, a7, q7, M7⟩
  refine runs_seq hrec (fun σ8 h8 => ?_)
  obtain ⟨hb8, F8, z8, s103, s102, a8, q8, M8⟩ := h8
  obtain ⟨d8, o8⟩ := fN σ8 F8
  refine runs_seq (runs_vdot σ8 (by lay) (by lay) (by lay) (by lay) (by lay) (by lay) (by lay) (by lay) (by lay)
    (by lay) (by omega) (by omega) (by omega) d8 o8) (fun σ9 h9' => ?_)
  obtain ⟨s94, f9⟩ := h9'
  have F9 : F σ9 := fr _ _ _ _ _ F8 f9 (by simp) (by subE) (by simp)
  have k9 : ∀ x, x ≠ V.sB + 94 → x ≠ V.sB + 97 → x ≠ V.sB + 98 → σ9.sc x = σ8.sc x := fun x h1 h2 h3 =>
    f9.2.1 x (by simp [h1, h2, h3])
  rw [q8] at s94
  have hb9 : BestRel V (σ.mat V.P) (σ.vec V.w) (ellRecord (σ.mat V.P) (σ.vec V.w) st.best st.a) σ9 := by
    rcases hr : ellRecord (σ.mat V.P) (σ.vec V.w) st.best st.a with _ | b
    · rw [hr] at hb8; exact (k9 _ (by omega) (by omega) (by omega)).trans hb8
    · rw [hr] at hb8
      obtain ⟨b1, b2, b3⟩ := hb8
      exact ⟨(k9 _ (by omega) (by omega) (by omega)).trans b1, (Env.Frame.vec f9 (by simp)).trans b2,
        (k9 _ (by omega) (by omega) (by omega)).trans b3⟩
  have r103' : σ9.sc (V.sB + 103) = 1 := by rw [k9 _ (by omega) (by omega) (by omega), s103]
  have r102' : σ9.sc (V.sB + 102) = 1 := by rw [k9 _ (by omega) (by omega) (by omega), s102]
  have a9 : σ9.vec (V.aB + 10) = st.a := by rw [Env.Frame.vec f9 (by simp), a8]
  have q9 : σ9.vec (V.aB + 13) = σ.mat V.P *ᵥ (st.a - σ.vec V.w) := by rw [Env.Frame.vec f9 (by simp), q8]
  have M9 : σ9.mat (V.aB + 9) = st.A := by rw [Env.Frame.mat f9 (by simp), M8]
  have z9 : σ9.sc (V.sB + 91) = 0 := by rw [k9 _ (by omega) (by omega) (by omega), z8]
  obtain ⟨d9, o9⟩ := fN σ9 F9
  unfold ellStep3F
  by_cases hz : σ.mat V.P *ᵥ (st.a - σ.vec V.w) = 0
  · simp only [hz, if_true]
    have hn : ¬ σ9.sc (V.sB + 91) < σ9.sc (V.sB + 94) := by
      rw [z9, s94]; exact (not_dot_self_pos_iff _).2 hz
    refine runs_mono (runs_ifS_f (by lay) (by lay) hn (runs_sconst (by lay) 0)) (by unfold kCut; omega)
      (fun σ10 e10 => ?_)
    subst e10
    exact ⟨⟨by simp [r103'], by simp, by rw [Env.setSc_vec, a9]⟩, frS _ (V.sB + 102) _ (by simp [s3S]) F9⟩
  · simp only [hz, if_false]
    have hc : σ9.sc (V.sB + 91) < σ9.sc (V.sB + 94) := by
      rw [z9, s94]; exact not_not.1 (mt (not_dot_self_pos_iff _).1 hz)
    refine runs_mono (runs_ifS_t (by lay) (by lay) hc (runs_cutCode hp (c := V.aB + 13) (by lay) (by omega) σ9 d9 o9))
      le_rfl (fun σ10 h10 => ?_)
    obtain ⟨m10, v10, f10⟩ := h10
    rw [M9, a9, q9] at m10 v10
    have k10 : ∀ x, x ∉ cutS V → σ10.sc x = σ9.sc x := fun x hx => f10.2.1 x hx
    refine ⟨⟨by rw [k10 _ (by inE), r103'], by rw [k10 _ (by inE), r102'], m10, v10, ?_⟩,
      fr _ _ _ _ _ F9 f10 (fun _ h => h) sub3 subA⟩
    rcases hr : ellRecord (σ.mat V.P) (σ.vec V.w) st.best st.a with _ | b
    · rw [hr] at hb9; exact (k10 _ (by inE)).trans hb9
    · rw [hr] at hb9
      obtain ⟨b1, b2, b3⟩ := hb9
      exact ⟨(k10 _ (by inE)).trans b1, (Env.Frame.vec f10 (by simp)).trans b2, (k10 _ (by inE)).trans b3⟩

theorem BestRel.of_eq {P : Matrix (Fin d) (Fin d) ℝ} {w : Fin d → ℝ} {o : Option (Fin d → ℝ)} {σa σb : Env d}
    (h : BestRel V P w o σa) (h104 : σb.sc (V.sB + 104) = σa.sc (V.sB + 104))
    (h105 : σb.sc (V.sB + 105) = σa.sc (V.sB + 105)) (h11 : σb.vec (V.aB + 11) = σa.vec (V.aB + 11)) :
    BestRel V P w o σb := by
  rcases o with _ | b
  · exact h104.trans h
  · exact ⟨h104.trans h.1, h11.trans h.2.1, h105.trans h.2.2⟩

theorem ERel.of_eq {P : Matrix (Fin d) (Fin d) ℝ} {w : Fin d → ℝ} {o : Option (EllSt d ⊕ (Fin d → ℝ))}
    {σa σb : Env d} (h : ERel V P w o σa) (h102 : σb.sc (V.sB + 102) = σa.sc (V.sB + 102))
    (h103 : σb.sc (V.sB + 103) = σa.sc (V.sB + 103)) (h104 : σb.sc (V.sB + 104) = σa.sc (V.sB + 104))
    (h105 : σb.sc (V.sB + 105) = σa.sc (V.sB + 105)) (h9 : σb.mat (V.aB + 9) = σa.mat (V.aB + 9))
    (h10 : σb.vec (V.aB + 10) = σa.vec (V.aB + 10)) (h11 : σb.vec (V.aB + 11) = σa.vec (V.aB + 11)) :
    ERel V P w o σb := by
  rcases o with _ | st | μ
  · exact ⟨h103.trans h.1, h102.trans h.2⟩
  · exact ⟨h103.trans h.1, h102.trans h.2.1, h9.trans h.2.2.1, h10.trans h.2.2.2.1,
      BestRel.of_eq h.2.2.2.2 h104 h105 h11⟩
  · exact ⟨h103.trans h.1, h102.trans h.2.1, h10.trans h.2.2⟩

theorem ERel.of_frame {P : Matrix (Fin d) (Fin d) ℝ} {w : Fin d → ℝ} {o : Option (EllSt d ⊕ (Fin d → ℝ))}
    {σa σb : Env d} {ns ss as : List ℕ} (h : ERel V P w o σa) (f : Env.Frame σa σb ns ss as)
    (h102 : V.sB + 102 ∉ ss) (h103 : V.sB + 103 ∉ ss) (h104 : V.sB + 104 ∉ ss) (h105 : V.sB + 105 ∉ ss)
    (h9 : V.aB + 9 ∉ as) (h10 : V.aB + 10 ∉ as) (h11 : V.aB + 11 ∉ as) : ERel V P w o σb :=
  h.of_eq (f.2.1 _ h102) (f.2.1 _ h103) (f.2.1 _ h104) (f.2.1 _ h105) (Env.Frame.mat f h9) (Env.Frame.vec f h10)
    (Env.Frame.vec f h11)

/-- The scalars that a step of ELL-cap writes. -/
abbrev stepS (V : APVars) : List ℕ := List.range' V.sB 100 ++ [V.sB + 102, V.sB + 103, V.sB + 104, V.sB + 105]
/-- The arrays that a step of ELL-cap writes. -/
abbrev stepA (V : APVars) : List ℕ := List.range' V.aB 14 ++ [V.qv]

/-- The step bound of the search of a cut and its end in a step of ELL-cap (SEP, then the cut or the failure). -/
def kESq (d Kq B J : ℕ) : ℕ := kSC d Kq B J + ((d * 9 + 4) + (kCut d + 8))

/-- The step bound of a step of ELL-cap. -/
def kES (d Kq B J : ℕ) : ℕ :=
  (d * 9 + 5) + (kCut d + (((d * 7 + 3) + (Kq + (1 + (kS3 d + (kESq d Kq B J + 2))))) + 2))

/-- Inclusion in the lists of a step. -/
macro "subST" : tactic => `(tactic| (intro j hj; simp only [stepS, stepA, sepS, sepA, s3S, s3A, cutN, cutS, cutA,
  List.mem_append, List.mem_cons, List.mem_range'_1, List.not_mem_nil, or_false] at hj ⊢; omega))

/-- A scalar of a step. -/
macro "stepIn" : tactic =>
  `(tactic| (simp only [stepS, List.mem_append, List.mem_cons, List.mem_range'_1, List.not_mem_nil, or_false, or_true,
    true_or] <;> omega))

/-- A variable outside the lists of a step. -/
macro "nmemST" : tactic => `(tactic| (simp only [stepS, stepA]; nmem_tac))

set_option maxHeartbeats 16000000 in
open Classical in
/-- The rule of one step of ELL-cap from a running state, with the constants `k` in their variables. -/
theorem runs_ellStepCode {Q : Set (Fin d → ℝ)} {Iq : Env d → Prop} {Kq : ℕ} {nsQ ssQ asQ : List ℕ}
    (hp : V.Ok L nsQ ssQ asQ) (hmem : MemRule L w memQ V Q Iq Kq nsQ ssQ asQ) (hIq : IqRule V Iq)
    (σ : Env d) (hd : σ.nat V.dv = d) (h1 : σ.nat V.one = 1) (hI : Iq σ) (h0 : 0 < d) (k : EllConsts)
    (hτ : σ.sc (V.sB + 100) = k.τ) (hℓ : σ.sc (V.sB + 101) = k.ℓ1) (hJ : σ.nat (V.nB + 10) = k.J)
    (hB : σ.nat (V.nB + 11) = k.B) (st : EllSt d) (hst : ERel V (σ.mat V.P) (σ.vec V.w) (some (.inl st)) σ) :
    Runs L w (ellStepCode L memQ V) σ (kES d Kq k.B k.J)
      (fun σ' => ERel V (σ.mat V.P) (σ.vec V.w)
          (ellStep Q (σ.vec V.a0) (σ.sc V.r) (σ.sc V.R) (σ.mat V.P) (σ.vec V.w) k st) σ' ∧
        KP Iq nsQ ssQ asQ (List.range' V.nB 8) (stepS V) (stepA V) σ σ') := by
  layout_facts
  have hON : ∀ j ∈ List.range' V.nB 8, j ∈ apN V := by mem_tac
  have hOS : ∀ j ∈ stepS V, j ∈ apS V := by mem_tac
  have hOA : ∀ j ∈ stepA V, j ∈ apA V := by mem_tac
  let G : Env d → Prop := KP Iq nsQ ssQ asQ (List.range' V.nB 8) (stepS V) (stepA V) σ
  have liftF : ∀ σa σb (ns ss as : List ℕ), G σa → Env.Frame σa σb ns ss as → (∀ j ∈ ns, j ∈ List.range' V.nB 8) →
      (∀ j ∈ ss, j ∈ stepS V) → (∀ j ∈ as, j ∈ stepA V) → G σb :=
    fun σa σb ns ss as g f hn hs ha => keep_own hIq hON hOS hOA g f hn hs ha
  have liftK : ∀ σa σb (ON OS OA : List ℕ), G σa → KP Iq nsQ ssQ asQ ON OS OA σa σb →
      (∀ j ∈ ON, j ∈ List.range' V.nB 8) → (∀ j ∈ OS, j ∈ stepS V) → (∀ j ∈ OA, j ∈ stepA V) → G σb :=
    fun σa σb ON OS OA g k hn hs ha => keep_trans g (keep_mono k hn hs ha)
  have ownS : ∀ σa (q : ℕ) (v : ℝ), q ∈ stepS V → G σa → G (σa.setSc q v) :=
    fun σa q v hq g => keep_own hIq hON hOS hOA g (frame_setSc _ _ _) (by simp) (by simpa using hq) (by simp)
  have gN : ∀ σa, G σa → σa.nat V.dv = d ∧ σa.nat V.one = 1 := fun σa g =>
    ⟨by rw [g.nat (by nmemS) hp.dv_nQ, hd], by rw [g.nat (by nmemS) hp.one_nQ, h1]⟩
  have gC : ∀ σa, G σa → σa.sc (V.sB + 100) = k.τ ∧ σa.sc (V.sB + 101) = k.ℓ1 ∧ σa.nat (V.nB + 10) = k.J ∧
      σa.nat (V.nB + 11) = k.B ∧ σa.mat V.P = σ.mat V.P ∧ σa.vec V.w = σ.vec V.w ∧ σa.sc V.R = σ.sc V.R ∧
      σa.sc V.r = σ.sc V.r ∧ σa.vec V.a0 = σ.vec V.a0 := fun σa g =>
    ⟨by rw [g.sc (by nmemST) (hp.sB_sQ (by omega) (by omega)), hτ],
      by rw [g.sc (by nmemST) (hp.sB_sQ (by omega) (by omega)), hℓ],
      by rw [g.nat (by nmemS) (hp.nN_nQ (by omega) (by omega)), hJ],
      by rw [g.nat (by nmemS) (hp.nN_nQ (by omega) (by omega)), hB],
      g.mat (by nmemST) hp.P_aQ, g.vec (by nmemST) hp.w_aQ, g.sc (by nmemST) hp.R_sQ, g.sc (by nmemST) hp.r_sQ,
      g.vec (by nmemST) hp.a0_aQ⟩
  obtain ⟨-, -, -, ha, -⟩ := id hst
  unfold ellStepCode kES
  refine runs_seq (runs_vnorm σ (by lay) (by lay) (by lay) (by lay) (by lay) (by lay) (by lay) (by lay) (by lay)
    (by omega) (by omega) (by omega) hd h1) (fun σ1 h1' => ?_)
  obtain ⟨s90, f1⟩ := h1'
  have g1 : G σ1 := liftF _ _ _ _ _ (keep_refl hI) f1 (by subST) (by subST) (by simp)
  have e1 : ERel V (σ.mat V.P) (σ.vec V.w) (some (.inl st)) σ1 :=
    hst.of_frame f1 (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
  rw [ha] at s90
  obtain ⟨d1, o1⟩ := gN σ1 g1
  have R1 : σ1.sc V.R = σ.sc V.R := (gC σ1 g1).2.2.2.2.2.2.1
  by_cases hc : σ.sc V.R < oNorm st.a
  · have hstep : ellStep Q (σ.vec V.a0) (σ.sc V.r) (σ.sc V.R) (σ.mat V.P) (σ.vec V.w) k st =
        some (.inl ⟨(ccUpdate st.A st.a st.a).1, (ccUpdate st.A st.a st.a).2, st.best⟩) := by
      unfold ellStep; rw [if_pos hc]
    rw [hstep]
    refine runs_mono (runs_ifS_t (by lay) (by lay) (by rw [R1, s90]; exact hc)
      (runs_cutCode hp (c := V.aB + 10) (by lay) (by omega) σ1 d1 o1)) (by omega) (fun σ2 h2 => ?_)
    obtain ⟨m2, v2, f2⟩ := h2
    obtain ⟨e103, e102, A1, a1, b1⟩ := e1
    rw [A1, a1] at m2 v2
    exact ⟨⟨by rw [f2.2.1 _ (by inE)]; exact e103, by rw [f2.2.1 _ (by inE)]; exact e102, m2, v2,
      BestRel.of_eq b1 (f2.2.1 _ (by inE)) (f2.2.1 _ (by inE)) (Env.Frame.vec f2 (by inE))⟩,
      liftF _ _ _ _ _ g1 f2 (by subST) (by subST) (by subST)⟩
  · refine runs_mono (K := (d * 7 + 3) + (Kq + (1 + (kS3 d + (kESq d Kq k.B k.J + 2)))) + 2)
      (runs_ifS_f (by lay) (by lay) (by rw [R1, s90]; exact hc) ?_) (by omega) (fun _ h => h)
    refine runs_seq (runs_vcopy σ1 (by lay) (by lay) (by lay) (by lay) (by lay) (by lay) (by lay) (by lay) d1 o1)
      (fun σ2 h2' => ?_)
    obtain ⟨v2, f2, -⟩ := h2'
    have g2 : G σ2 := liftF _ _ _ _ _ g1 f2 (by subST) (by subST) (by subST)
    have e2 : ERel V (σ.mat V.P) (σ.vec V.w) (some (.inl st)) σ2 :=
      e1.of_frame f2 (by simp) (by simp) (by simp) (by simp) (by simp; lay) (by simp; lay) (by simp; lay)
    obtain ⟨d2, o2⟩ := gN σ2 g2
    refine runs_seq (hmem σ2 g2.1 d2 o2) (fun σ3 h3' => ?_)
    obtain ⟨q3, f3, I3⟩ := h3'
    have g3 : G σ3 := keep_mem g2 f3 I3
    have e3 : ERel V (σ.mat V.P) (σ.vec V.w) (some (.inl st)) σ3 :=
      e2.of_frame f3 (hp.sB_sQ (by omega) (by omega)) (hp.sB_sQ (by omega) (by omega))
        (hp.sB_sQ (by omega) (by omega)) (hp.sB_sQ (by omega) (by omega)) (hp.aB_aQ (by omega) (by omega))
        (hp.aB_aQ (by omega) (by omega)) (hp.aB_aQ (by omega) (by omega))
    rw [v2, e1.2.2.2.1] at q3
    refine runs_seq (runs_sconst (by lay) 0) (fun σ4 e4' => ?_)
    have g4 : G σ4 := by rw [e4']; exact ownS _ _ _ (by stepIn) g3
    have e4 : ERel V (σ.mat V.P) (σ.vec V.w) (some (.inl st)) σ4 := by
      rw [e4']; exact e3.of_frame (frame_setSc _ _ _) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
        (by simp)
    have z4 : σ4.sc (V.sB + 91) = 0 := by rw [e4']; simp
    have qo4 : σ4.sc V.qo = if st.a ∈ Q then 1 else 0 := by
      rw [e4']; simp only [Env.setSc_sc]; rw [if_neg (by lay), q3]
    obtain ⟨d4, o4⟩ := gN σ4 g4
    obtain ⟨c100, c101, c10, c11, cP, cw, cR, cr, ca0⟩ := gC σ4 g4
    by_cases hq : st.a ∈ Q
    · have hstep : ellStep Q (σ.vec V.a0) (σ.sc V.r) (σ.sc V.R) (σ.mat V.P) (σ.vec V.w) k st =
          ellStep3F (σ.mat V.P) (σ.vec V.w) st := by
        unfold ellStep ellStep3F; rw [if_neg hc, if_neg (not_not.2 hq)]
      rw [hstep]
      have e4' := e4
      rw [← cP, ← cw] at e4'
      refine runs_mono (runs_ifS_t (by lay) (by lay) (by rw [z4, qo4, if_pos hq]; exact one_pos)
        (runs_ellStep3 hp σ4 d4 o4 st e4' z4)) (by omega) (fun σ5 h5 => ?_)
      obtain ⟨r5, f5⟩ := h5
      rw [cP, cw] at r5
      exact ⟨r5, liftF _ _ _ _ _ g4 f5 (by subST) (by subST) (by subST)⟩
    · refine runs_mono (K := kESq d Kq k.B k.J + 2)
        (runs_ifS_f (by lay) (by lay) (by rw [z4, qo4, if_neg hq]; exact lt_irrefl 0) ?_) (by omega)
        (fun _ h => h)
      unfold kESq
      refine runs_seq (runs_mono (runs_sepCode hp hmem hIq (y0 := V.aB + 10) (by lay) σ4 d4 o4 g4.1 h0)
        (le_of_eq (by rw [c11, c10])) (fun _ h => h)) (fun σ5 h5 => ?_)
      obtain ⟨hR5, k5⟩ := h5
      have g5 : G σ5 := liftK _ _ _ _ _ g4 k5 (by subST) (by subST) (by subST)
      have e5 : ERel V (σ.mat V.P) (σ.vec V.w) (some (.inl st)) σ5 :=
        e4.of_frame k5.2 (by simp only [List.mem_append, not_or]; exact ⟨by nmemS, hp.sB_sQ (by omega) (by omega)⟩)
          (by simp only [List.mem_append, not_or]; exact ⟨by nmemS, hp.sB_sQ (by omega) (by omega)⟩)
          (by simp only [List.mem_append, not_or]; exact ⟨by nmemS, hp.sB_sQ (by omega) (by omega)⟩)
          (by simp only [List.mem_append, not_or]; exact ⟨by nmemS, hp.sB_sQ (by omega) (by omega)⟩)
          (by simp only [List.mem_append, not_or]; exact ⟨by nmemS, hp.aB_aQ (by omega) (by omega)⟩)
          (by simp only [List.mem_append, not_or]; exact ⟨by nmemS, hp.aB_aQ (by omega) (by omega)⟩)
          (by simp only [List.mem_append, not_or]; exact ⟨by nmemS, hp.aB_aQ (by omega) (by omega)⟩)
      have z5 : σ5.sc (V.sB + 91) = 0 := by rw [k5.sc (by nmemS) (hp.sB_sQ (by omega) (by omega)), z4]
      have hg5 : gev Q V σ4 = oGaugeValCap Q (σ.vec V.a0) (σ.sc V.r) (σ.sc V.R) k.B := by
        unfold gev; rw [ca0, cr, cR, c11]
      rw [hg5, e4.2.2.2.1, c100, c101, c10, cr] at hR5
      obtain ⟨d5, o5⟩ := gN σ5 g5
      cases hs : sep (oGaugeValCap Q (σ.vec V.a0) (σ.sc V.r) (σ.sc V.R) k.B) st.a k.τ k.ℓ1 (1 / σ.sc V.r) k.J with
      | none =>
        rw [hs] at hR5
        have hstep : ellStep Q (σ.vec V.a0) (σ.sc V.r) (σ.sc V.R) (σ.mat V.P) (σ.vec V.w) k st = none := by
          unfold ellStep; rw [if_neg hc, if_pos hq, hs]
        rw [hstep]
        refine runs_mono (K := 1 + 1 + 2) (runs_ifS_f (by lay) (by lay) (by rw [z5, hR5]; exact lt_irrefl 0) ?_)
          (by omega) (fun _ h => h)
        refine runs_seq (runs_sconst (by lay) 0) (fun σ6 e6 => ?_)
        refine runs_mono (runs_sconst (by lay) 0) le_rfl (fun σ7 e7 => ?_)
        subst e7 e6
        exact ⟨⟨by simp, by simp⟩, ownS _ (V.sB + 103) _ (by stepIn) (ownS _ (V.sB + 102) _ (by stepIn) g5)⟩
      | some p =>
        obtain ⟨y, g⟩ := p
        rw [hs] at hR5
        obtain ⟨r61, -, r6⟩ := hR5
        refine runs_mono (K := (d * 9 + 4) + (kCut d + 4) + 1)
          (runs_ifS_t (by lay) (by lay) (by rw [z5, r61]; exact one_pos) ?_) (by omega) (fun _ h => h)
        refine runs_seq (runs_vdot σ5 (by lay) (by lay) (by lay) (by lay) (by lay) (by lay) (by lay) (by lay)
          (by lay) (by lay) (by omega) (by omega) (by omega) d5 o5) (fun σ6 h6' => ?_)
        obtain ⟨s99, f6⟩ := h6'
        rw [r6] at s99
        have g6 : G σ6 := liftF _ _ _ _ _ g5 f6 (by subST) (by subST) (by simp)
        have e6 : ERel V (σ.mat V.P) (σ.vec V.w) (some (.inl st)) σ6 :=
          e5.of_frame f6 (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
        have z6 : σ6.sc (V.sB + 91) = 0 := by rw [f6.2.1 _ (by simp), z5]
        have g6v : σ6.vec (V.aB + 6) = g := by rw [Env.Frame.vec f6 (by simp), r6]
        obtain ⟨d6, o6⟩ := gN σ6 g6
        by_cases hg : g = 0
        · have hstep : ellStep Q (σ.vec V.a0) (σ.sc V.r) (σ.sc V.R) (σ.mat V.P) (σ.vec V.w) k st = none := by
            unfold ellStep; rw [if_neg hc, if_pos hq, hs]; simp [hg]
          rw [hstep]
          refine runs_mono (K := 1 + 1 + 2)
            (runs_ifS_f (by lay) (by lay) (by rw [z6, s99]; exact (not_dot_self_pos_iff g).2 hg) ?_)
            (by omega) (fun _ h => h)
          refine runs_seq (runs_sconst (by lay) 0) (fun σ7 e7 => ?_)
          refine runs_mono (runs_sconst (by lay) 0) le_rfl (fun σ8 e8 => ?_)
          subst e8 e7
          exact ⟨⟨by simp, by simp⟩, ownS _ (V.sB + 103) _ (by stepIn) (ownS _ (V.sB + 102) _ (by stepIn) g6)⟩
        · have hstep : ellStep Q (σ.vec V.a0) (σ.sc V.r) (σ.sc V.R) (σ.mat V.P) (σ.vec V.w) k st =
              some (.inl ⟨(ccUpdate st.A st.a g).1, (ccUpdate st.A st.a g).2, st.best⟩) := by
            unfold ellStep; rw [if_neg hc, if_pos hq, hs]; simp [hg]
          rw [hstep]
          refine runs_mono (runs_ifS_t (by lay) (by lay)
            (by rw [z6, s99]; exact not_not.1 (mt (not_dot_self_pos_iff g).1 hg))
            (runs_cutCode hp (c := V.aB + 6) (by lay) (by omega) σ6 d6 o6)) (by omega) (fun σ7 h7 => ?_)
          obtain ⟨m7, v7, f7⟩ := h7
          obtain ⟨e103, e102, A6, a6, b6⟩ := e6
          rw [A6, a6, g6v] at m7 v7
          exact ⟨⟨by rw [f7.2.1 _ (by inE)]; exact e103, by rw [f7.2.1 _ (by inE)]; exact e102, m7, v7,
            BestRel.of_eq b6 (f7.2.1 _ (by inE)) (f7.2.1 _ (by inE)) (Env.Frame.vec f7 (by inE))⟩,
            liftF _ _ _ _ _ g6 f7 (by subST) (by subST) (by subST)⟩

end AdversarialBco.Poly.AP
