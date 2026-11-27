/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.MachAPLine
public import AdversarialBco.Poly.APMathSep

@[expose] public section

/-!
# The subroutine AP in VL: Procedure SEP

SEP asks the values `gev Q V σ x η`, the gauge value of `Q` around `a₀` with the cap `B` (the natural variable
`nB + 11`). Its state during the searches is `SRel`: the flag `sB + 61` (`0` after a failure), the point `y` in the
array `aB + 2`, the length `ℓ` in `sB + 60`, the scales `δ` in the array `aB + 3`; its result is `SepRes`, the flag,
the point and the vector `g` in the array `aB + 6`. The rules: `runs_sepCoordTurn` (one search), the loops of the
tail (`runs_sepMinLoop`, `runs_sepPlusLoop`, `runs_sepMinusLoop`, `runs_sepGLoop`), `runs_sepTail` and
`runs_sepCode`, which computes `sep` through `sep_eq_bind`.
-/

namespace AdversarialBco.Poly.AP

open AdversarialBco AdversarialBco.RealRAM AdversarialBco.Poly.Mach AdversarialBco.Poly.Mach.VL Matrix

variable {d : ℕ} {L : Layout} {w : World d} {memQ : Cmd} {V : APVars}

/-- The gauge values that SEP asks. -/
noncomputable def gev (Q : Set (Fin d → ℝ)) (V : APVars) (σ : Env d) : (Fin d → ℝ) → ℝ → Option ℝ :=
  oGaugeValCap Q (σ.vec V.a0) (σ.sc V.r) (σ.sc V.R) (σ.nat (V.nB + 11))

/-- The state of the searches of SEP: the flag `sB + 61`, the point `aB + 2`, the length `sB + 60`, the scales
`aB + 3`. -/
def SRel (V : APVars) : Option (SepSt d) → Env d → Prop
  | none, σ => σ.sc (V.sB + 61) = 0
  | some st, σ => σ.sc (V.sB + 61) = 1 ∧ σ.vec (V.aB + 2) = st.1 ∧ σ.sc (V.sB + 60) = st.2.1 ∧
      σ.vec (V.aB + 3) = st.2.2

/-- The result of SEP: the flag `sB + 61`, the point `aB + 2`, the vector `g` in `aB + 6`. -/
def SepRes (V : APVars) : Option ((Fin d → ℝ) × (Fin d → ℝ)) → Env d → Prop
  | none, σ => σ.sc (V.sB + 61) = 0
  | some p, σ => σ.sc (V.sB + 61) = 1 ∧ σ.vec (V.aB + 2) = p.1 ∧ σ.vec (V.aB + 6) = p.2

/-- The scalars of SEP. -/
abbrev sepS (V : APVars) : List ℕ := List.range' V.sB 71
/-- The arrays of SEP. -/
abbrev sepA (V : APVars) : List ℕ := [V.aB, V.aB + 1, V.aB + 2, V.aB + 3, V.aB + 4, V.aB + 5, V.aB + 6, V.qv]

theorem gev_congr {Q : Set (Fin d → ℝ)} {Iq : Env d → Prop} {nsQ ssQ asQ ON OS OA : List ℕ}
    (hp : V.Ok L nsQ ssQ asQ) {σ σ' : Env d} (h : KP Iq nsQ ssQ asQ ON OS OA σ σ')
    (hN : V.nB + 11 ∉ ON) (hr : V.r ∉ OS) (hR : V.R ∉ OS) (ha : V.a0 ∉ OA) :
    gev Q V σ' = gev Q V σ := by
  unfold gev
  rw [h.vec ha hp.a0_aQ, h.sc hr hp.r_sQ, h.sc hR hp.R_sQ, h.nat hN (hp.nN_nQ (by omega) (by omega))]

/-- `nmem_tac` through the lists of SEP. -/
macro "nmemS" : tactic => `(tactic| ((try simp only [lineN, lineS, lineA, sepS, sepA]); nmem_tac))

/-- The step bound of one search. -/
def kST (d Kq B J : ℕ) : ℕ := kLC d Kq B J + 10

set_option maxHeartbeats 4000000 in
open Classical in
/-- One search of SEP, along the coordinate `i` (the natural variable `nB + 6`), with `16 L` in `sB + 62` and `0` in
`sB + 63`. -/
theorem runs_sepCoordTurn {Q : Set (Fin d → ℝ)} {Iq : Env d → Prop} {Kq : ℕ} {nsQ ssQ asQ : List ℕ}
    (hp : V.Ok L nsQ ssQ asQ) (hmem : MemRule L w memQ V Q Iq Kq nsQ ssQ asQ) (hIq : IqRule V Iq)
    (σ : Env d) (hd : σ.nat V.dv = d) (h1 : σ.nat V.one = 1) (hI : Iq σ) (i : Fin d)
    (hi : σ.nat (V.nB + 6) = i) (st : SepSt d) (hst : SRel V (some st) σ) (h63 : σ.sc (V.sB + 63) = 0)
    {Lc : ℝ} (h62 : σ.sc (V.sB + 62) = 16 * Lc) :
    Runs L w (sepCoordTurn L memQ V) σ (kST d Kq (σ.nat (V.nB + 11)) (σ.nat (V.nB + 10)))
      (fun σ' => SRel V (sepCoord (gev Q V σ) (σ.sc (V.sB + 100)) Lc (σ.nat (V.nB + 10)) i st) σ' ∧
        σ'.sc (V.sB + 63) = 0 ∧ σ'.sc (V.sB + 62) = 16 * Lc ∧
        KP Iq nsQ ssQ asQ (List.range' V.nB 6) (sepS V) (sepA V) σ σ') := by
  layout_facts
  have hON : ∀ j ∈ List.range' V.nB 6, j ∈ apN V := by mem_tac
  have hOS : ∀ j ∈ sepS V, j ∈ apS V := by mem_tac
  have hOA : ∀ j ∈ sepA V, j ∈ apA V := by mem_tac
  let G : Env d → Prop := KP Iq nsQ ssQ asQ (List.range' V.nB 6) (sepS V) (sepA V) σ
  have ownS : ∀ σa (q : ℕ) (v : ℝ), V.sB ≤ q → q < V.sB + 71 → G σa → G (σa.setSc q v) :=
    fun σa q v h1 h2 g => keep_own hIq hON hOS hOA g (frame_setSc _ _ _) (by simp)
      (by intro j hj; simp only [List.mem_singleton] at hj; subst hj; simp only [List.mem_range'_1]; omega) (by simp)
  have ownA : ∀ σa (a k : ℕ) (v : ℝ), a ∈ sepA V → G σa → G (σa.setArr a k v) :=
    fun σa a k v ha g => keep_own hIq hON hOS hOA g (frame_setArr _ _ _ _) (by simp) (by simp)
      (by intro j hj; simp only [List.mem_singleton] at hj; subst hj; exact ha)
  obtain ⟨f61, hy, hl, hδ⟩ := hst
  unfold sepCoordTurn
  refine runs_mono (K := kLC d Kq (σ.nat (V.nB + 11)) (σ.nat (V.nB + 10)) + 10) ?_ (le_of_eq rfl) (fun _ h => h)
  refine runs_seq (runs_lineCode hp hmem hIq σ hd h1 hI i hi) (fun σ1 h1' => ?_)
  obtain ⟨hR, k1⟩ := h1'
  have g1 : G σ1 := keep_mono k1 (fun _ h => h) (by intro j hj; simp only [List.mem_range'_1] at hj ⊢; omega)
    (by intro j hj; simp only [lineA, sepA, List.mem_cons, List.not_mem_nil, or_false] at hj ⊢; omega)
  have hline : lev Q V σ i = fun s η => gev Q V σ (st.1 + s • oUnit i) η := by
    unfold lev gev; rw [hy]
  rw [hline, hl] at hR
  have r61 : σ1.sc (V.sB + 61) = 1 := by rw [k1.sc (by nmemS) (hp.sB_sQ (by omega) (by omega)), f61]
  have r62 : σ1.sc (V.sB + 62) = 16 * Lc := by rw [k1.sc (by nmemS) (hp.sB_sQ (by omega) (by omega)), h62]
  have r63 : σ1.sc (V.sB + 63) = 0 := by rw [k1.sc (by nmemS) (hp.sB_sQ (by omega) (by omega)), h63]
  have r100 : σ1.sc (V.sB + 100) = σ.sc (V.sB + 100) := k1.sc (by nmemS) (hp.sB_sQ (by omega) (by omega))
  have n6 : σ1.nat (V.nB + 6) = i := by rw [k1.nat (by nmemS) (hp.nN_nQ (by omega) (by omega)), hi]
  have y1 : σ1.vec (V.aB + 2) = st.1 := by rw [k1.vec (by nmemS) (hp.aB_aQ (by omega) (by omega)), hy]
  have δ1 : σ1.vec (V.aB + 3) = st.2.2 := by rw [k1.vec (by nmemS) (hp.aB_aQ (by omega) (by omega)), hδ]
  cases hL : line (fun s η => gev Q V σ (st.1 + s • oUnit i) η) st.2.1 (σ.sc (V.sB + 100)) (σ.nat (V.nB + 10)) with
  | none =>
    rw [hL] at hR
    have hsc : sepCoord (gev Q V σ) (σ.sc (V.sB + 100)) Lc (σ.nat (V.nB + 10)) i st = none := by
      rw [sepCoord_eq, hL]; rfl
    rw [hsc]
    refine runs_mono (runs_ifS_f (by lay) (by lay) (by rw [r63, hR]; exact lt_irrefl 0)
      (runs_sconst (by lay) 0)) (by omega) (fun σ2 e2 => ?_)
    subst e2
    refine ⟨by simp [SRel], by simp [r63], by simp [r62], ownS _ _ _ (by omega) (by omega) g1⟩
  | some p =>
    obtain ⟨s, δ⟩ := p
    rw [hL] at hR
    obtain ⟨r28, r30, r31⟩ := hR
    have hsc : sepCoord (gev Q V σ) (σ.sc (V.sB + 100)) Lc (σ.nat (V.nB + 10)) i st =
        some (st.1 + s • oUnit i, σ.sc (V.sB + 100) * δ / (16 * Lc), Function.update st.2.2 i δ) := by
      rw [sepCoord_eq, hL]; rfl
    rw [hsc]
    have hk : σ1.nat (V.nB + 6) < asz d := by rw [n6]; exact lt_asz i.isLt
    refine runs_mono (K := (2 + (1 + (2 + (1 + (1 + 2))))) + 1)
      (runs_ifS_t (by lay) (by lay) (by rw [r63, r28]; exact one_pos) ?_) (by omega) (fun _ h => h)
    refine runs_seq (runs_aget (by lay) (by lay) (by lay) hk) (fun σ2 e2 => ?_)
    refine runs_seq (runs_sop2 (by lay) (by lay) (by lay) .add) (fun σ3 e3 => ?_)
    have i3 : σ3.nat (V.nB + 6) = i := by rw [e3, e2]; exact n6
    refine runs_seq (runs_aset (by lay) (by lay) (by lay) (by rw [i3]; exact lt_asz i.isLt)) (fun σ4 e4 => ?_)
    refine runs_seq (runs_sop2 (by lay) (by lay) (by lay) .mul) (fun σ5 e5 => ?_)
    refine runs_seq (runs_sop2 (by lay) (by lay) (by lay) .div) (fun σ6 e6 => ?_)
    have i6 : σ6.nat (V.nB + 6) = i := by rw [e6, e5, e4]; exact i3
    refine runs_mono (runs_aset (by lay) (by lay) (by lay) (by rw [i6]; exact lt_asz i.isLt)) le_rfl
      (fun σ7 e7 => ?_)
    have y1i : σ1.arr (V.aB + 2) i = st.1 i := congrFun y1 i
    have v66 : σ3.sc (V.sB + 66) = st.1 i + s := by
      rw [e3, e2]; simp [Op2.eval, n6, y1i, r30]
    have y3 : σ3.vec (V.aB + 2) = st.1 := by rw [e3, e2]; simpa using y1
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
    · rw [e7, e6, e5, e4, e3, e2]; simp [r61]
    · rw [e7, Env.setArr_vec_ne _ (by omega), e6, e5, Env.setSc_vec, Env.setSc_vec, e4, i3, Env.setArr_vec_self,
        v66, y3, update_add_eq_oUnit]
    · rw [e7, e6, e5, e4, e3, e2]; simp [Op2.eval, r100, r31, r62]
    · rw [e7, i6, Env.setArr_vec_self, e6, e5, e4, e3, e2]
      simp only [Env.setSc_vec, Env.setSc_sc, Env.setArr_sc]
      rw [Env.setArr_vec_ne _ (by omega), Env.setSc_vec, Env.setSc_vec, δ1]
      simp [r31]
    · rw [e7, e6, e5, e4, e3, e2]; simp [r63]
    · rw [e7, e6, e5, e4, e3, e2]; simp [r62]
    · rw [e7, e6, e5, e4, e3, e2]
      exact ownA _ _ _ _ (by simp [sepA]) (ownS _ _ _ (by omega) (by omega) (ownS _ _ _ (by omega) (by omega)
        (ownA _ _ _ _ (by simp [sepA]) (ownS _ _ _ (by omega) (by omega) (ownS _ _ _ (by omega) (by omega) g1)))))

theorem frame_setArr_of {σ σ' : Env d} {ns ss as : List ℕ} (h : σ.Frame σ' ns ss as) {a : ℕ} (ha : a ∈ as) (k : ℕ)
    (v : ℝ) : σ.Frame (σ'.setArr a k v) ns ss as :=
  Env.Frame.trans h (Env.Frame.mono (frame_setArr σ' a k v) (by simp) (by simp) (by simpa using ha))

set_option maxHeartbeats 1000000 in
/-- The loop of the least scale: `sB + 67` ends at `oMin δ`, `δ` the array `aB + 3`, from one of the scales. -/
theorem runs_sepMinLoop {nsQ ssQ asQ : List ℕ} (hp : V.Ok L nsQ ssQ asQ) (σ : Env d) (hd : σ.nat V.dv = d)
    (h1 : σ.nat V.one = 1) (h0 : 0 < d) (hm : ∃ j, σ.vec (V.aB + 3) j = σ.sc (V.sB + 67)) :
    Runs L w (forN (V.nB + 7) V.dv V.one (.seq (aget L (V.sB + 66) (V.aB + 3) (V.nB + 7))
      (smin L (V.sB + 67) (V.sB + 67) (V.sB + 66)))) σ (d * (5 + 3) + 3)
      (fun σ' => σ'.sc (V.sB + 67) = oMin (σ.vec (V.aB + 3)) ∧
        Env.Frame σ σ' [V.nB + 7] [V.sB + 66, V.sB + 67] []) := by
  layout_facts
  let J : ℕ → Env d → Prop := fun t σ' => minInv (σ.vec (V.aB + 3)) t (σ'.sc (V.sB + 67)) ∧
    Env.Frame σ σ' [V.nB + 7] [V.sB + 66, V.sB + 67] []
  have h0' : J 0 (σ.setNat (V.nB + 7) 0) :=
    ⟨⟨fun j hj => absurd hj (Nat.not_lt_zero _), by simpa using hm⟩,
      Env.Frame.setNat (Env.Frame.refl _ _ _ _) (by simp) 0⟩
  refine runs_mono (runs_forN (by lay) (by lay) (by lay) (by lay) (by lay) d 5 J σ hd h1 h0' ?_) le_rfl
    (fun σ' h => ⟨(minInv_final h0 h.1.1).symm, h.1.2⟩)
  intro t ht σ' hJ hit hnt hot
  obtain ⟨hmin, hf⟩ := hJ
  have δ' : σ'.vec (V.aB + 3) = σ.vec (V.aB + 3) := Env.Frame.vec hf (by simp)
  have hv : σ'.arr (V.aB + 3) t = σ.vec (V.aB + 3) ⟨t, ht⟩ := congrFun δ' ⟨t, ht⟩
  refine runs_mono (K := 2 + 3) ?_ le_rfl (fun _ h => h)
  refine runs_seq (runs_aget (by lay) (by lay) (by lay) (by rw [hit]; exact lt_asz ht)) (fun σ2 e2 => ?_)
  refine runs_mono (runs_smin (by lay) (by lay) (by lay)) le_rfl (fun σ3 e3 => ?_)
  have v3 : σ3.sc (V.sB + 67) = min (σ'.sc (V.sB + 67)) (σ.vec (V.aB + 3) ⟨t, ht⟩) := by
    rw [e3, e2]; simp [hit, hv]
  have f3 : Env.Frame σ σ3 [V.nB + 7] [V.sB + 66, V.sB + 67] [] := by
    rw [e3, e2]; exact Env.Frame.setSc (Env.Frame.setSc hf (by simp) _) (by simp) _
  refine ⟨by rw [e3, e2]; exact hit, by rw [e3, e2]; exact hnt, by rw [e3, e2]; exact hot, ?_, ?_⟩
  · show minInv _ _ ((σ3.setNat _ _).sc _)
    rw [Env.setNat_sc, v3]; exact minInv_step hmin ⟨t, ht⟩ rfl
  · exact Env.Frame.setNat f3 (by simp) _

theorem SRel.setNat {st : Option (SepSt d)} {σ : Env d} (h : SRel V st σ) (j v : ℕ) : SRel V st (σ.setNat j v) := by
  rcases st with _ | st <;> exact h

/-- The scalars that a turn of the values `v⁺` or `v⁻` writes. -/
abbrev valS (V : APVars) : List ℕ :=
  (V.sB + 61) :: (V.sB + 65) :: (V.sB + 66) :: (V.sB + 68) :: (V.sB + 69) :: List.range' V.sB 21

/-- The step bound of one turn of the values `v⁺`. -/
def kPT (d Kq B : ℕ) : ℕ := kEV d Kq B + 8

set_option maxHeartbeats 4000000 in
open Classical in
/-- One turn of the values `v⁺`: the value at `y + δ_i e_i` with error `τ δ_i/400` into `v⁺_i`, or the flag `0`. -/
theorem runs_sepPlusTurn {Q : Set (Fin d → ℝ)} {Iq : Env d → Prop} {Kq : ℕ} {nsQ ssQ asQ : List ℕ}
    (hp : V.Ok L nsQ ssQ asQ) (hmem : MemRule L w memQ V Q Iq Kq nsQ ssQ asQ) (hIq : IqRule V Iq)
    (σ : Env d) (hd : σ.nat V.dv = d) (h1 : σ.nat V.one = 1) (hI : Iq σ) (i : Fin d)
    (hi : σ.nat (V.nB + 7) = i) (h63 : σ.sc (V.sB + 63) = 0) :
    Runs L w (sepPlusTurn L memQ V) σ (kPT d Kq (σ.nat (V.nB + 11)))
      (fun σ' => (gev Q V σ (σ.vec (V.aB + 2) + σ.vec (V.aB + 3) i • oUnit i)
          (σ.sc (V.sB + 100) * σ.vec (V.aB + 3) i / 400) = none →
          σ'.sc (V.sB + 61) = 0 ∧ σ'.vec (V.aB + 4) = σ.vec (V.aB + 4)) ∧
        (∀ v, gev Q V σ (σ.vec (V.aB + 2) + σ.vec (V.aB + 3) i • oUnit i)
          (σ.sc (V.sB + 100) * σ.vec (V.aB + 3) i / 400) = some v →
          σ'.sc (V.sB + 61) = σ.sc (V.sB + 61) ∧ σ'.vec (V.aB + 4) = Function.update (σ.vec (V.aB + 4)) i v) ∧
        KP Iq nsQ ssQ asQ (List.range' V.nB 5) (valS V) [V.aB, V.aB + 1, V.aB + 4, V.qv] σ σ') := by
  layout_facts
  have hON : ∀ j ∈ List.range' V.nB 5, j ∈ apN V := by mem_tac
  have hOS : ∀ j ∈ valS V, j ∈ apS V := by mem_tac
  have hOA : ∀ j ∈ [V.aB, V.aB + 1, V.aB + 4, V.qv], j ∈ apA V := by mem_tac
  let G : Env d → Prop := KP Iq nsQ ssQ asQ (List.range' V.nB 5) (valS V) [V.aB, V.aB + 1, V.aB + 4, V.qv] σ
  have own : ∀ σa (q : ℕ) (v : ℝ), q ∈ valS V → G σa → G (σa.setSc q v) :=
    fun σa q v hq g => keep_own hIq hON hOS hOA g (frame_setSc _ _ _) (by simp) (by simpa using hq) (by simp)
  have hk : σ.nat (V.nB + 7) < asz d := by rw [hi]; exact lt_asz i.isLt
  unfold sepPlusTurn
  refine runs_mono (K := 2 + (1 + (1 + (1 + (kEV d Kq (σ.nat (V.nB + 11)) + 3))))) ?_ (by unfold kPT; omega)
    (fun _ h => h)
  refine runs_seq (runs_aget (by lay) (by lay) (by lay) hk) (fun σ2 e2 => ?_)
  refine runs_seq (runs_sop2 (by lay) (by lay) (by lay) .mul) (fun σ3 e3 => ?_)
  refine runs_seq (runs_sconst (by lay) 400) (fun σ4 e4 => ?_)
  refine runs_seq (runs_sop2 (by lay) (by lay) (by lay) .div) (fun σ5 e5 => ?_)
  have k5 : G σ5 := by
    rw [e5, e4, e3, e2]
    exact own _ _ _ (by simp) (own _ _ _ (by simp) (own _ _ _ (by simp) (own _ _ _ (by simp) (keep_refl hI))))
  have n5 : σ5.nat = σ.nat := by rw [e5, e4, e3, e2]; rfl
  have a5 : σ5.arr = σ.arr := by rw [e5, e4, e3, e2]; rfl
  have hvi : σ.arr (V.aB + 3) i = σ.vec (V.aB + 3) i := rfl
  have s69 : σ5.sc (V.sB + 69) = σ.vec (V.aB + 3) i := by rw [e5, e4, e3, e2]; simp [hi, hvi]
  have s68 : σ5.sc (V.sB + 68) = σ.sc (V.sB + 100) * σ.vec (V.aB + 3) i / 400 := by
    rw [e5, e4, e3, e2]; simp [Op2.eval, hi, hvi]
  have s61 : σ5.sc (V.sB + 61) = σ.sc (V.sB + 61) := by rw [e5, e4, e3, e2]; simp
  have s63 : σ5.sc (V.sB + 63) = 0 := by rw [e5, e4, e3, e2]; simp [h63]
  refine runs_seq (runs_mono (runs_ev1Code hp hmem hIq (idx := V.nB + 7) (s := V.sB + 69) (η := V.sB + 68)
    ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ σ5 (by rw [n5, hd]) (by rw [n5, h1]) k5.1 i
    (by rw [n5, hi])) (le_of_eq (by rw [n5])) (fun _ h => h)) (fun σ6 h6 => ?_)
  obtain ⟨hO, k6⟩ := h6
  have hg : oGaugeValCap Q (σ5.vec V.a0) (σ5.sc V.r) (σ5.sc V.R) (σ5.nat (V.nB + 11))
      (σ5.vec (V.aB + 2) + σ5.sc (V.sB + 69) • oUnit i) (σ5.sc (V.sB + 68)) =
      gev Q V σ (σ.vec (V.aB + 2) + σ.vec (V.aB + 3) i • oUnit i) (σ.sc (V.sB + 100) * σ.vec (V.aB + 3) i / 400) := by
    rw [s69, s68, n5, Env.vec_of_arr a5, Env.vec_of_arr a5, k5.sc (by nmemS) hp.r_sQ, k5.sc (by nmemS) hp.R_sQ]
    rfl
  rw [hg] at hO
  have g6 : G σ6 := keep_trans k5 (keep_mono k6 (fun _ h => h)
    (by intro j hj; simp only [valS, List.mem_cons, List.mem_range'_1] at hj ⊢; omega)
    (by intro j hj; simp only [List.mem_cons, List.not_mem_nil, or_false] at hj ⊢; omega))
  have r63 : σ6.sc (V.sB + 63) = 0 := by rw [k6.sc (by nmemS) (hp.sB_sQ (by omega) (by omega)), s63]
  have r61 : σ6.sc (V.sB + 61) = σ.sc (V.sB + 61) := by
    rw [k6.sc (by nmemS) (hp.sB_sQ (by omega) (by omega)), s61]
  have r4 : σ6.vec (V.aB + 4) = σ.vec (V.aB + 4) := by
    rw [k6.vec (by nmemS) (hp.aB_aQ (by omega) (by omega)), Env.vec_of_arr a5]
  have i6 : σ6.nat (V.nB + 7) = i := by
    rw [k6.nat (by nmemS) (hp.nN_nQ (by omega) (by omega)), n5, hi]
  cases hv : gev Q V σ (σ.vec (V.aB + 2) + σ.vec (V.aB + 3) i • oUnit i)
      (σ.sc (V.sB + 100) * σ.vec (V.aB + 3) i / 400) with
  | none =>
    rw [hv] at hO
    refine runs_mono (runs_ifS_f (by lay) (by lay) (by rw [r63, hO]; exact lt_irrefl 0)
      (runs_sconst (by lay) 0)) (by omega) (fun σ7 e7 => ?_)
    subst e7
    exact ⟨fun _ => ⟨by simp, by rw [Env.setSc_vec, r4]⟩, (fun _ h => nomatch h),
      own _ _ _ (by simp) g6⟩
  | some v =>
    rw [hv] at hO
    obtain ⟨o17, o18⟩ := hO
    refine runs_mono (runs_ifS_t (by lay) (by lay) (by rw [r63, o17]; exact one_pos)
      (runs_aset (by lay) (by lay) (by lay) (by rw [i6]; exact lt_asz i.isLt))) (by omega) (fun σ7 e7 => ?_)
    subst e7
    refine ⟨(fun h => nomatch h), fun v' h => ?_, ?_⟩
    · cases h
      refine ⟨by simp [r61], ?_⟩
      rw [i6, Env.setArr_vec_self, r4, o18]
    · exact keep_own hIq hON hOS hOA g6 (frame_setArr _ _ _ _) (by simp) (by simp) (by simp)

/-- The step bound of the loop of the values `v⁺`. -/
def kPL (d Kq B : ℕ) : ℕ := d * (kPT d Kq B + 3) + 3

set_option maxHeartbeats 4000000 in
open Classical in
/-- The loop of the values `v⁺`: `oValsAll` at the points `y + δ_j e_j` with errors `τ δ_j/400`. -/
theorem runs_sepPlusLoop {Q : Set (Fin d → ℝ)} {Iq : Env d → Prop} {Kq : ℕ} {nsQ ssQ asQ : List ℕ}
    (hp : V.Ok L nsQ ssQ asQ) (hmem : MemRule L w memQ V Q Iq Kq nsQ ssQ asQ) (hIq : IqRule V Iq)
    (σ : Env d) (hd : σ.nat V.dv = d) (h1 : σ.nat V.one = 1) (hI : Iq σ) (h63 : σ.sc (V.sB + 63) = 0) :
    Runs L w (forN (V.nB + 7) V.dv V.one (sepPlusTurn L memQ V)) σ (kPL d Kq (σ.nat (V.nB + 11)))
      (fun σ' => (oValsAll (gev Q V σ) (fun j => σ.vec (V.aB + 2) + σ.vec (V.aB + 3) j • oUnit j)
          (fun j => σ.sc (V.sB + 100) * σ.vec (V.aB + 3) j / 400) = none → σ'.sc (V.sB + 61) = 0) ∧
        (∀ vp, oValsAll (gev Q V σ) (fun j => σ.vec (V.aB + 2) + σ.vec (V.aB + 3) j • oUnit j)
          (fun j => σ.sc (V.sB + 100) * σ.vec (V.aB + 3) j / 400) = some vp →
          σ'.sc (V.sB + 61) = σ.sc (V.sB + 61) ∧ σ'.vec (V.aB + 4) = vp) ∧
        KP Iq nsQ ssQ asQ (List.range' V.nB 8) (valS V) [V.aB, V.aB + 1, V.aB + 4, V.qv] σ σ') := by
  layout_facts
  have hON : ∀ j ∈ List.range' V.nB 8, j ∈ apN V := by mem_tac
  have hOS : ∀ j ∈ valS V, j ∈ apS V := by mem_tac
  have hOA : ∀ j ∈ [V.aB, V.aB + 1, V.aB + 4, V.qv], j ∈ apA V := by mem_tac
  let G : Env d → Prop := KP Iq nsQ ssQ asQ (List.range' V.nB 8) (valS V) [V.aB, V.aB + 1, V.aB + 4, V.qv] σ
  have own7 : ∀ σa (v : ℕ), G σa → G (σa.setNat (V.nB + 7) v) :=
    fun σa v g => keep_own hIq hON hOS hOA g (frame_setNat _ _ _)
      (by intro j hj; simp only [List.mem_singleton] at hj; subst hj; simp only [List.mem_range'_1]; omega)
      (by simp) (by simp)
  let J : ℕ → Env d → Prop := fun t σ' =>
    valsInv (gev Q V σ) (fun j => σ.vec (V.aB + 2) + σ.vec (V.aB + 3) j • oUnit j)
      (fun j => σ.sc (V.sB + 100) * σ.vec (V.aB + 3) j / 400) (σ.sc (V.sB + 61)) t (σ'.sc (V.sB + 61))
      (σ'.vec (V.aB + 4)) ∧ G σ'
  refine runs_mono (runs_forN (by lay) (by lay) (by lay) (by lay) (by lay) d (kPT d Kq (σ.nat (V.nB + 11))) J σ hd
    h1 ⟨valsInv_zero _ _ _ _ _, own7 _ _ (keep_refl hI)⟩ ?_) (le_of_eq rfl)
    (fun σ' h => ⟨(valsInv_final h.1.1).1, (valsInv_final h.1.1).2, h.1.2⟩)
  intro t ht σ' hJ hit hnt hot
  obtain ⟨hv, k⟩ := hJ
  have e11 : σ'.nat (V.nB + 11) = σ.nat (V.nB + 11) := k.nat (by nmemS) (hp.nN_nQ (by omega) (by omega))
  have hg : gev Q V σ' = gev Q V σ := gev_congr hp k (by nmemS) (by nmemS) (by nmemS) (by nmemS)
  have y' : σ'.vec (V.aB + 2) = σ.vec (V.aB + 2) := k.vec (by nmemS) (hp.aB_aQ (by omega) (by omega))
  have δ' : σ'.vec (V.aB + 3) = σ.vec (V.aB + 3) := k.vec (by nmemS) (hp.aB_aQ (by omega) (by omega))
  have τ' : σ'.sc (V.sB + 100) = σ.sc (V.sB + 100) := k.sc (by nmemS) (hp.sB_sQ (by omega) (by omega))
  have z' : σ'.sc (V.sB + 63) = 0 := by rw [k.sc (by nmemS) (hp.sB_sQ (by omega) (by omega)), h63]
  refine runs_mono (runs_sepPlusTurn hp hmem hIq σ' hnt hot k.1 ⟨t, ht⟩ hit z') (le_of_eq (by rw [e11]))
    (fun σ'' h'' => ?_)
  obtain ⟨hn, hs, k''⟩ := h''
  rw [hg, y', δ', τ'] at hn hs
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [k''.nat (by nmemS) (hp.nN_nQ (by omega) (by omega)), hit]
  · rw [k''.nat (by nmemS) hp.dv_nQ, hnt]
  · rw [k''.nat (by nmemS) hp.one_nQ, hot]
  · refine ⟨?_, own7 _ _ (keep_trans k (keep_mono k'' (by
      intro j hj; simp only [List.mem_range'_1] at hj ⊢; omega) (fun _ h => h) (fun _ h => h)))⟩
    show valsInv _ _ _ _ _ ((σ''.setNat _ _).sc _) ((σ''.setNat _ _).vec _)
    rw [Env.setNat_sc, Env.setNat_vec]
    cases hx : gev Q V σ (σ.vec (V.aB + 2) + σ.vec (V.aB + 3) ⟨t, ht⟩ • oUnit ⟨t, ht⟩)
        (σ.sc (V.sB + 100) * σ.vec (V.aB + 3) ⟨t, ht⟩ / 400) with
    | none =>
      obtain ⟨f0, f4⟩ := hn hx
      rw [f0, f4]; exact valsInv_none hv ⟨t, ht⟩ rfl hx
    | some x =>
      obtain ⟨f0, f4⟩ := hs x hx
      rw [f0, f4]; exact valsInv_some hv ⟨t, ht⟩ rfl hx

/-- The step bound of one turn of the values `v⁻`. -/
def kMT (d Kq B : ℕ) : ℕ := kEV d Kq B + 9

set_option maxHeartbeats 4000000 in
open Classical in
/-- One turn of the values `v⁻`: the value at `y - δ_i e_i` with error `τ δ_i/400` into `v⁻_i`, or the flag `0`. -/
theorem runs_sepMinusTurn {Q : Set (Fin d → ℝ)} {Iq : Env d → Prop} {Kq : ℕ} {nsQ ssQ asQ : List ℕ}
    (hp : V.Ok L nsQ ssQ asQ) (hmem : MemRule L w memQ V Q Iq Kq nsQ ssQ asQ) (hIq : IqRule V Iq)
    (σ : Env d) (hd : σ.nat V.dv = d) (h1 : σ.nat V.one = 1) (hI : Iq σ) (i : Fin d)
    (hi : σ.nat (V.nB + 7) = i) (h63 : σ.sc (V.sB + 63) = 0) :
    Runs L w (sepMinusTurn L memQ V) σ (kMT d Kq (σ.nat (V.nB + 11)))
      (fun σ' => (gev Q V σ (σ.vec (V.aB + 2) - σ.vec (V.aB + 3) i • oUnit i)
          (σ.sc (V.sB + 100) * σ.vec (V.aB + 3) i / 400) = none →
          σ'.sc (V.sB + 61) = 0 ∧ σ'.vec (V.aB + 5) = σ.vec (V.aB + 5)) ∧
        (∀ v, gev Q V σ (σ.vec (V.aB + 2) - σ.vec (V.aB + 3) i • oUnit i)
          (σ.sc (V.sB + 100) * σ.vec (V.aB + 3) i / 400) = some v →
          σ'.sc (V.sB + 61) = σ.sc (V.sB + 61) ∧ σ'.vec (V.aB + 5) = Function.update (σ.vec (V.aB + 5)) i v) ∧
        KP Iq nsQ ssQ asQ (List.range' V.nB 5) (valS V) [V.aB, V.aB + 1, V.aB + 5, V.qv] σ σ') := by
  layout_facts
  have hON : ∀ j ∈ List.range' V.nB 5, j ∈ apN V := by mem_tac
  have hOS : ∀ j ∈ valS V, j ∈ apS V := by mem_tac
  have hOA : ∀ j ∈ [V.aB, V.aB + 1, V.aB + 5, V.qv], j ∈ apA V := by mem_tac
  let G : Env d → Prop := KP Iq nsQ ssQ asQ (List.range' V.nB 5) (valS V) [V.aB, V.aB + 1, V.aB + 5, V.qv] σ
  have own : ∀ σa (q : ℕ) (v : ℝ), q ∈ valS V → G σa → G (σa.setSc q v) :=
    fun σa q v hq g => keep_own hIq hON hOS hOA g (frame_setSc _ _ _) (by simp) (by simpa using hq) (by simp)
  have hk : σ.nat (V.nB + 7) < asz d := by rw [hi]; exact lt_asz i.isLt
  unfold sepMinusTurn
  refine runs_mono (K := 2 + (1 + (1 + (1 + (1 + (kEV d Kq (σ.nat (V.nB + 11)) + 3)))))) ?_ (by unfold kMT; omega)
    (fun _ h => h)
  refine runs_seq (runs_aget (by lay) (by lay) (by lay) hk) (fun σ2 e2 => ?_)
  refine runs_seq (runs_sop2 (by lay) (by lay) (by lay) .sub) (fun σ3 e3 => ?_)
  refine runs_seq (runs_sop2 (by lay) (by lay) (by lay) .mul) (fun σ34 e34 => ?_)
  refine runs_seq (runs_sconst (by lay) 400) (fun σ4 e4 => ?_)
  refine runs_seq (runs_sop2 (by lay) (by lay) (by lay) .div) (fun σ5 e5 => ?_)
  have k5 : G σ5 := by
    rw [e5, e4, e34, e3, e2]
    exact own _ _ _ (by simp) (own _ _ _ (by simp) (own _ _ _ (by simp) (own _ _ _ (by simp) (own _ _ _ (by simp)
      (keep_refl hI)))))
  have n5 : σ5.nat = σ.nat := by rw [e5, e4, e34, e3, e2]; rfl
  have a5 : σ5.arr = σ.arr := by rw [e5, e4, e34, e3, e2]; rfl
  have hvi : σ.arr (V.aB + 3) i = σ.vec (V.aB + 3) i := rfl
  have s69 : σ5.sc (V.sB + 69) = 0 - σ.vec (V.aB + 3) i := by rw [e5, e4, e34, e3, e2]; simp [Op2.eval, hi, hvi, h63]
  have s68 : σ5.sc (V.sB + 68) = σ.sc (V.sB + 100) * σ.vec (V.aB + 3) i / 400 := by
    rw [e5, e4, e34, e3, e2]; simp [Op2.eval, hi, hvi]
  have s61 : σ5.sc (V.sB + 61) = σ.sc (V.sB + 61) := by rw [e5, e4, e34, e3, e2]; simp
  have s63 : σ5.sc (V.sB + 63) = 0 := by rw [e5, e4, e34, e3, e2]; simp [h63]
  refine runs_seq (runs_mono (runs_ev1Code hp hmem hIq (idx := V.nB + 7) (s := V.sB + 69) (η := V.sB + 68)
    ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ σ5 (by rw [n5, hd]) (by rw [n5, h1]) k5.1 i
    (by rw [n5, hi])) (le_of_eq (by rw [n5])) (fun _ h => h)) (fun σ6 h6 => ?_)
  obtain ⟨hO, k6⟩ := h6
  have hg : oGaugeValCap Q (σ5.vec V.a0) (σ5.sc V.r) (σ5.sc V.R) (σ5.nat (V.nB + 11))
      (σ5.vec (V.aB + 2) + σ5.sc (V.sB + 69) • oUnit i) (σ5.sc (V.sB + 68)) =
      gev Q V σ (σ.vec (V.aB + 2) - σ.vec (V.aB + 3) i • oUnit i) (σ.sc (V.sB + 100) * σ.vec (V.aB + 3) i / 400) := by
    rw [s69, s68, n5, Env.vec_of_arr a5, Env.vec_of_arr a5, k5.sc (by nmemS) hp.r_sQ, k5.sc (by nmemS) hp.R_sQ,
      add_zero_sub_smul]
    rfl
  rw [hg] at hO
  have g6 : G σ6 := keep_trans k5 (keep_mono k6 (fun _ h => h)
    (by intro j hj; simp only [valS, List.mem_cons, List.mem_range'_1] at hj ⊢; omega)
    (by intro j hj; simp only [List.mem_cons, List.not_mem_nil, or_false] at hj ⊢; omega))
  have r63 : σ6.sc (V.sB + 63) = 0 := by rw [k6.sc (by nmemS) (hp.sB_sQ (by omega) (by omega)), s63]
  have r61 : σ6.sc (V.sB + 61) = σ.sc (V.sB + 61) := by
    rw [k6.sc (by nmemS) (hp.sB_sQ (by omega) (by omega)), s61]
  have r4 : σ6.vec (V.aB + 5) = σ.vec (V.aB + 5) := by
    rw [k6.vec (by nmemS) (hp.aB_aQ (by omega) (by omega)), Env.vec_of_arr a5]
  have i6 : σ6.nat (V.nB + 7) = i := by
    rw [k6.nat (by nmemS) (hp.nN_nQ (by omega) (by omega)), n5, hi]
  cases hv : gev Q V σ (σ.vec (V.aB + 2) - σ.vec (V.aB + 3) i • oUnit i)
      (σ.sc (V.sB + 100) * σ.vec (V.aB + 3) i / 400) with
  | none =>
    rw [hv] at hO
    refine runs_mono (runs_ifS_f (by lay) (by lay) (by rw [r63, hO]; exact lt_irrefl 0)
      (runs_sconst (by lay) 0)) (by omega) (fun σ7 e7 => ?_)
    subst e7
    exact ⟨fun _ => ⟨by simp, by rw [Env.setSc_vec, r4]⟩, (fun _ h => nomatch h),
      own _ _ _ (by simp) g6⟩
  | some v =>
    rw [hv] at hO
    obtain ⟨o17, o18⟩ := hO
    refine runs_mono (runs_ifS_t (by lay) (by lay) (by rw [r63, o17]; exact one_pos)
      (runs_aset (by lay) (by lay) (by lay) (by rw [i6]; exact lt_asz i.isLt))) (by omega) (fun σ7 e7 => ?_)
    subst e7
    refine ⟨(fun h => nomatch h), fun v' h => ?_, ?_⟩
    · cases h
      refine ⟨by simp [r61], ?_⟩
      rw [i6, Env.setArr_vec_self, r4, o18]
    · exact keep_own hIq hON hOS hOA g6 (frame_setArr _ _ _ _) (by simp) (by simp) (by simp)

/-- The step bound of the loop of the values `v⁻`. -/
def kML (d Kq B : ℕ) : ℕ := d * (kMT d Kq B + 3) + 3

set_option maxHeartbeats 4000000 in
open Classical in
/-- The loop of the values `v⁻`: `oValsAll` at the points `y - δ_j e_j` with errors `τ δ_j/400`. -/
theorem runs_sepMinusLoop {Q : Set (Fin d → ℝ)} {Iq : Env d → Prop} {Kq : ℕ} {nsQ ssQ asQ : List ℕ}
    (hp : V.Ok L nsQ ssQ asQ) (hmem : MemRule L w memQ V Q Iq Kq nsQ ssQ asQ) (hIq : IqRule V Iq)
    (σ : Env d) (hd : σ.nat V.dv = d) (h1 : σ.nat V.one = 1) (hI : Iq σ) (h63 : σ.sc (V.sB + 63) = 0) :
    Runs L w (forN (V.nB + 7) V.dv V.one (sepMinusTurn L memQ V)) σ (kML d Kq (σ.nat (V.nB + 11)))
      (fun σ' => (oValsAll (gev Q V σ) (fun j => σ.vec (V.aB + 2) - σ.vec (V.aB + 3) j • oUnit j)
          (fun j => σ.sc (V.sB + 100) * σ.vec (V.aB + 3) j / 400) = none → σ'.sc (V.sB + 61) = 0) ∧
        (∀ vp, oValsAll (gev Q V σ) (fun j => σ.vec (V.aB + 2) - σ.vec (V.aB + 3) j • oUnit j)
          (fun j => σ.sc (V.sB + 100) * σ.vec (V.aB + 3) j / 400) = some vp →
          σ'.sc (V.sB + 61) = σ.sc (V.sB + 61) ∧ σ'.vec (V.aB + 5) = vp) ∧
        KP Iq nsQ ssQ asQ (List.range' V.nB 8) (valS V) [V.aB, V.aB + 1, V.aB + 5, V.qv] σ σ') := by
  layout_facts
  have hON : ∀ j ∈ List.range' V.nB 8, j ∈ apN V := by mem_tac
  have hOS : ∀ j ∈ valS V, j ∈ apS V := by mem_tac
  have hOA : ∀ j ∈ [V.aB, V.aB + 1, V.aB + 5, V.qv], j ∈ apA V := by mem_tac
  let G : Env d → Prop := KP Iq nsQ ssQ asQ (List.range' V.nB 8) (valS V) [V.aB, V.aB + 1, V.aB + 5, V.qv] σ
  have own7 : ∀ σa (v : ℕ), G σa → G (σa.setNat (V.nB + 7) v) :=
    fun σa v g => keep_own hIq hON hOS hOA g (frame_setNat _ _ _)
      (by intro j hj; simp only [List.mem_singleton] at hj; subst hj; simp only [List.mem_range'_1]; omega)
      (by simp) (by simp)
  let J : ℕ → Env d → Prop := fun t σ' =>
    valsInv (gev Q V σ) (fun j => σ.vec (V.aB + 2) - σ.vec (V.aB + 3) j • oUnit j)
      (fun j => σ.sc (V.sB + 100) * σ.vec (V.aB + 3) j / 400) (σ.sc (V.sB + 61)) t (σ'.sc (V.sB + 61))
      (σ'.vec (V.aB + 5)) ∧ G σ'
  refine runs_mono (runs_forN (by lay) (by lay) (by lay) (by lay) (by lay) d (kMT d Kq (σ.nat (V.nB + 11))) J σ hd
    h1 ⟨valsInv_zero _ _ _ _ _, own7 _ _ (keep_refl hI)⟩ ?_) (le_of_eq rfl)
    (fun σ' h => ⟨(valsInv_final h.1.1).1, (valsInv_final h.1.1).2, h.1.2⟩)
  intro t ht σ' hJ hit hnt hot
  obtain ⟨hv, k⟩ := hJ
  have e11 : σ'.nat (V.nB + 11) = σ.nat (V.nB + 11) := k.nat (by nmemS) (hp.nN_nQ (by omega) (by omega))
  have hg : gev Q V σ' = gev Q V σ := gev_congr hp k (by nmemS) (by nmemS) (by nmemS) (by nmemS)
  have y' : σ'.vec (V.aB + 2) = σ.vec (V.aB + 2) := k.vec (by nmemS) (hp.aB_aQ (by omega) (by omega))
  have δ' : σ'.vec (V.aB + 3) = σ.vec (V.aB + 3) := k.vec (by nmemS) (hp.aB_aQ (by omega) (by omega))
  have τ' : σ'.sc (V.sB + 100) = σ.sc (V.sB + 100) := k.sc (by nmemS) (hp.sB_sQ (by omega) (by omega))
  have z' : σ'.sc (V.sB + 63) = 0 := by rw [k.sc (by nmemS) (hp.sB_sQ (by omega) (by omega)), h63]
  refine runs_mono (runs_sepMinusTurn hp hmem hIq σ' hnt hot k.1 ⟨t, ht⟩ hit z') (le_of_eq (by rw [e11]))
    (fun σ'' h'' => ?_)
  obtain ⟨hn, hs, k''⟩ := h''
  rw [hg, y', δ', τ'] at hn hs
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [k''.nat (by nmemS) (hp.nN_nQ (by omega) (by omega)), hit]
  · rw [k''.nat (by nmemS) hp.dv_nQ, hnt]
  · rw [k''.nat (by nmemS) hp.one_nQ, hot]
  · refine ⟨?_, own7 _ _ (keep_trans k (keep_mono k'' (by
      intro j hj; simp only [List.mem_range'_1] at hj ⊢; omega) (fun _ h => h) (fun _ h => h)))⟩
    show valsInv _ _ _ _ _ ((σ''.setNat _ _).sc _) ((σ''.setNat _ _).vec _)
    rw [Env.setNat_sc, Env.setNat_vec]
    cases hx : gev Q V σ (σ.vec (V.aB + 2) - σ.vec (V.aB + 3) ⟨t, ht⟩ • oUnit ⟨t, ht⟩)
        (σ.sc (V.sB + 100) * σ.vec (V.aB + 3) ⟨t, ht⟩ / 400) with
    | none =>
      obtain ⟨f0, f4⟩ := hn hx
      rw [f0, f4]; exact valsInv_none hv ⟨t, ht⟩ rfl hx
    | some x =>
      obtain ⟨f0, f4⟩ := hs x hx
      rw [f0, f4]; exact valsInv_some hv ⟨t, ht⟩ rfl hx

set_option maxHeartbeats 2000000 in
/-- The loop of `g`: `g_j = (v⁺_j - v⁻_j)/(2 δ_j)` from the arrays `aB + 4`, `aB + 5`, `aB + 3` into `aB + 6`. -/
theorem runs_sepGLoop {nsQ ssQ asQ : List ℕ} (hp : V.Ok L nsQ ssQ asQ) (σ : Env d) (hd : σ.nat V.dv = d)
    (h1 : σ.nat V.one = 1) :
    Runs L w (forN (V.nB + 7) V.dv V.one (sepGTurn L V)) σ (d * (12 + 3) + 3)
      (fun σ' => σ'.vec (V.aB + 6) =
          (fun j => (σ.vec (V.aB + 4) j - σ.vec (V.aB + 5) j) / (2 * σ.vec (V.aB + 3) j)) ∧
        Env.Frame σ σ' [V.nB + 7] [V.sB + 65, V.sB + 66, V.sB + 70] [V.aB + 6]) := by
  layout_facts
  let J : ℕ → Env d → Prop := fun t σ' => (∀ j : Fin d, j.val < t →
      σ'.vec (V.aB + 6) j = (σ.vec (V.aB + 4) j - σ.vec (V.aB + 5) j) / (2 * σ.vec (V.aB + 3) j)) ∧
    Env.Frame σ σ' [V.nB + 7] [V.sB + 65, V.sB + 66, V.sB + 70] [V.aB + 6]
  refine runs_mono (runs_forN (by lay) (by lay) (by lay) (by lay) (by lay) d 12 J σ hd h1
    ⟨fun j hj => absurd hj (Nat.not_lt_zero _), Env.Frame.setNat (Env.Frame.refl _ _ _ _) (by simp) 0⟩ ?_) le_rfl
    (fun σ' h => ⟨funext fun j => h.1.1 j j.isLt, h.1.2⟩)
  intro t ht σ' hJ hit hnt hot
  obtain ⟨hg, hf⟩ := hJ
  have a4 : σ'.arr (V.aB + 4) t = σ.vec (V.aB + 4) ⟨t, ht⟩ := congrFun (Env.Frame.vec hf (by simp)) ⟨t, ht⟩
  have a5 : σ'.arr (V.aB + 5) t = σ.vec (V.aB + 5) ⟨t, ht⟩ := congrFun (Env.Frame.vec hf (by simp)) ⟨t, ht⟩
  have a3 : σ'.arr (V.aB + 3) t = σ.vec (V.aB + 3) ⟨t, ht⟩ := congrFun (Env.Frame.vec hf (by simp)) ⟨t, ht⟩
  have hk : σ'.nat (V.nB + 7) < asz d := by rw [hit]; exact lt_asz ht
  unfold sepGTurn
  refine runs_mono (K := 2 + (2 + (1 + (2 + (1 + (1 + (1 + 2))))))) ?_ le_rfl (fun _ h => h)
  refine runs_seq (runs_aget (by lay) (by lay) (by lay) hk) (fun σ2 e2 => ?_)
  refine runs_seq (runs_aget (by lay) (by lay) (by lay) (by rw [e2]; exact hk)) (fun σ3 e3 => ?_)
  refine runs_seq (runs_sop2 (by lay) (by lay) (by lay) .sub) (fun σ4 e4 => ?_)
  refine runs_seq (runs_aget (by lay) (by lay) (by lay) (by rw [e4, e3, e2]; exact hk)) (fun σ5 e5 => ?_)
  refine runs_seq (runs_sconst (by lay) 2) (fun σ6 e6 => ?_)
  refine runs_seq (runs_sop2 (by lay) (by lay) (by lay) .mul) (fun σ7 e7 => ?_)
  refine runs_seq (runs_sop2 (by lay) (by lay) (by lay) .div) (fun σ8 e8 => ?_)
  have n8 : σ8.nat = σ'.nat := by rw [e8, e7, e6, e5, e4, e3, e2]; rfl
  refine runs_mono (runs_aset (by lay) (by lay) (by lay) (by rw [n8]; exact hk)) le_rfl (fun σ9 e9 => ?_)
  have v66 : σ8.sc (V.sB + 66) =
      (σ.vec (V.aB + 4) ⟨t, ht⟩ - σ.vec (V.aB + 5) ⟨t, ht⟩) / (2 * σ.vec (V.aB + 3) ⟨t, ht⟩) := by
    rw [e8, e7, e6, e5, e4, e3, e2]; simp [Op2.eval, hit, a4, a5, a3]
  have f8 : Env.Frame σ σ8 [V.nB + 7] [V.sB + 65, V.sB + 66, V.sB + 70] [V.aB + 6] := by
    rw [e8, e7, e6, e5, e4, e3, e2]
    exact Env.Frame.setSc (Env.Frame.setSc (Env.Frame.setSc (Env.Frame.setSc (Env.Frame.setSc (Env.Frame.setSc
      (Env.Frame.setSc hf (by simp) _) (by simp) _) (by simp) _) (by simp) _) (by simp) _) (by simp) _) (by simp) _
  have hv8 : σ8.vec (V.aB + 6) = σ'.vec (V.aB + 6) := by rw [e8, e7, e6, e5, e4, e3, e2]; rfl
  have hit' : σ8.nat (V.nB + 7) = ((⟨t, ht⟩ : Fin d) : ℕ) := by rw [n8]; exact hit
  refine ⟨by rw [e9]; exact (congrFun n8 _).trans hit, by rw [e9]; exact (congrFun n8 _).trans hnt,
    by rw [e9]; exact (congrFun n8 _).trans hot, ?_, ?_⟩
  · intro j hj
    show (σ9.setNat _ _).vec _ j = _
    rw [Env.setNat_vec, e9, hit', Env.setArr_vec_self]
    by_cases hjt : j = ⟨t, ht⟩
    · subst hjt; rw [Function.update_self, v66]
    · rw [Function.update_of_ne hjt, hv8]
      exact hg j (by have : j.val ≠ t := fun h => hjt (Fin.ext h); omega)
  · exact Env.Frame.setNat (by rw [e9]; exact frame_setArr_of f8 (by simp) _ _) (by simp) _

/-- The step bound of the tail of SEP. -/
def kTail (d Kq B : ℕ) : ℕ :=
  1 + (2 + ((d * (5 + 3) + 3) + (1 + (1 + (1 + (kGV d Kq B +
    ((kPL d Kq B + (kML d Kq B + (d * (12 + 3) + 3))) + 1)))))))

set_option maxHeartbeats 8000000 in
open Classical in
/-- The tail of SEP after its searches from the state `st`: `sepTailF`. -/
theorem runs_sepTail {Q : Set (Fin d → ℝ)} {Iq : Env d → Prop} {Kq : ℕ} {nsQ ssQ asQ : List ℕ}
    (hp : V.Ok L nsQ ssQ asQ) (hmem : MemRule L w memQ V Q Iq Kq nsQ ssQ asQ) (hIq : IqRule V Iq)
    (σ : Env d) (hd : σ.nat V.dv = d) (h1 : σ.nat V.one = 1) (hI : Iq σ) (h0 : 0 < d) (st : SepSt d)
    (hst : SRel V (some st) σ) (h63 : σ.sc (V.sB + 63) = 0) :
    Runs L w (sepTail L memQ V) σ (kTail d Kq (σ.nat (V.nB + 11)))
      (fun σ' => SepRes V (sepTailF (gev Q V σ) (σ.sc (V.sB + 100)) st) σ' ∧
        KP Iq nsQ ssQ asQ (List.range' V.nB 8) (sepS V) (sepA V) σ σ') := by
  layout_facts
  have hON : ∀ j ∈ List.range' V.nB 8, j ∈ apN V := by mem_tac
  have hOS : ∀ j ∈ sepS V, j ∈ apS V := by mem_tac
  have hOA : ∀ j ∈ sepA V, j ∈ apA V := by mem_tac
  let G : Env d → Prop := KP Iq nsQ ssQ asQ (List.range' V.nB 8) (sepS V) (sepA V) σ
  have ownS : ∀ σa (q : ℕ) (v : ℝ), V.sB ≤ q → q < V.sB + 71 → G σa → G (σa.setSc q v) :=
    fun σa q v h1 h2 g => keep_own hIq hON hOS hOA g (frame_setSc _ _ _) (by simp)
      (by intro j hj; simp only [List.mem_singleton] at hj; subst hj; simp only [List.mem_range'_1]; omega) (by simp)
  have ownN : ∀ σa (v : ℕ), G σa → G (σa.setNat (V.nB + 7) v) :=
    fun σa v g => keep_own hIq hON hOS hOA g (frame_setNat _ _ _)
      (by intro j hj; simp only [List.mem_singleton] at hj; subst hj; simp only [List.mem_range'_1]; omega)
      (by simp) (by simp)
  obtain ⟨f61, hy, hl, hδ⟩ := hst
  obtain ⟨B, hB⟩ : ∃ B, σ.nat (V.nB + 11) = B := ⟨_, rfl⟩
  rw [hB]
  unfold sepTail
  refine runs_seq (runs_nconst (by lay) 0) (fun σ1 e1 => ?_)
  have hk1 : σ1.nat (V.nB + 7) < asz d := by rw [e1]; simp only [Env.setNat_nat, if_true]; exact lt_asz h0
  refine runs_seq (runs_aget (by lay) (by lay) (by lay) hk1) (fun σ2 e2 => ?_)
  have n2 : ∀ j, j ≠ V.nB + 7 → σ2.nat j = σ.nat j := fun j hj => by rw [e2, e1]; simp [hj]
  have m2 : ∃ j, σ2.vec (V.aB + 3) j = σ2.sc (V.sB + 67) := ⟨⟨0, h0⟩, by rw [e2, e1]; simp [Env.vec]⟩
  have g2 : G σ2 := by rw [e2, e1]; exact ownS _ _ _ (by omega) (by omega) (ownN _ _ (keep_refl hI))
  have δ2 : σ2.vec (V.aB + 3) = st.2.2 := by rw [e2, e1]; exact hδ
  refine runs_seq (runs_sepMinLoop hp σ2 ((n2 _ (by lay)).trans hd) ((n2 _ (by lay)).trans h1) h0 m2)
    (fun σ3 h3 => ?_)
  obtain ⟨m3, f3⟩ := h3
  have g3 : G σ3 := keep_own hIq hON hOS hOA g2 f3
    (by intro j hj; simp only [List.mem_singleton] at hj; subst hj; simp only [List.mem_range'_1]; omega)
    (by intro j hj; simp only [sepS, List.mem_cons, List.mem_range'_1, List.not_mem_nil, or_false] at hj ⊢; omega) (by simp)
  refine runs_seq (runs_sop2 (by lay) (by lay) (by lay) .mul) (fun σ4 e4 => ?_)
  refine runs_seq (runs_sconst (by lay) 400) (fun σ5 e5 => ?_)
  refine runs_seq (runs_sop2 (by lay) (by lay) (by lay) .div) (fun σ6 e6 => ?_)
  have g6 : G σ6 := by
    rw [e6, e5, e4]
    exact ownS _ _ _ (by omega) (by omega) (ownS _ _ _ (by omega) (by omega) (ownS _ _ _ (by omega) (by omega) g3))
  have s68 : σ6.sc (V.sB + 68) = σ.sc (V.sB + 100) * oMin st.2.2 / 400 := by
    have t3 : σ3.sc (V.sB + 100) = σ.sc (V.sB + 100) := by
      rw [f3.2.1 _ (by simp), e2, e1]; simp
    rw [e6, e5, e4]; simp [Op2.eval, t3, m3, δ2]
  have y6 : σ6.vec (V.aB + 2) = st.1 := by
    rw [e6, e5, e4]; simp only [Env.setSc_vec]; rw [Env.Frame.vec f3 (by simp), e2, e1]; exact hy
  have δ6 : σ6.vec (V.aB + 3) = st.2.2 := by
    rw [e6, e5, e4]; simp only [Env.setSc_vec]; rw [Env.Frame.vec f3 (by simp), δ2]
  have z6 : σ6.sc (V.sB + 63) = 0 := by
    rw [e6, e5, e4]; simp only [Env.setSc_sc]; simp only [show V.sB + 63 ≠ V.sB + 68 by omega,
      show V.sB + 63 ≠ V.sB + 65 by omega, if_false]; rw [f3.2.1 _ (by simp), e2, e1]; simp [h63]
  have o6 : σ6.sc (V.sB + 61) = 1 := by
    rw [e6, e5, e4]; simp only [Env.setSc_sc]; simp only [show V.sB + 61 ≠ V.sB + 68 by omega,
      show V.sB + 61 ≠ V.sB + 65 by omega, if_false]; rw [f3.2.1 _ (by simp), e2, e1]; simp [f61]
  have gN : ∀ σa, G σa → σa.nat V.dv = d ∧ σa.nat V.one = 1 ∧ σa.nat (V.nB + 11) = B := fun σa g =>
    ⟨by rw [g.nat (by nmemS) hp.dv_nQ, hd], by rw [g.nat (by nmemS) hp.one_nQ, h1],
      by rw [g.nat (by nmemS) (hp.nN_nQ (by omega) (by omega)), hB]⟩
  have gE : ∀ σa, G σa → gev Q V σa = gev Q V σ ∧ σa.sc (V.sB + 100) = σ.sc (V.sB + 100) := fun σa g =>
    ⟨gev_congr hp g (by nmemS) (by nmemS) (by nmemS) (by nmemS), g.sc (by nmemS) (hp.sB_sQ (by omega) (by omega))⟩
  obtain ⟨d6, o6', b6⟩ := gN σ6 g6
  refine runs_seq (runs_mono (runs_gvCode hp hmem hIq (x := V.aB + 2) (η := V.sB + 68) (by lay) (by omega) (by lay)
    (by omega) σ6 d6 o6' g6.1) (le_of_eq (by rw [b6])) (fun _ h => h)) (fun σ7 h7 => ?_)
  obtain ⟨hO, k7⟩ := h7
  have hO' : OptRel (gev Q V σ st.1 (σ.sc (V.sB + 100) * oMin st.2.2 / 400)) (σ7.sc (V.sB + 17))
      (σ7.sc (V.sB + 18)) := by
    rw [← (gE σ6 g6).1, ← y6, ← s68]; exact hO
  have g7 : G σ7 := keep_trans g6 (keep_mono k7
    (by intro j hj; simp only [List.mem_range'_1] at hj ⊢; omega)
    (by intro j hj; simp only [List.mem_range'_1] at hj ⊢; omega)
    (by intro j hj; simp only [sepA, List.mem_cons, List.not_mem_nil, or_false] at hj ⊢; omega))
  have kS7' : ∀ x, V.sB + 20 ≤ x → x < V.sB + 128 → σ7.sc x = σ6.sc x := fun x h1 h2 =>
    k7.sc (by simp only [List.mem_range'_1]; omega) (hp.sB_sQ (by omega) (by omega))
  have z7 : σ7.sc (V.sB + 63) = 0 := by rw [kS7' _ (by omega) (by omega), z6]
  have o7 : σ7.sc (V.sB + 61) = 1 := by rw [kS7' _ (by omega) (by omega), o6]
  have y7 : σ7.vec (V.aB + 2) = st.1 := by rw [k7.vec (by nmemS) (hp.aB_aQ (by omega) (by omega)), y6]
  have δ7 : σ7.vec (V.aB + 3) = st.2.2 := by rw [k7.vec (by nmemS) (hp.aB_aQ (by omega) (by omega)), δ6]
  have hT : sepTailF (gev Q V σ) (σ.sc (V.sB + 100)) st =
      (gev Q V σ st.1 (σ.sc (V.sB + 100) * oMin st.2.2 / 400)).bind (fun _ =>
        (oValsAll (gev Q V σ) (fun i => st.1 + st.2.2 i • oUnit i)
          (fun i => σ.sc (V.sB + 100) * st.2.2 i / 400)).bind (fun vp =>
        (oValsAll (gev Q V σ) (fun i => st.1 - st.2.2 i • oUnit i)
          (fun i => σ.sc (V.sB + 100) * st.2.2 i / 400)).bind (fun vm =>
        some (st.1, fun i => (vp i - vm i) / (2 * st.2.2 i))))) := rfl
  rw [hT]
  cases hv0 : gev Q V σ st.1 (σ.sc (V.sB + 100) * oMin st.2.2 / 400) with
  | none =>
    rw [hv0] at hO'
    refine runs_mono (runs_ifS_f (by lay) (by lay) (by rw [z7, hO']; exact lt_irrefl 0)
      (runs_sconst (by lay) 0)) (by omega) (fun σ8 e8 => ?_)
    subst e8
    exact ⟨by simp [SepRes], ownS _ _ _ (by omega) (by omega) g7⟩
  | some v0 =>
    rw [hv0] at hO'
    obtain ⟨o17, -⟩ := hO'
    refine runs_mono (runs_ifS_t (by lay) (by lay) (by rw [z7, o17]; exact one_pos) ?_) le_rfl (fun _ h => h)
    obtain ⟨d7, o7', b7⟩ := gN σ7 g7
    refine runs_seq (runs_mono (runs_sepPlusLoop hp hmem hIq σ7 d7 o7' g7.1 z7) (le_of_eq (by rw [b7]))
      (fun _ h => h)) (fun σ8 h8 => ?_)
    obtain ⟨p_none, p_some, k8⟩ := h8
    rw [(gE σ7 g7).1, (gE σ7 g7).2, y7, δ7] at p_none p_some
    have g8 : G σ8 := keep_trans g7 (keep_mono k8 (fun _ h => h)
      (by intro j hj; simp only [valS, List.mem_cons, List.mem_range'_1] at hj ⊢; omega)
      (by intro j hj; simp only [sepA, List.mem_cons, List.not_mem_nil, or_false] at hj ⊢; omega))
    have z8 : σ8.sc (V.sB + 63) = 0 := by rw [k8.sc (by nmemS) (hp.sB_sQ (by omega) (by omega)), z7]
    have y8 : σ8.vec (V.aB + 2) = st.1 := by rw [k8.vec (by nmemS) (hp.aB_aQ (by omega) (by omega)), y7]
    have δ8 : σ8.vec (V.aB + 3) = st.2.2 := by rw [k8.vec (by nmemS) (hp.aB_aQ (by omega) (by omega)), δ7]
    obtain ⟨d8, o8', b8⟩ := gN σ8 g8
    refine runs_seq (runs_mono (runs_sepMinusLoop hp hmem hIq σ8 d8 o8' g8.1 z8) (le_of_eq (by rw [b8]))
      (fun _ h => h)) (fun σ9 h9 => ?_)
    obtain ⟨m_none, m_some, k9⟩ := h9
    rw [(gE σ8 g8).1, (gE σ8 g8).2, y8, δ8] at m_none m_some
    have g9 : G σ9 := keep_trans g8 (keep_mono k9 (fun _ h => h)
      (by intro j hj; simp only [valS, List.mem_cons, List.mem_range'_1] at hj ⊢; omega)
      (by intro j hj; simp only [sepA, List.mem_cons, List.not_mem_nil, or_false] at hj ⊢; omega))
    have y9 : σ9.vec (V.aB + 2) = st.1 := by rw [k9.vec (by nmemS) (hp.aB_aQ (by omega) (by omega)), y8]
    have δ9 : σ9.vec (V.aB + 3) = st.2.2 := by rw [k9.vec (by nmemS) (hp.aB_aQ (by omega) (by omega)), δ8]
    have v9 : σ9.vec (V.aB + 4) = σ8.vec (V.aB + 4) := k9.vec (by nmemS) (hp.aB_aQ (by omega) (by omega))
    obtain ⟨d9, o9', -⟩ := gN σ9 g9
    refine runs_mono (runs_sepGLoop hp σ9 d9 o9') le_rfl (fun σ10 h10 => ?_)
    obtain ⟨hg10, f10⟩ := h10
    have g10 : G σ10 := keep_own hIq hON hOS hOA g9 f10
      (by intro j hj; simp only [List.mem_singleton] at hj; subst hj; simp only [List.mem_range'_1]; omega)
      (by intro j hj; simp only [sepS, List.mem_cons, List.mem_range'_1, List.not_mem_nil, or_false] at hj ⊢; omega)
      (by intro j hj; simp only [List.mem_singleton] at hj; subst hj; simp [sepA])
    refine ⟨?_, g10⟩
    have t61 : σ10.sc (V.sB + 61) = σ9.sc (V.sB + 61) := f10.2.1 _ (by simp)
    have y10 : σ10.vec (V.aB + 2) = st.1 := by rw [Env.Frame.vec f10 (by simp), y9]
    simp only [Option.bind_some]
    cases hpv : oValsAll (gev Q V σ) (fun i => st.1 + st.2.2 i • oUnit i)
        (fun i => σ.sc (V.sB + 100) * st.2.2 i / 400) with
    | none =>
      have p0 := p_none hpv
      have h9' : σ9.sc (V.sB + 61) = 0 := by
        cases hmv : oValsAll (gev Q V σ) (fun i => st.1 - st.2.2 i • oUnit i)
            (fun i => σ.sc (V.sB + 100) * st.2.2 i / 400) with
        | none => exact m_none hmv
        | some vm => rw [(m_some vm hmv).1, p0]
      show σ10.sc (V.sB + 61) = 0
      rw [t61, h9']
    | some vp =>
      obtain ⟨p61, p4⟩ := p_some vp hpv
      cases hmv : oValsAll (gev Q V σ) (fun i => st.1 - st.2.2 i • oUnit i)
          (fun i => σ.sc (V.sB + 100) * st.2.2 i / 400) with
      | none =>
        show σ10.sc (V.sB + 61) = 0
        rw [t61, m_none hmv]
      | some vm =>
        obtain ⟨m61, m5⟩ := m_some vm hmv
        refine ⟨?_, y10, ?_⟩
        · rw [t61, m61, p61, o7]
        · rw [hg10, v9, p4, m5, δ9]

/-- The step bound of SEP. -/
def kSC (d Kq B J : ℕ) : ℕ :=
  (d * 7 + 3) + (1 + ((d * 5 + 3) + (1 + (1 + (1 + (1 + (1 + (1 +
    ((d * (kST d Kq B J + 1 + 3) + 3) + (kTail d Kq B + 1))))))))))

set_option maxHeartbeats 8000000 in
open Classical in
/-- The rule of SEP from the array `y0`: `sep` on the gauge values, with `τ` the scalar `sB + 100`, `ℓ₁` the scalar
`sB + 101`, `L = 1/r` and the cap `J` the natural variable `nB + 10`. -/
theorem runs_sepCode {Q : Set (Fin d → ℝ)} {Iq : Env d → Prop} {Kq : ℕ} {nsQ ssQ asQ : List ℕ}
    (hp : V.Ok L nsQ ssQ asQ) (hmem : MemRule L w memQ V Q Iq Kq nsQ ssQ asQ) (hIq : IqRule V Iq)
    {y0 : ℕ} (hy0 : y0 < L.NA) (σ : Env d) (hd : σ.nat V.dv = d) (h1 : σ.nat V.one = 1) (hI : Iq σ)
    (h0 : 0 < d) :
    Runs L w (sepCode L memQ V y0) σ (kSC d Kq (σ.nat (V.nB + 11)) (σ.nat (V.nB + 10)))
      (fun σ' => SepRes V (sep (gev Q V σ) (σ.vec y0) (σ.sc (V.sB + 100)) (σ.sc (V.sB + 101)) (1 / σ.sc V.r)
          (σ.nat (V.nB + 10))) σ' ∧
        KP Iq nsQ ssQ asQ (List.range' V.nB 8) (sepS V) (sepA V) σ σ') := by
  layout_facts
  have hON : ∀ j ∈ List.range' V.nB 8, j ∈ apN V := by mem_tac
  have hOS : ∀ j ∈ sepS V, j ∈ apS V := by mem_tac
  have hOA : ∀ j ∈ sepA V, j ∈ apA V := by mem_tac
  let G : Env d → Prop := KP Iq nsQ ssQ asQ (List.range' V.nB 8) (sepS V) (sepA V) σ
  have ownS : ∀ σa (q : ℕ) (v : ℝ), V.sB ≤ q → q < V.sB + 71 → G σa → G (σa.setSc q v) :=
    fun σa q v h1 h2 g => keep_own hIq hON hOS hOA g (frame_setSc _ _ _) (by simp)
      (by intro j hj; simp only [List.mem_singleton] at hj; subst hj; simp only [List.mem_range'_1]; omega) (by simp)
  have ownN6 : ∀ σa (v : ℕ), G σa → G (σa.setNat (V.nB + 6) v) :=
    fun σa v g => keep_own hIq hON hOS hOA g (frame_setNat _ _ _)
      (by intro j hj; simp only [List.mem_singleton] at hj; subst hj; simp only [List.mem_range'_1]; omega)
      (by simp) (by simp)
  obtain ⟨B, hB⟩ : ∃ B, σ.nat (V.nB + 11) = B := ⟨_, rfl⟩
  obtain ⟨Jc, hJ⟩ : ∃ J, σ.nat (V.nB + 10) = J := ⟨_, rfl⟩
  have gN : ∀ σa, G σa → σa.nat V.dv = d ∧ σa.nat V.one = 1 ∧ σa.nat (V.nB + 11) = B ∧
      σa.nat (V.nB + 10) = Jc := fun σa g =>
    ⟨by rw [g.nat (by nmemS) hp.dv_nQ, hd], by rw [g.nat (by nmemS) hp.one_nQ, h1],
      by rw [g.nat (by nmemS) (hp.nN_nQ (by omega) (by omega)), hB],
      by rw [g.nat (by nmemS) (hp.nN_nQ (by omega) (by omega)), hJ]⟩
  have gE : ∀ σa, G σa → gev Q V σa = gev Q V σ ∧ σa.sc (V.sB + 100) = σ.sc (V.sB + 100) := fun σa g =>
    ⟨gev_congr hp g (by nmemS) (by nmemS) (by nmemS) (by nmemS), g.sc (by nmemS) (hp.sB_sQ (by omega) (by omega))⟩
  rw [hB, hJ]
  unfold sepCode kSC
  refine runs_seq (runs_vcopy σ (by lay) (by lay) (by lay) (by lay) hy0 (by lay) (by lay) (by lay) hd h1)
    (fun σ1 h1' => ?_)
  obtain ⟨y1, f1, -⟩ := h1'
  have g1 : G σ1 := keep_own hIq hON hOS hOA (keep_refl hI) f1
    (by intro j hj; simp only [List.mem_singleton] at hj; subst hj; simp only [List.mem_range'_1]; omega)
    (by intro j hj; simp only [List.mem_singleton] at hj; subst hj; simp only [sepS, List.mem_range'_1]; omega)
    (by intro j hj; simp only [List.mem_singleton] at hj; subst hj; simp [sepA])
  refine runs_seq (runs_sconst (by lay) 0) (fun σ2 e2 => ?_)
  have g2 : G σ2 := by rw [e2]; exact ownS _ _ _ (by omega) (by omega) g1
  obtain ⟨d2, o2, -, -⟩ := gN σ2 g2
  refine runs_seq (runs_vfill σ2 (by lay) (by lay) (by lay) (by lay) (by lay) (by lay) (by lay) d2 o2)
    (fun σ3 h3' => ?_)
  obtain ⟨v3, f3, -⟩ := h3'
  have g3 : G σ3 := keep_own hIq hON hOS hOA g2 f3
    (by intro j hj; simp only [List.mem_singleton] at hj; subst hj; simp only [List.mem_range'_1]; omega)
    (by simp) (by intro j hj; simp only [List.mem_singleton] at hj; subst hj; simp [sepA])
  refine runs_seq (runs_smov (by lay) (by lay)) (fun σ4 e4 => ?_)
  refine runs_seq (runs_sconst (by lay) 1) (fun σ5 e5 => ?_)
  refine runs_seq (runs_sconst (by lay) 1) (fun σ6 e6 => ?_)
  refine runs_seq (runs_sop2 (by lay) (by lay) (by lay) .div) (fun σ7 e7 => ?_)
  refine runs_seq (runs_sconst (by lay) 16) (fun σ8 e8 => ?_)
  refine runs_seq (runs_sop2 (by lay) (by lay) (by lay) .mul) (fun σ9 e9 => ?_)
  have g9 : G σ9 := by
    rw [e9, e8, e7, e6, e5, e4]
    exact ownS _ _ _ (by omega) (by omega) (ownS _ _ _ (by omega) (by omega) (ownS _ _ _ (by omega) (by omega)
      (ownS _ _ _ (by omega) (by omega) (ownS _ _ _ (by omega) (by omega) (ownS _ _ _ (by omega) (by omega) g3)))))
  have r3 : σ3.sc V.r = σ.sc V.r := g3.sc (by nmemS) hp.r_sQ
  have hr60 : V.r ≠ V.sB + 60 := by lay
  have hr61 : V.r ≠ V.sB + 61 := by lay
  have hr64 : V.r ≠ V.sB + 64 := by lay
  have s101 : σ3.sc (V.sB + 101) = σ.sc (V.sB + 101) := g3.sc (by nmemS) (hp.sB_sQ (by omega) (by omega))
  have z3 : σ3.sc (V.sB + 63) = 0 := by
    rw [f3.2.1 _ (by simp), e2]; simp
  have y9 : σ9.vec (V.aB + 2) = σ.vec y0 := by
    rw [e9, e8, e7, e6, e5, e4]; simp only [Env.setSc_vec]
    rw [Env.Frame.vec f3 (by simp), e2, Env.setSc_vec, y1]
  have δ9 : σ9.vec (V.aB + 3) = 0 := by
    rw [e9, e8, e7, e6, e5, e4]; simp only [Env.setSc_vec]
    rw [v3, e2]; funext j; simp
  have l9 : σ9.sc (V.sB + 60) = σ.sc (V.sB + 101) := by
    rw [e9, e8, e7, e6, e5, e4]; simp [s101]
  have o9 : σ9.sc (V.sB + 61) = 1 := by rw [e9, e8, e7, e6, e5, e4]; simp
  have z9 : σ9.sc (V.sB + 63) = 0 := by rw [e9, e8, e7, e6, e5, e4]; simp [z3]
  have c9 : σ9.sc (V.sB + 62) = 16 * (1 / σ.sc V.r) := by
    rw [e9, e8, e7, e6, e5, e4]; simp [Op2.eval, hr60, hr61, hr64, r3]
  obtain ⟨d9, o9', -, -⟩ := gN σ9 g9
  let J : ℕ → Env d → Prop := fun t σ' =>
    SRel V (sepCoords (gev Q V σ) (σ.vec y0) (σ.sc (V.sB + 100)) (σ.sc (V.sB + 101)) (1 / σ.sc V.r) Jc t) σ' ∧
      σ'.sc (V.sB + 63) = 0 ∧ σ'.sc (V.sB + 62) = 16 * (1 / σ.sc V.r) ∧ G σ'
  have h0' : J 0 (σ9.setNat (V.nB + 6) 0) :=
    ⟨SRel.setNat (st := some (σ.vec y0, σ.sc (V.sB + 101), 0)) ⟨o9, y9, l9, δ9⟩ _ _, z9, c9, ownN6 _ _ g9⟩
  refine runs_seq (runs_forN (by lay) (by lay) (by lay) (by lay) (by lay) d (kST d Kq B Jc + 1) J σ9 d9 o9' h0' ?_)
    (fun σ10 h10 => ?_)
  · intro t ht σ' hJ' hit hnt hot
    obtain ⟨hS, z', c', g'⟩ := hJ'
    obtain ⟨d', o', b', j'⟩ := gN σ' g'
    have e' := gE σ' g'
    cases hc : sepCoords (gev Q V σ) (σ.vec y0) (σ.sc (V.sB + 100)) (σ.sc (V.sB + 101)) (1 / σ.sc V.r) Jc t with
    | none =>
      rw [hc] at hS
      refine runs_mono (runs_ifS_f (by lay) (by lay) (by rw [z', hS]; exact lt_irrefl 0) (runs_skip σ'))
        (by unfold kST; omega) (fun σ'' e'' => ?_)
      subst e''
      refine ⟨hit, hnt, hot, ?_, by simpa using z', by simpa using c', ownN6 _ _ g'⟩
      show SRel V _ _
      rw [sepCoords_succ_lt _ _ _ _ _ _ ht, hc]
      exact SRel.setNat (st := none) hS _ _
    | some st =>
      rw [hc] at hS
      refine runs_mono (runs_ifS_t (by lay) (by lay) (by rw [z', hS.1]; exact one_pos)
        (runs_sepCoordTurn hp hmem hIq σ' d' o' g'.1 ⟨t, ht⟩ hit st hS z' c')) (le_of_eq (by rw [b', j']))
        (fun σ'' h'' => ?_)
      obtain ⟨hS'', z'', c'', k''⟩ := h''
      rw [e'.1, e'.2, j'] at hS''
      refine ⟨?_, ?_, ?_, ?_, by simpa using z'', by simpa using c'', ownN6 _ _ (keep_trans g' (keep_mono k''
        (by intro j hj; simp only [List.mem_range'_1] at hj ⊢; omega) (fun _ h => h) (fun _ h => h)))⟩
      · rw [k''.nat (by nmemS) (hp.nN_nQ (by omega) (by omega)), hit]
      · rw [k''.nat (by nmemS) hp.dv_nQ, hnt]
      · rw [k''.nat (by nmemS) hp.one_nQ, hot]
      · show SRel V _ _
        rw [sepCoords_succ_lt _ _ _ _ _ _ ht, hc]
        exact SRel.setNat hS'' _ _
  · obtain ⟨⟨hS, z10, -, g10⟩, -⟩ := h10
    obtain ⟨d10, o10, b10, -⟩ := gN σ10 g10
    have e10 := gE σ10 g10
    rw [sep_eq_bind]
    cases hc : sepCoords (gev Q V σ) (σ.vec y0) (σ.sc (V.sB + 100)) (σ.sc (V.sB + 101)) (1 / σ.sc V.r) Jc d with
    | none =>
      rw [hc] at hS
      refine runs_mono (runs_ifS_f (by lay) (by lay) (by rw [z10, hS]; exact lt_irrefl 0) (runs_skip σ10))
        (by unfold kTail; omega) (fun σ'' e'' => ?_)
      subst e''
      exact ⟨hS, g10⟩
    | some st =>
      rw [hc] at hS
      refine runs_mono (runs_ifS_t (by lay) (by lay) (by rw [z10, hS.1]; exact one_pos)
        (runs_sepTail hp hmem hIq σ10 d10 o10 g10.1 h0 st hS z10)) (le_of_eq (by rw [b10])) (fun σ'' h'' => ?_)
      obtain ⟨hR, k''⟩ := h''
      rw [e10.1, e10.2] at hR
      exact ⟨hR, keep_trans g10 k''⟩

end AdversarialBco.Poly.AP
