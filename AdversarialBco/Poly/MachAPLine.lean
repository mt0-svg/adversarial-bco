/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.MachAPBase

@[expose] public section

/-!
# The subroutine AP in VL: Procedure LINE

LINE asks the values `lev Q V σ i s η`, the gauge value at `y + s e_i` (`y` the array `aB + 2`, `i` the natural
variable `nB + 6`) with error `η`. Its state is `LRel`: the flags `sB + 28` (`0` after a failure) and `sB + 29` (`1`
while running), the window in `sB + 21 .. 27` (`WinAt`) and the result in `sB + 30, 31`; `LRes` is the result
alone. The rules: `runs_lineEv` (one value, then the rest of the code or the failure), `runs_lineFirstCode`,
`runs_lineHalveCode`, `runs_lineCheck`, and `runs_lineCode`, which computes `line` through `line_eq_lineEnd`.
-/

namespace AdversarialBco.Poly.AP

open AdversarialBco AdversarialBco.RealRAM AdversarialBco.Poly.Mach AdversarialBco.Poly.Mach.VL Matrix

variable {d : ℕ} {L : Layout} {w : World d} {memQ : Cmd} {V : APVars}

/-- The values that LINE asks: the gauge value at `y + s e_i`, `y` the array `aB + 2`. -/
noncomputable def lev (Q : Set (Fin d → ℝ)) (V : APVars) (σ : Env d) (i : Fin d) : ℝ → ℝ → Option ℝ :=
  fun s η => oGaugeValCap Q (σ.vec V.a0) (σ.sc V.r) (σ.sc V.R) (σ.nat (V.nB + 11)) (σ.vec (V.aB + 2) + s • oUnit i) η

/-- The window `W` in the scalars `sB + 21 .. 27`. -/
def WinAt (V : APVars) (σ : Env d) (W : LineWin) : Prop :=
  σ.sc (V.sB + 21) = W.p0 ∧ σ.sc (V.sB + 22) = W.lam ∧ σ.sc (V.sB + 23) = W.v0 ∧ σ.sc (V.sB + 24) = W.v1 ∧
    σ.sc (V.sB + 25) = W.v2 ∧ σ.sc (V.sB + 26) = W.v3 ∧ σ.sc (V.sB + 27) = W.v4

/-- The state of LINE: the flags `sB + 28, 29`, the window, the result `sB + 30, 31`. -/
def LRel (V : APVars) : Option (LineWin ⊕ (ℝ × ℝ)) → Env d → Prop
  | none, σ => σ.sc (V.sB + 28) = 0 ∧ σ.sc (V.sB + 29) = 0
  | some (.inl W), σ => σ.sc (V.sB + 28) = 1 ∧ σ.sc (V.sB + 29) = 1 ∧ WinAt V σ W
  | some (.inr p), σ => σ.sc (V.sB + 28) = 1 ∧ σ.sc (V.sB + 29) = 0 ∧ σ.sc (V.sB + 30) = p.1 ∧ σ.sc (V.sB + 31) = p.2

/-- The result of LINE. -/
def LRes (V : APVars) : Option (ℝ × ℝ) → Env d → Prop
  | none, σ => σ.sc (V.sB + 28) = 0
  | some p, σ => σ.sc (V.sB + 28) = 1 ∧ σ.sc (V.sB + 30) = p.1 ∧ σ.sc (V.sB + 31) = p.2

/-- Membership of offsets in the lists of a piece, keeping the hypotheses on the offsets. -/
macro "mem_tac'" : tactic =>
  `(tactic| (intro i hi; simp only [apN, apS, apA, List.mem_cons, List.mem_append, List.mem_range'_1,
    List.not_mem_nil, or_false] at hi ⊢; all_goals omega))

theorem lev_congr {Q : Set (Fin d → ℝ)} {Iq : Env d → Prop} {nsQ ssQ asQ ON OS OA : List ℕ}
    (hp : V.Ok L nsQ ssQ asQ) {σ σ' : Env d} (h : KP Iq nsQ ssQ asQ ON OS OA σ σ') (i : Fin d)
    (hN : V.nB + 11 ∉ ON) (hr : V.r ∉ OS) (hR : V.R ∉ OS) (ha : V.a0 ∉ OA) (hy : V.aB + 2 ∉ OA) :
    lev Q V σ' i = lev Q V σ i := by
  unfold lev
  rw [h.vec ha hp.a0_aQ, h.sc hr hp.r_sQ, h.sc hR hp.R_sQ, h.nat hN (hp.nN_nQ (by omega) (by omega)),
    h.vec hy (hp.aB_aQ (by omega) (by omega))]

set_option maxHeartbeats 1000000 in
open Classical in
/-- One value of LINE into `dst`, then `rest`; on a failed value, the failure of LINE. -/
theorem runs_lineEv {Q : Set (Fin d → ℝ)} {Iq : Env d → Prop} {Kq : ℕ} {nsQ ssQ asQ : List ℕ}
    (hp : V.Ok L nsQ ssQ asQ) (hmem : MemRule L w memQ V Q Iq Kq nsQ ssQ asQ) (hIq : IqRule V Iq)
    {dst : ℕ} (hdst : V.sB + 21 ≤ dst ∧ dst < V.sB + 50) {rest : Cmd} {Krest : ℕ} {Post : Env d → Prop}
    (σ : Env d) (hd : σ.nat V.dv = d) (h1 : σ.nat V.one = 1) (hI : Iq σ) (i : Fin d)
    (hi : σ.nat (V.nB + 6) = i) (hz : σ.sc (V.sB + 32) = 0) {B : ℕ} (hB : σ.nat (V.nB + 11) = B)
    (hrest : ∀ v σ', lev Q V σ i (σ.sc (V.sB + 39)) (σ.sc (V.sB + 38)) = some v → σ'.sc dst = v →
      KP Iq nsQ ssQ asQ (List.range' V.nB 5) (dst :: List.range' V.sB 21) [V.aB, V.aB + 1, V.qv] σ σ' →
      Runs L w rest σ' Krest Post)
    (hfail : ∀ σ', lev Q V σ i (σ.sc (V.sB + 39)) (σ.sc (V.sB + 38)) = none → σ'.sc (V.sB + 28) = 0 →
      σ'.sc (V.sB + 29) = 0 →
      KP Iq nsQ ssQ asQ (List.range' V.nB 5) ((V.sB + 28) :: (V.sB + 29) :: List.range' V.sB 21)
        [V.aB, V.aB + 1, V.qv] σ σ' → Post σ') :
    Runs L w (lineEv L memQ V dst rest) σ (kEV d Kq B + (Krest + 4)) Post := by
  subst hB
  layout_facts
  unfold lineEv
  refine runs_seq (runs_ev1Code hp hmem hIq (idx := V.nB + 6) (s := V.sB + 39) (η := V.sB + 38)
    ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ σ hd h1 hI i hi) (fun σ1 h => ?_)
  obtain ⟨hrel, k1⟩ := h
  have hrel' : OptRel (lev Q V σ i (σ.sc (V.sB + 39)) (σ.sc (V.sB + 38))) (σ1.sc (V.sB + 17))
      (σ1.sc (V.sB + 18)) := hrel
  have z1 : σ1.sc (V.sB + 32) = 0 := by rw [k1.sc (by nmem_tac) (hp.sB_sQ (by lay) (by lay))]; exact hz
  have hON : ∀ j ∈ List.range' V.nB 5, j ∈ apN V := by mem_tac
  have hOA : ∀ j ∈ [V.aB, V.aB + 1, V.qv], j ∈ apA V := by mem_tac
  cases hv : lev Q V σ i (σ.sc (V.sB + 39)) (σ.sc (V.sB + 38)) with
  | none =>
    rw [hv] at hrel'
    simp only [OptRel] at hrel'
    refine runs_mono (K := 2 + 2) (runs_ifS_f (by lay) (by lay) (by rw [z1, hrel']; exact lt_irrefl 0) ?_)
      (by omega) (fun _ h => h)
    unfold lineFail
    refine runs_seq (runs_sconst (by lay) 0) (fun σ2 e2 => runs_mono (runs_sconst (by lay) 0) le_rfl
      (fun σ3 e3 => ?_))
    have hOS : ∀ j ∈ (V.sB + 28) :: (V.sB + 29) :: List.range' V.sB 21, j ∈ apS V := by mem_tac
    have k1' := keep_mono (ON' := List.range' V.nB 5) (OS' := (V.sB + 28) :: (V.sB + 29) :: List.range' V.sB 21)
      (OA' := [V.aB, V.aB + 1, V.qv]) k1 (by mem_tac) (by mem_tac) (by mem_tac)
    subst e2 e3
    have k3 := keep_own hIq hON hOS hOA (keep_own hIq hON hOS hOA k1' (frame_setSc σ1 (V.sB + 28) ((0 : ℚ) : ℝ)) (by simp)
      (by mem_tac) (by simp)) (frame_setSc _ (V.sB + 29) ((0 : ℚ) : ℝ)) (by simp) (by mem_tac) (by simp)
    exact hfail _ hv (by simp) (by simp) k3
  | some v =>
    rw [hv] at hrel'
    simp only [OptRel] at hrel'
    refine runs_mono (K := (1 + Krest) + 1)
      (runs_ifS_t (by lay) (by lay) (by rw [z1, hrel'.1]; exact one_pos) ?_) (by omega) (fun _ h => h)
    refine runs_seq (runs_smov (by lay) (by lay)) (fun σ2 e2 => ?_)
    have hOS : ∀ j ∈ dst :: List.range' V.sB 21, j ∈ apS V := by mem_tac'
    have k1' := keep_mono (ON' := List.range' V.nB 5) (OS' := dst :: List.range' V.sB 21)
      (OA' := [V.aB, V.aB + 1, V.qv]) k1 (by mem_tac) (by mem_tac) (by mem_tac)
    have k2 := keep_own hIq hON hOS hOA k1' (frame_setSc σ1 dst (σ1.sc (V.sB + 18))) (by simp) (by simp) (by simp)
    rw [← e2] at k2
    exact hrest v σ2 hv (by rw [e2]; simp [hrel'.2]) k2

/-- The lists of LINE. -/
abbrev lineN (V : APVars) : List ℕ := List.range' V.nB 5
/-- The scalars of LINE. -/
abbrev lineS (V : APVars) : List ℕ := List.range' V.sB 50
/-- The arrays of LINE. -/
abbrev lineA (V : APVars) : List ℕ := [V.aB, V.aB + 1, V.qv]

/-- The step bound of the first window. -/
def kLF (d Kq B : ℕ) : ℕ := 5 * kEV d Kq B + 37

set_option maxHeartbeats 4000000 in
open Classical in
/-- The rule of the first window of LINE. -/
theorem runs_lineFirstCode {Q : Set (Fin d → ℝ)} {Iq : Env d → Prop} {Kq : ℕ} {nsQ ssQ asQ : List ℕ}
    (hp : V.Ok L nsQ ssQ asQ) (hmem : MemRule L w memQ V Q Iq Kq nsQ ssQ asQ) (hIq : IqRule V Iq)
    (σ : Env d) (hd : σ.nat V.dv = d) (h1 : σ.nat V.one = 1) (hI : Iq σ) (i : Fin d)
    (hi : σ.nat (V.nB + 6) = i) :
    Runs L w (lineFirstCode L memQ V) σ (kLF d Kq (σ.nat (V.nB + 11)))
      (fun σ' => LRel V ((lineFirst (lev Q V σ i) (σ.sc (V.sB + 60)) (σ.sc (V.sB + 100))).map .inl) σ' ∧
        σ'.sc (V.sB + 32) = 0 ∧ KP Iq nsQ ssQ asQ (lineN V) (lineS V) (lineA V) σ σ') := by
  layout_facts
  have hON : ∀ j ∈ lineN V, j ∈ apN V := by mem_tac
  have hOS : ∀ j ∈ lineS V, j ∈ apS V := by mem_tac
  have hOA : ∀ j ∈ lineA V, j ∈ apA V := by mem_tac
  let G : Env d → Prop := KP Iq nsQ ssQ asQ (lineN V) (lineS V) (lineA V) σ
  have own : ∀ σa (q : ℕ) (v : ℝ), V.sB ≤ q → q < V.sB + 50 → G σa → G (σa.setSc q v) :=
    fun σa q v h1 h2 g => keep_own hIq hON hOS hOA g (frame_setSc _ _ _) (by simp)
      (by intro j hj; simp only [List.mem_singleton] at hj; subst hj; simp only [List.mem_range'_1]; omega) (by simp)
  have lift : ∀ σa σb (dst : ℕ), V.sB ≤ dst → dst < V.sB + 50 → G σa →
      KP Iq nsQ ssQ asQ (List.range' V.nB 5) (dst :: List.range' V.sB 21) (lineA V) σa σb → G σb :=
    fun σa σb dst h1 h2 g k => keep_trans g (keep_mono k (by mem_tac) (by mem_tac') (by mem_tac))
  have liftF : ∀ σa σb, G σa →
      KP Iq nsQ ssQ asQ (List.range' V.nB 5) ((V.sB + 28) :: (V.sB + 29) :: List.range' V.sB 21) (lineA V) σa σb →
      G σb :=
    fun σa σb g k => keep_trans g (keep_mono k (by mem_tac) (by mem_tac) (by mem_tac))
  have Gdv : ∀ σa, G σa → σa.nat V.dv = d := fun σa g => by rw [g.nat (by nmem_tac) hp.dv_nQ]; exact hd
  have Gone : ∀ σa, G σa → σa.nat V.one = 1 := fun σa g => by rw [g.nat (by nmem_tac) hp.one_nQ]; exact h1
  have Gi : ∀ σa, G σa → σa.nat (V.nB + 6) = i := fun σa g => by
    rw [g.nat (by nmem_tac) (hp.nN_nQ (by lay) (by lay))]; exact hi
  have GB : ∀ σa, G σa → σa.nat (V.nB + 11) = σ.nat (V.nB + 11) := fun σa g =>
    g.nat (by nmem_tac) (hp.nN_nQ (by lay) (by lay))
  have Glev : ∀ σa, G σa → lev Q V σa i = lev Q V σ i := fun σa g =>
    lev_congr hp g i (by nmem_tac) (by nmem_tac) (by nmem_tac) (by nmem_tac) (by nmem_tac)
  obtain ⟨B, hB⟩ : ∃ B, σ.nat (V.nB + 11) = B := ⟨_, rfl⟩
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ, σ.sc (V.sB + 60) = ℓ := ⟨_, rfl⟩
  obtain ⟨τ, hτ⟩ : ∃ τ, σ.sc (V.sB + 100) = τ := ⟨_, rfl⟩
  rw [hB, hℓ, hτ]
  rw [hB] at GB
  set ev := lev Q V σ i with hev
  unfold lineFirstCode
  refine runs_mono (K := 1 + (1 + (1 + (1 + (1 + (1 + (1 +
    (kEV d Kq B + ((1 + (kEV d Kq B + ((1 + (1 + (kEV d Kq B + ((1 + (1 + (kEV d Kq B + ((1 + (1 +
      (kEV d Kq B + ((1 + (1 + 1)) + 4)))) + 4)))) + 4)))) + 4))) + 4)))))))))
    ?_ (le_of_eq (by unfold kLF; ring)) (fun _ h => h)
  refine runs_seq (runs_sconst (by lay) 0) (fun σ1 e1 => ?_)
  refine runs_seq (runs_sconst (by lay) 4) (fun σ2 e2 => ?_)
  refine runs_seq (runs_sop2 (by lay) (by lay) (by lay) .div) (fun σ3 e3 => ?_)
  refine runs_seq (runs_sop2 (by lay) (by lay) (by lay) .mul) (fun σ4 e4 => ?_)
  refine runs_seq (runs_sconst (by lay) 400) (fun σ5 e5 => ?_)
  refine runs_seq (runs_sop2 (by lay) (by lay) (by lay) .div) (fun σ6 e6 => ?_)
  refine runs_seq (runs_sconst (by lay) 0) (fun σ7 e7 => ?_)
  have g7 : G σ7 := by
    rw [e7, e6, e5, e4, e3, e2, e1]
    exact own _ _ _ (by lay) (by lay) (own _ _ _ (by lay) (by lay) (own _ _ _ (by lay) (by lay)
      (own _ _ _ (by lay) (by lay) (own _ _ _ (by lay) (by lay) (own _ _ _ (by lay) (by lay)
      (own _ _ _ (by lay) (by lay) (keep_refl hI)))))))
  have ℓ0 : σ.sc (V.sB + 60) = ℓ := hℓ
  have τ0 : σ.sc (V.sB + 100) = τ := hτ
  have l7 : σ7.sc (V.sB + 22) = ℓ / 4 := by
    rw [e7, e6, e5, e4, e3, e2, e1]; simp [Op2.eval, ℓ0]
  have η7 : σ7.sc (V.sB + 38) = τ * (ℓ / 4) / 400 := by
    rw [e7, e6, e5, e4, e3, e2, e1]; simp [Op2.eval, ℓ0, τ0]
  have s7 : σ7.sc (V.sB + 39) = 0 := by rw [e7]; simp
  have z7 : σ7.sc (V.sB + 32) = 0 := by rw [e7, e6, e5, e4, e3, e2, e1]; simp
  -- the value at 0
  refine runs_lineEv hp hmem hIq (dst := V.sB + 23) ⟨by omega, by omega⟩ σ7 (Gdv _ g7) (Gone _ g7) g7.1 i
    (Gi _ g7) z7 (GB _ g7) (fun v0 σ8 hv0 e8 k8 => ?_) (fun σ' hv0 f1 f2 k' => ?_)
  rotate_left
  · rw [Glev _ g7, s7, η7] at hv0
    refine ⟨?_, by rw [k'.sc (by nmem_tac) (hp.sB_sQ (by lay) (by lay))]; exact z7, liftF _ _ g7 k'⟩
    have : lineFirst ev ℓ τ = none := by simp [lineFirst, hv0]
    rw [this]; exact ⟨f1, f2⟩
  rw [Glev _ g7, s7, η7] at hv0
  have g8 := lift _ _ _ (by omega) (by omega) g7 k8
  have l8 : σ8.sc (V.sB + 22) = ℓ / 4 := by rw [k8.sc (by nmem_tac) (hp.sB_sQ (by lay) (by lay))]; exact l7
  have η8 : σ8.sc (V.sB + 38) = τ * (ℓ / 4) / 400 := by
    rw [k8.sc (by nmem_tac) (hp.sB_sQ (by lay) (by lay))]; exact η7
  have z8 : σ8.sc (V.sB + 32) = 0 := by rw [k8.sc (by nmem_tac) (hp.sB_sQ (by lay) (by lay))]; exact z7
  refine runs_seq (runs_smov (by lay) (by lay)) (fun σ9 e9 => ?_)
  have g9 : G σ9 := by rw [e9]; exact own _ _ _ (by lay) (by lay) g8
  have l9 : σ9.sc (V.sB + 22) = ℓ / 4 := by rw [e9]; simp [l8]
  have η9 : σ9.sc (V.sB + 38) = τ * (ℓ / 4) / 400 := by rw [e9]; simp [η8]
  have z9 : σ9.sc (V.sB + 32) = 0 := by rw [e9]; simp [z8]
  have a9 : σ9.sc (V.sB + 23) = v0 := by rw [e9]; simp [e8]
  have s9 : σ9.sc (V.sB + 39) = ℓ / 4 := by rw [e9]; simp [l8]
  -- the value at λ
  refine runs_lineEv hp hmem hIq (dst := V.sB + 24) ⟨by omega, by omega⟩ σ9 (Gdv _ g9) (Gone _ g9) g9.1 i
    (Gi _ g9) z9 (GB _ g9) (fun v1 σ10 hv1 e10 k10 => ?_) (fun σ' hv1 f1 f2 k' => ?_)
  rotate_left
  · rw [Glev _ g9, s9, η9] at hv1
    refine ⟨?_, by rw [k'.sc (by nmem_tac) (hp.sB_sQ (by lay) (by lay))]; exact z9, liftF _ _ g9 k'⟩
    have : lineFirst ev ℓ τ = none := by simp [lineFirst, hv0, hv1]
    rw [this]; exact ⟨f1, f2⟩
  rw [Glev _ g9, s9, η9] at hv1
  have g10 := lift _ _ _ (by omega) (by omega) g9 k10
  have l10 : σ10.sc (V.sB + 22) = ℓ / 4 := by rw [k10.sc (by nmem_tac) (hp.sB_sQ (by lay) (by lay))]; exact l9
  have η10 : σ10.sc (V.sB + 38) = τ * (ℓ / 4) / 400 := by
    rw [k10.sc (by nmem_tac) (hp.sB_sQ (by lay) (by lay))]; exact η9
  have z10 : σ10.sc (V.sB + 32) = 0 := by rw [k10.sc (by nmem_tac) (hp.sB_sQ (by lay) (by lay))]; exact z9
  have a10 : σ10.sc (V.sB + 23) = v0 := by rw [k10.sc (by nmem_tac) (hp.sB_sQ (by lay) (by lay))]; exact a9
  refine runs_seq (runs_sconst (by lay) 2) (fun σ11 e11 => ?_)
  refine runs_seq (runs_sop2 (by lay) (by lay) (by lay) .mul) (fun σ12 e12 => ?_)
  have g12 : G σ12 := by rw [e12, e11]; exact own _ _ _ (by lay) (by lay) (own _ _ _ (by lay) (by lay) g10)
  have l12 : σ12.sc (V.sB + 22) = ℓ / 4 := by rw [e12, e11]; simp [l10]
  have η12 : σ12.sc (V.sB + 38) = τ * (ℓ / 4) / 400 := by rw [e12, e11]; simp [η10]
  have z12 : σ12.sc (V.sB + 32) = 0 := by rw [e12, e11]; simp [z10]
  have a12 : σ12.sc (V.sB + 23) = v0 := by rw [e12, e11]; simp [a10]
  have b12 : σ12.sc (V.sB + 24) = v1 := by rw [e12, e11]; simp [e10]
  have s12 : σ12.sc (V.sB + 39) = 2 * (ℓ / 4) := by rw [e12, e11]; simp [Op2.eval, l10]
  -- the value at 2λ
  refine runs_lineEv hp hmem hIq (dst := V.sB + 25) ⟨by omega, by omega⟩ σ12 (Gdv _ g12) (Gone _ g12) g12.1 i
    (Gi _ g12) z12 (GB _ g12) (fun v2 σ13 hv2 e13 k13 => ?_) (fun σ' hv2 f1 f2 k' => ?_)
  rotate_left
  · rw [Glev _ g12, s12, η12] at hv2
    refine ⟨?_, by rw [k'.sc (by nmem_tac) (hp.sB_sQ (by lay) (by lay))]; exact z12, liftF _ _ g12 k'⟩
    have : lineFirst ev ℓ τ = none := by simp [lineFirst, hv0, hv1, hv2]
    rw [this]; exact ⟨f1, f2⟩
  rw [Glev _ g12, s12, η12] at hv2
  have g13 := lift _ _ _ (by omega) (by omega) g12 k13
  have l13 : σ13.sc (V.sB + 22) = ℓ / 4 := by rw [k13.sc (by nmem_tac) (hp.sB_sQ (by lay) (by lay))]; exact l12
  have η13 : σ13.sc (V.sB + 38) = τ * (ℓ / 4) / 400 := by
    rw [k13.sc (by nmem_tac) (hp.sB_sQ (by lay) (by lay))]; exact η12
  have z13 : σ13.sc (V.sB + 32) = 0 := by rw [k13.sc (by nmem_tac) (hp.sB_sQ (by lay) (by lay))]; exact z12
  have a13 : σ13.sc (V.sB + 23) = v0 := by rw [k13.sc (by nmem_tac) (hp.sB_sQ (by lay) (by lay))]; exact a12
  have b13 : σ13.sc (V.sB + 24) = v1 := by rw [k13.sc (by nmem_tac) (hp.sB_sQ (by lay) (by lay))]; exact b12
  refine runs_seq (runs_sconst (by lay) 3) (fun σ14 e14 => ?_)
  refine runs_seq (runs_sop2 (by lay) (by lay) (by lay) .mul) (fun σ15 e15 => ?_)
  have g15 : G σ15 := by rw [e15, e14]; exact own _ _ _ (by lay) (by lay) (own _ _ _ (by lay) (by lay) g13)
  have l15 : σ15.sc (V.sB + 22) = ℓ / 4 := by rw [e15, e14]; simp [l13]
  have η15 : σ15.sc (V.sB + 38) = τ * (ℓ / 4) / 400 := by rw [e15, e14]; simp [η13]
  have z15 : σ15.sc (V.sB + 32) = 0 := by rw [e15, e14]; simp [z13]
  have a15 : σ15.sc (V.sB + 23) = v0 := by rw [e15, e14]; simp [a13]
  have b15 : σ15.sc (V.sB + 24) = v1 := by rw [e15, e14]; simp [b13]
  have c15 : σ15.sc (V.sB + 25) = v2 := by rw [e15, e14]; simp [e13]
  have s15 : σ15.sc (V.sB + 39) = 3 * (ℓ / 4) := by rw [e15, e14]; simp [Op2.eval, l13]
  -- the value at 3λ
  refine runs_lineEv hp hmem hIq (dst := V.sB + 26) ⟨by omega, by omega⟩ σ15 (Gdv _ g15) (Gone _ g15) g15.1 i
    (Gi _ g15) z15 (GB _ g15) (fun v3 σ16 hv3 e16 k16 => ?_) (fun σ' hv3 f1 f2 k' => ?_)
  rotate_left
  · rw [Glev _ g15, s15, η15] at hv3
    refine ⟨?_, by rw [k'.sc (by nmem_tac) (hp.sB_sQ (by lay) (by lay))]; exact z15, liftF _ _ g15 k'⟩
    have : lineFirst ev ℓ τ = none := by simp [lineFirst, hv0, hv1, hv2, hv3]
    rw [this]; exact ⟨f1, f2⟩
  rw [Glev _ g15, s15, η15] at hv3
  have g16 := lift _ _ _ (by omega) (by omega) g15 k16
  have l16 : σ16.sc (V.sB + 22) = ℓ / 4 := by rw [k16.sc (by nmem_tac) (hp.sB_sQ (by lay) (by lay))]; exact l15
  have η16 : σ16.sc (V.sB + 38) = τ * (ℓ / 4) / 400 := by
    rw [k16.sc (by nmem_tac) (hp.sB_sQ (by lay) (by lay))]; exact η15
  have z16 : σ16.sc (V.sB + 32) = 0 := by rw [k16.sc (by nmem_tac) (hp.sB_sQ (by lay) (by lay))]; exact z15
  have a16 : σ16.sc (V.sB + 23) = v0 := by rw [k16.sc (by nmem_tac) (hp.sB_sQ (by lay) (by lay))]; exact a15
  have b16 : σ16.sc (V.sB + 24) = v1 := by rw [k16.sc (by nmem_tac) (hp.sB_sQ (by lay) (by lay))]; exact b15
  have c16 : σ16.sc (V.sB + 25) = v2 := by rw [k16.sc (by nmem_tac) (hp.sB_sQ (by lay) (by lay))]; exact c15
  refine runs_seq (runs_sconst (by lay) 4) (fun σ17 e17 => ?_)
  refine runs_seq (runs_sop2 (by lay) (by lay) (by lay) .mul) (fun σ18 e18 => ?_)
  have g18 : G σ18 := by rw [e18, e17]; exact own _ _ _ (by lay) (by lay) (own _ _ _ (by lay) (by lay) g16)
  have η18 : σ18.sc (V.sB + 38) = τ * (ℓ / 4) / 400 := by rw [e18, e17]; simp [η16]
  have z18 : σ18.sc (V.sB + 32) = 0 := by rw [e18, e17]; simp [z16]
  have a18 : σ18.sc (V.sB + 23) = v0 := by rw [e18, e17]; simp [a16]
  have b18 : σ18.sc (V.sB + 24) = v1 := by rw [e18, e17]; simp [b16]
  have c18 : σ18.sc (V.sB + 25) = v2 := by rw [e18, e17]; simp [c16]
  have d18 : σ18.sc (V.sB + 26) = v3 := by rw [e18, e17]; simp [e16]
  have l18 : σ18.sc (V.sB + 22) = ℓ / 4 := by rw [e18, e17]; simp [l16]
  have s18 : σ18.sc (V.sB + 39) = 4 * (ℓ / 4) := by rw [e18, e17]; simp [Op2.eval, l16]
  -- the value at 4λ
  refine runs_lineEv hp hmem hIq (dst := V.sB + 27) ⟨by omega, by omega⟩ σ18 (Gdv _ g18) (Gone _ g18) g18.1 i
    (Gi _ g18) z18 (GB _ g18) (fun v4 σ19 hv4 e19 k19 => ?_) (fun σ' hv4 f1 f2 k' => ?_)
  rotate_left
  · rw [Glev _ g18, s18, η18] at hv4
    refine ⟨?_, by rw [k'.sc (by nmem_tac) (hp.sB_sQ (by lay) (by lay))]; exact z18, liftF _ _ g18 k'⟩
    have : lineFirst ev ℓ τ = none := by simp [lineFirst, hv0, hv1, hv2, hv3, hv4]
    rw [this]; exact ⟨f1, f2⟩
  rw [Glev _ g18, s18, η18] at hv4
  have g19 := lift _ _ _ (by omega) (by omega) g18 k19
  have kk : ∀ x, V.sB + 21 ≤ x → x < V.sB + 50 → x ≠ V.sB + 27 → σ19.sc x = σ18.sc x := fun x h1 h2 h3 =>
    k19.sc (by nmem_tac) (hp.sB_sQ (by lay) (by lay))
  have hW : lineFirst ev ℓ τ = some ⟨0, ℓ / 4, v0, v1, v2, v3, v4⟩ := by
    simp [lineFirst, hv0, hv1, hv2, hv3, hv4]
  refine runs_seq (runs_sconst (by lay) 0) (fun σ20 e20 => ?_)
  refine runs_seq (runs_sconst (by lay) 1) (fun σ21 e21 => runs_mono (runs_sconst (by lay) 1) le_rfl
    (fun σ22 e22 => ?_))
  have l19 := kk (V.sB + 22) (by omega) (by omega) (by omega)
  have a19 := kk (V.sB + 23) (by omega) (by omega) (by omega)
  have b19 := kk (V.sB + 24) (by omega) (by omega) (by omega)
  have c19 := kk (V.sB + 25) (by omega) (by omega) (by omega)
  have d19 := kk (V.sB + 26) (by omega) (by omega) (by omega)
  have z19 := kk (V.sB + 32) (by omega) (by omega) (by omega)
  rw [hW]
  refine ⟨?_, ?_, ?_⟩
  · rw [e22, e21, e20]
    simp only [Option.map_some, LRel, WinAt]
    simp [l19, a19, b19, c19, d19, l18, a18, b18, c18, d18, e19]
  · rw [e22, e21, e20]; simp [z19, z18]
  · rw [e22, e21, e20]
    exact own _ _ _ (by lay) (by lay) (own _ _ _ (by lay) (by lay) (own _ _ _ (by lay) (by lay) g19))

/-! ## Known values of scalars -/

/-- The scalars `p.1` hold the values `p.2`, for `p ∈ fs`. -/
def Kn (σ : Env d) (fs : List (ℕ × ℝ)) : Prop := ∀ p ∈ fs, σ.sc p.1 = p.2

theorem Kn.get {σ : Env d} {fs : List (ℕ × ℝ)} (h : Kn σ fs) {x : ℕ} {v : ℝ} (hx : (x, v) ∈ fs) : σ.sc x = v :=
  h _ hx

theorem Kn.add {σ : Env d} {fs : List (ℕ × ℝ)} (h : Kn σ fs) {x : ℕ} {v : ℝ} (hx : σ.sc x = v) :
    Kn σ ((x, v) :: fs) := by
  intro p hp
  rcases List.mem_cons.1 hp with rfl | hp
  · exact hx
  · exact h p hp

theorem Kn.set {σ : Env d} {fs : List (ℕ × ℝ)} (h : Kn σ fs) {y : ℕ} (hy : ∀ p ∈ fs, p.1 ≠ y) (v : ℝ) :
    Kn (σ.setSc y v) fs := by
  intro p hp; rw [Env.setSc_sc, ite_eq_right (hy p hp)]; exact h p hp

theorem Kn.setEq {σ σ' : Env d} {fs : List (ℕ × ℝ)} (h : Kn σ fs) {y : ℕ} (hy : ∀ p ∈ fs, p.1 ≠ y) {v : ℝ}
    (e : σ' = σ.setSc y v) : Kn σ' fs := by
  rw [e]; exact h.set hy v

theorem Kn.ofKP {Iq : Env d → Prop} {nsQ ssQ asQ ON OS OA : List ℕ} {σ σ' : Env d} {fs : List (ℕ × ℝ)}
    (h : Kn σ fs) (k : KP Iq nsQ ssQ asQ ON OS OA σ σ') (h1 : ∀ p ∈ fs, p.1 ∉ OS) (h2 : ∀ p ∈ fs, p.1 ∉ ssQ) :
    Kn σ' fs := by
  intro p hp; rw [k.sc (h1 p hp) (h2 p hp)]; exact h p hp

set_option hygiene false in
/-- One side condition on a known value. -/
macro "kn_one" : tactic => `(tactic| first
  | exact hp.sB_sQ (by lay) (by lay)
  | nmem_tac
  | simp)

/-- The side conditions on a list of known values. -/
macro "kn_tac" : tactic =>
  `(tactic| (simp only [List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq]; (repeat' apply And.intro); all_goals (try dsimp only); all_goals kn_one))

/-- The step bound of one halving. -/
def kLH (d Kq B : ℕ) : ℕ := 6 * kEV d Kq B + 64

set_option maxHeartbeats 8000000 in
open Classical in
/-- The rule of one halving of LINE. -/
theorem runs_lineHalveCode {Q : Set (Fin d → ℝ)} {Iq : Env d → Prop} {Kq : ℕ} {nsQ ssQ asQ : List ℕ}
    (hp : V.Ok L nsQ ssQ asQ) (hmem : MemRule L w memQ V Q Iq Kq nsQ ssQ asQ) (hIq : IqRule V Iq)
    (σ : Env d) (hd : σ.nat V.dv = d) (h1 : σ.nat V.one = 1) (hI : Iq σ) (i : Fin d)
    (hi : σ.nat (V.nB + 6) = i) (W : LineWin) (hW : LRel V (some (.inl W)) σ) (hz : σ.sc (V.sB + 32) = 0) :
    Runs L w (lineHalveCode L memQ V) σ (kLH d Kq (σ.nat (V.nB + 11)))
      (fun σ' => LRel V ((lineHalve (lev Q V σ i) (σ.sc (V.sB + 100)) W).map .inl) σ' ∧
        σ'.sc (V.sB + 32) = 0 ∧ KP Iq nsQ ssQ asQ (lineN V) (lineS V) (lineA V) σ σ') := by
  layout_facts
  have hON : ∀ j ∈ lineN V, j ∈ apN V := by mem_tac
  have hOS : ∀ j ∈ lineS V, j ∈ apS V := by mem_tac
  have hOA : ∀ j ∈ lineA V, j ∈ apA V := by mem_tac
  let G : Env d → Prop := KP Iq nsQ ssQ asQ (lineN V) (lineS V) (lineA V) σ
  have own : ∀ σa (q : ℕ) (v : ℝ), V.sB ≤ q → q < V.sB + 50 → G σa → G (σa.setSc q v) :=
    fun σa q v h1 h2 g => keep_own hIq hON hOS hOA g (frame_setSc _ _ _) (by simp)
      (by intro j hj; simp only [List.mem_singleton] at hj; subst hj; simp only [List.mem_range'_1]; omega) (by simp)
  have lift : ∀ σa σb (dst : ℕ), V.sB ≤ dst → dst < V.sB + 50 → G σa →
      KP Iq nsQ ssQ asQ (List.range' V.nB 5) (dst :: List.range' V.sB 21) (lineA V) σa σb → G σb :=
    fun σa σb dst h1 h2 g k => keep_trans g (keep_mono k (by mem_tac) (by mem_tac') (by mem_tac))
  have liftF : ∀ σa σb, G σa →
      KP Iq nsQ ssQ asQ (List.range' V.nB 5) ((V.sB + 28) :: (V.sB + 29) :: List.range' V.sB 21) (lineA V) σa σb →
      G σb :=
    fun σa σb g k => keep_trans g (keep_mono k (by mem_tac) (by mem_tac) (by mem_tac))
  have Gdv : ∀ σa, G σa → σa.nat V.dv = d := fun σa g => by rw [g.nat (by nmem_tac) hp.dv_nQ]; exact hd
  have Gone : ∀ σa, G σa → σa.nat V.one = 1 := fun σa g => by rw [g.nat (by nmem_tac) hp.one_nQ]; exact h1
  have Gi : ∀ σa, G σa → σa.nat (V.nB + 6) = i := fun σa g => by
    rw [g.nat (by nmem_tac) (hp.nN_nQ (by lay) (by lay))]; exact hi
  have GB : ∀ σa, G σa → σa.nat (V.nB + 11) = σ.nat (V.nB + 11) := fun σa g =>
    g.nat (by nmem_tac) (hp.nN_nQ (by lay) (by lay))
  have Glev : ∀ σa, G σa → lev Q V σa i = lev Q V σ i := fun σa g =>
    lev_congr hp g i (by nmem_tac) (by nmem_tac) (by nmem_tac) (by nmem_tac) (by nmem_tac)
  obtain ⟨B, hB⟩ : ∃ B, σ.nat (V.nB + 11) = B := ⟨_, rfl⟩
  obtain ⟨τ, hτ⟩ : ∃ τ, σ.sc (V.sB + 100) = τ := ⟨_, rfl⟩
  rw [hB, hτ]
  rw [hB] at GB
  set ev := lev Q V σ i with hev
  obtain ⟨f28, f29, w21, w22, w23, w24, w25, w26, w27⟩ := hW
  have kn0 : Kn σ [(V.sB + 32, 0), (V.sB + 28, 1), (V.sB + 29, 1), (V.sB + 24, W.v1), (V.sB + 25, W.v2),
      (V.sB + 26, W.v3)] := by
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
  unfold lineHalveCode
  refine runs_mono (K := 1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 +
    (kEV d Kq B + ((1 + (1 + (1 + (kEV d Kq B + ((1 + (1 + (1 + (kEV d Kq B + ((1 +
      (kEV d Kq B + ((1 + (1 + (1 + (kEV d Kq B + ((1 + (1 + (1 + (kEV d Kq B +
        ((1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + 9)))))))) + 4))))) + 4))))) + 4))) + 4))))) + 4))))) + 4))))))))))))
    ?_ (le_of_eq (by unfold kLH; ring)) (fun _ h => h)
  refine runs_seq (runs_sconst (by lay) 4) (fun σ1 e1 => ?_)
  refine runs_seq (runs_sop2 (by lay) (by lay) (by lay) .div) (fun σ2 e2 => ?_)
  refine runs_seq (runs_sop2 (by lay) (by lay) (by lay) .add) (fun σ3 e3 => ?_)
  refine runs_seq (runs_sconst (by lay) 2) (fun σ4 e4 => ?_)
  refine runs_seq (runs_sop2 (by lay) (by lay) (by lay) .mul) (fun σ5 e5 => ?_)
  refine runs_seq (runs_sop2 (by lay) (by lay) (by lay) .add) (fun σ6 e6 => ?_)
  refine runs_seq (runs_sop2 (by lay) (by lay) (by lay) .mul) (fun σ7 e7 => ?_)
  refine runs_seq (runs_sconst (by lay) 1600) (fun σ8 e8 => ?_)
  refine runs_seq (runs_sop2 (by lay) (by lay) (by lay) .div) (fun σ9 e9 => ?_)
  refine runs_seq (runs_sop2 (by lay) (by lay) (by lay) .add) (fun σ10 e10 => ?_)
  have g10 : G σ10 := by
    rw [e10, e9, e8, e7, e6, e5, e4, e3, e2, e1]
    exact own _ _ _ (by lay) (by lay) (own _ _ _ (by lay) (by lay) (own _ _ _ (by lay) (by lay)
      (own _ _ _ (by lay) (by lay) (own _ _ _ (by lay) (by lay) (own _ _ _ (by lay) (by lay)
      (own _ _ _ (by lay) (by lay) (own _ _ _ (by lay) (by lay) (own _ _ _ (by lay) (by lay)
      (own _ _ _ (by lay) (by lay) (keep_refl hI))))))))))
  have l10 : σ10.sc (V.sB + 35) = W.lam / 4 := by
    rw [e10, e9, e8, e7, e6, e5, e4, e3, e2, e1]; simp [Op2.eval, w22]
  have p1_10 : σ10.sc (V.sB + 36) = W.p0 + W.lam := by
    rw [e10, e9, e8, e7, e6, e5, e4, e3, e2, e1]; simp [Op2.eval, w21, w22]
  have p2_10 : σ10.sc (V.sB + 37) = W.p0 + 2 * W.lam := by
    rw [e10, e9, e8, e7, e6, e5, e4, e3, e2, e1]; simp [Op2.eval, w21, w22]
  have η10 : σ10.sc (V.sB + 38) = τ * W.lam / 1600 := by
    rw [e10, e9, e8, e7, e6, e5, e4, e3, e2, e1]; simp [Op2.eval, w22, hτ]
  have s10 : σ10.sc (V.sB + 39) = W.p0 + W.lam + W.lam / 4 := by
    rw [e10, e9, e8, e7, e6, e5, e4, e3, e2, e1]; simp [Op2.eval, w21, w22]
  have kn10 : Kn σ10 [(V.sB + 38, τ * W.lam / 1600), (V.sB + 37, W.p0 + 2 * W.lam), (V.sB + 36, W.p0 + W.lam),
      (V.sB + 35, W.lam / 4), (V.sB + 32, 0), (V.sB + 28, 1), (V.sB + 29, 1), (V.sB + 24, W.v1), (V.sB + 25, W.v2),
      (V.sB + 26, W.v3)] := by
    refine Kn.add (Kn.add (Kn.add (Kn.add ?_ l10) p1_10) p2_10) η10
    rw [e10, e9, e8, e7, e6, e5, e4, e3, e2, e1]
    refine Kn.set (Kn.set (Kn.set (Kn.set (Kn.set (Kn.set (Kn.set (Kn.set (Kn.set (Kn.set kn0
      (by kn_tac) _) (by kn_tac) _) (by kn_tac) _) (by kn_tac) _) (by kn_tac) _) (by kn_tac) _) (by kn_tac) _)
      (by kn_tac) _) (by kn_tac) _) (by kn_tac) _
  -- u1
  refine runs_lineEv hp hmem hIq (dst := V.sB + 40) ⟨by omega, by omega⟩ σ10 (Gdv _ g10) (Gone _ g10) g10.1 i
    (Gi _ g10) (kn10.get (x := V.sB + 32) (v := 0) (by simp)) (GB _ g10) (fun u1 σ11 hu1 e11 k11 => ?_) (fun σ' hu1 f1 f2 k' => ?_)
  rotate_left
  · rw [Glev _ g10, s10, η10] at hu1
    refine ⟨?_, by rw [k'.sc (by nmem_tac) (hp.sB_sQ (by lay) (by lay)), kn10.get (x := V.sB + 32) (v := 0) (by simp)], liftF _ _ g10 k'⟩
    have : lineHalve ev τ W = none := by simp [lineHalve, hu1]
    rw [this]; exact ⟨f1, f2⟩
  rw [Glev _ g10, s10, η10] at hu1
  have g11 := lift _ _ _ (by omega) (by omega) g10 k11
  have kn11 := Kn.add (Kn.ofKP kn10 k11 (by kn_tac) (by kn_tac)) e11
  refine runs_seq (runs_sconst (by lay) 2) (fun σ12 e12 => ?_)
  refine runs_seq (runs_sop2 (by lay) (by lay) (by lay) .mul) (fun σ13 e13 => ?_)
  refine runs_seq (runs_sop2 (by lay) (by lay) (by lay) .add) (fun σ14 e14 => ?_)
  have g14 : G σ14 := by
    rw [e14, e13, e12]
    exact own _ _ _ (by lay) (by lay) (own _ _ _ (by lay) (by lay) (own _ _ _ (by lay) (by lay) g11))
  have kn14 := Kn.setEq (Kn.setEq (Kn.setEq kn11 (by kn_tac) e12) (by kn_tac) e13) (by kn_tac) e14
  have s14 : σ14.sc (V.sB + 39) = W.p0 + W.lam + 2 * (W.lam / 4) := by
    rw [e14, e13, e12]; simp [Op2.eval, kn11.get (x := V.sB + 35) (v := W.lam / 4) (by simp), kn11.get (x := V.sB + 36) (v := W.p0 + W.lam) (by simp)]
  -- u2
  refine runs_lineEv hp hmem hIq (dst := V.sB + 41) ⟨by omega, by omega⟩ σ14 (Gdv _ g14) (Gone _ g14) g14.1 i
    (Gi _ g14) (kn14.get (x := V.sB + 32) (v := 0) (by simp)) (GB _ g14) (fun u2 σ15 hu2 e15 k15 => ?_) (fun σ' hu2 f1 f2 k' => ?_)
  rotate_left
  · rw [Glev _ g14, s14, kn14.get (x := V.sB + 38) (v := τ * W.lam / 1600) (by simp)] at hu2
    refine ⟨?_, by rw [k'.sc (by nmem_tac) (hp.sB_sQ (by lay) (by lay)), kn14.get (x := V.sB + 32) (v := 0) (by simp)], liftF _ _ g14 k'⟩
    have : lineHalve ev τ W = none := by simp [lineHalve, hu1, hu2]
    rw [this]; exact ⟨f1, f2⟩
  rw [Glev _ g14, s14, kn14.get (x := V.sB + 38) (v := τ * W.lam / 1600) (by simp)] at hu2
  have g15 := lift _ _ _ (by omega) (by omega) g14 k15
  have kn15 := Kn.add (Kn.ofKP kn14 k15 (by kn_tac) (by kn_tac)) e15
  refine runs_seq (runs_sconst (by lay) 3) (fun σ16 e16 => ?_)
  refine runs_seq (runs_sop2 (by lay) (by lay) (by lay) .mul) (fun σ17 e17 => ?_)
  refine runs_seq (runs_sop2 (by lay) (by lay) (by lay) .add) (fun σ18 e18 => ?_)
  have g18 : G σ18 := by
    rw [e18, e17, e16]
    exact own _ _ _ (by lay) (by lay) (own _ _ _ (by lay) (by lay) (own _ _ _ (by lay) (by lay) g15))
  have kn18 := Kn.setEq (Kn.setEq (Kn.setEq kn15 (by kn_tac) e16) (by kn_tac) e17) (by kn_tac) e18
  have s18 : σ18.sc (V.sB + 39) = W.p0 + W.lam + 3 * (W.lam / 4) := by
    rw [e18, e17, e16]; simp [Op2.eval, kn15.get (x := V.sB + 35) (v := W.lam / 4) (by simp), kn15.get (x := V.sB + 36) (v := W.p0 + W.lam) (by simp)]
  -- u3
  refine runs_lineEv hp hmem hIq (dst := V.sB + 42) ⟨by omega, by omega⟩ σ18 (Gdv _ g18) (Gone _ g18) g18.1 i
    (Gi _ g18) (kn18.get (x := V.sB + 32) (v := 0) (by simp)) (GB _ g18) (fun u3 σ19 hu3 e19 k19 => ?_) (fun σ' hu3 f1 f2 k' => ?_)
  rotate_left
  · rw [Glev _ g18, s18, kn18.get (x := V.sB + 38) (v := τ * W.lam / 1600) (by simp)] at hu3
    refine ⟨?_, by rw [k'.sc (by nmem_tac) (hp.sB_sQ (by lay) (by lay)), kn18.get (x := V.sB + 32) (v := 0) (by simp)], liftF _ _ g18 k'⟩
    have : lineHalve ev τ W = none := by simp [lineHalve, hu1, hu2, hu3]
    rw [this]; exact ⟨f1, f2⟩
  rw [Glev _ g18, s18, kn18.get (x := V.sB + 38) (v := τ * W.lam / 1600) (by simp)] at hu3
  have g19 := lift _ _ _ (by omega) (by omega) g18 k19
  have kn19 := Kn.add (Kn.ofKP kn18 k19 (by kn_tac) (by kn_tac)) e19
  refine runs_seq (runs_sop2 (by lay) (by lay) (by lay) .add) (fun σ20 e20 => ?_)
  have g20 : G σ20 := by rw [e20]; exact own _ _ _ (by lay) (by lay) g19
  have kn20 := Kn.setEq kn19 (by kn_tac) e20
  have s20 : σ20.sc (V.sB + 39) = W.p0 + 2 * W.lam + W.lam / 4 := by
    rw [e20]; simp [Op2.eval, kn19.get (x := V.sB + 35) (v := W.lam / 4) (by simp), kn19.get (x := V.sB + 37) (v := W.p0 + 2 * W.lam) (by simp)]
  -- u5
  refine runs_lineEv hp hmem hIq (dst := V.sB + 43) ⟨by omega, by omega⟩ σ20 (Gdv _ g20) (Gone _ g20) g20.1 i
    (Gi _ g20) (kn20.get (x := V.sB + 32) (v := 0) (by simp)) (GB _ g20) (fun u5 σ21 hu5 e21 k21 => ?_) (fun σ' hu5 f1 f2 k' => ?_)
  rotate_left
  · rw [Glev _ g20, s20, kn20.get (x := V.sB + 38) (v := τ * W.lam / 1600) (by simp)] at hu5
    refine ⟨?_, by rw [k'.sc (by nmem_tac) (hp.sB_sQ (by lay) (by lay)), kn20.get (x := V.sB + 32) (v := 0) (by simp)], liftF _ _ g20 k'⟩
    have : lineHalve ev τ W = none := by simp [lineHalve, hu1, hu2, hu3, hu5]
    rw [this]; exact ⟨f1, f2⟩
  rw [Glev _ g20, s20, kn20.get (x := V.sB + 38) (v := τ * W.lam / 1600) (by simp)] at hu5
  have g21 := lift _ _ _ (by omega) (by omega) g20 k21
  have kn21 := Kn.add (Kn.ofKP kn20 k21 (by kn_tac) (by kn_tac)) e21
  refine runs_seq (runs_sconst (by lay) 2) (fun σ22 e22 => ?_)
  refine runs_seq (runs_sop2 (by lay) (by lay) (by lay) .mul) (fun σ23 e23 => ?_)
  refine runs_seq (runs_sop2 (by lay) (by lay) (by lay) .add) (fun σ24 e24 => ?_)
  have g24 : G σ24 := by
    rw [e24, e23, e22]
    exact own _ _ _ (by lay) (by lay) (own _ _ _ (by lay) (by lay) (own _ _ _ (by lay) (by lay) g21))
  have kn24 := Kn.setEq (Kn.setEq (Kn.setEq kn21 (by kn_tac) e22) (by kn_tac) e23) (by kn_tac) e24
  have s24 : σ24.sc (V.sB + 39) = W.p0 + 2 * W.lam + 2 * (W.lam / 4) := by
    rw [e24, e23, e22]; simp [Op2.eval, kn21.get (x := V.sB + 35) (v := W.lam / 4) (by simp), kn21.get (x := V.sB + 37) (v := W.p0 + 2 * W.lam) (by simp)]
  -- u6
  refine runs_lineEv hp hmem hIq (dst := V.sB + 44) ⟨by omega, by omega⟩ σ24 (Gdv _ g24) (Gone _ g24) g24.1 i
    (Gi _ g24) (kn24.get (x := V.sB + 32) (v := 0) (by simp)) (GB _ g24) (fun u6 σ25 hu6 e25 k25 => ?_) (fun σ' hu6 f1 f2 k' => ?_)
  rotate_left
  · rw [Glev _ g24, s24, kn24.get (x := V.sB + 38) (v := τ * W.lam / 1600) (by simp)] at hu6
    refine ⟨?_, by rw [k'.sc (by nmem_tac) (hp.sB_sQ (by lay) (by lay)), kn24.get (x := V.sB + 32) (v := 0) (by simp)], liftF _ _ g24 k'⟩
    have : lineHalve ev τ W = none := by simp [lineHalve, hu1, hu2, hu3, hu5, hu6]
    rw [this]; exact ⟨f1, f2⟩
  rw [Glev _ g24, s24, kn24.get (x := V.sB + 38) (v := τ * W.lam / 1600) (by simp)] at hu6
  have g25 := lift _ _ _ (by omega) (by omega) g24 k25
  have kn25 := Kn.add (Kn.ofKP kn24 k25 (by kn_tac) (by kn_tac)) e25
  refine runs_seq (runs_sconst (by lay) 3) (fun σ26 e26 => ?_)
  refine runs_seq (runs_sop2 (by lay) (by lay) (by lay) .mul) (fun σ27 e27 => ?_)
  refine runs_seq (runs_sop2 (by lay) (by lay) (by lay) .add) (fun σ28 e28 => ?_)
  have g28 : G σ28 := by
    rw [e28, e27, e26]
    exact own _ _ _ (by lay) (by lay) (own _ _ _ (by lay) (by lay) (own _ _ _ (by lay) (by lay) g25))
  have kn28 := Kn.setEq (Kn.setEq (Kn.setEq kn25 (by kn_tac) e26) (by kn_tac) e27) (by kn_tac) e28
  have s28 : σ28.sc (V.sB + 39) = W.p0 + 2 * W.lam + 3 * (W.lam / 4) := by
    rw [e28, e27, e26]; simp [Op2.eval, kn25.get (x := V.sB + 35) (v := W.lam / 4) (by simp), kn25.get (x := V.sB + 37) (v := W.p0 + 2 * W.lam) (by simp)]
  -- u7
  refine runs_lineEv hp hmem hIq (dst := V.sB + 45) ⟨by omega, by omega⟩ σ28 (Gdv _ g28) (Gone _ g28) g28.1 i
    (Gi _ g28) (kn28.get (x := V.sB + 32) (v := 0) (by simp)) (GB _ g28) (fun u7 σ29 hu7 e29 k29 => ?_) (fun σ' hu7 f1 f2 k' => ?_)
  rotate_left
  · rw [Glev _ g28, s28, kn28.get (x := V.sB + 38) (v := τ * W.lam / 1600) (by simp)] at hu7
    refine ⟨?_, by rw [k'.sc (by nmem_tac) (hp.sB_sQ (by lay) (by lay)), kn28.get (x := V.sB + 32) (v := 0) (by simp)], liftF _ _ g28 k'⟩
    have : lineHalve ev τ W = none := by simp [lineHalve, hu1, hu2, hu3, hu5, hu6, hu7]
    rw [this]; exact ⟨f1, f2⟩
  rw [Glev _ g28, s28, kn28.get (x := V.sB + 38) (v := τ * W.lam / 1600) (by simp)] at hu7
  have g29 := lift _ _ _ (by omega) (by omega) g28 k29
  have kn29 := Kn.add (Kn.ofKP kn28 k29 (by kn_tac) (by kn_tac)) e29
  -- the spreads
  refine runs_mono (K := 1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + 9)))))))) ?_ (by norm_num) (fun _ h => h)
  refine runs_seq (runs_sop2 (by lay) (by lay) (by lay) .sub) (fun σ30 e30 => ?_)
  refine runs_seq (runs_sop2 (by lay) (by lay) (by lay) .sub) (fun σ31 e31 => ?_)
  refine runs_seq (runs_sop2 (by lay) (by lay) (by lay) .sub) (fun σ32 e32 => ?_)
  refine runs_seq (runs_sop2 (by lay) (by lay) (by lay) .div) (fun σ33 e33 => ?_)
  refine runs_seq (runs_sop2 (by lay) (by lay) (by lay) .sub) (fun σ34 e34 => ?_)
  refine runs_seq (runs_sop2 (by lay) (by lay) (by lay) .sub) (fun σ35 e35 => ?_)
  refine runs_seq (runs_sop2 (by lay) (by lay) (by lay) .sub) (fun σ36 e36 => ?_)
  refine runs_seq (runs_sop2 (by lay) (by lay) (by lay) .div) (fun σ37 e37 => ?_)
  have g37 : G σ37 := by
    rw [e37, e36, e35, e34, e33, e32, e31, e30]
    exact own _ _ _ (by lay) (by lay) (own _ _ _ (by lay) (by lay) (own _ _ _ (by lay) (by lay)
      (own _ _ _ (by lay) (by lay) (own _ _ _ (by lay) (by lay) (own _ _ _ (by lay) (by lay)
      (own _ _ _ (by lay) (by lay) (own _ _ _ (by lay) (by lay) g29)))))))
  have kn37 := Kn.setEq (Kn.setEq (Kn.setEq (Kn.setEq (Kn.setEq (Kn.setEq (Kn.setEq (Kn.setEq kn29
    (by kn_tac) e30) (by kn_tac) e31) (by kn_tac) e32) (by kn_tac) e33) (by kn_tac) e34) (by kn_tac) e35)
    (by kn_tac) e36) (by kn_tac) e37
  let Aw : LineWin := ⟨W.p0 + W.lam, W.lam / 4, W.v1, u1, u2, u3, W.v2⟩
  let Bw : LineWin := ⟨W.p0 + 2 * W.lam, W.lam / 4, W.v2, u5, u6, u7, W.v3⟩
  have spA : σ37.sc (V.sB + 46) = Aw.spread := by
    rw [e37, e36, e35, e34, e33, e32, e31, e30]
    simp [Op2.eval, LineWin.spread, Aw, kn29.get (x := V.sB + 25) (v := W.v2) (by simp),
      kn29.get (x := V.sB + 42) (v := u3) (by simp), kn29.get (x := V.sB + 40) (v := u1) (by simp),
      kn29.get (x := V.sB + 24) (v := W.v1) (by simp), kn29.get (x := V.sB + 35) (v := W.lam / 4) (by simp)]
  have spB : σ37.sc (V.sB + 47) = Bw.spread := by
    rw [e37, e36, e35, e34, e33, e32, e31, e30]
    simp [Op2.eval, LineWin.spread, Bw, kn29.get (x := V.sB + 26) (v := W.v3) (by simp),
      kn29.get (x := V.sB + 45) (v := u7) (by simp), kn29.get (x := V.sB + 43) (v := u5) (by simp),
      kn29.get (x := V.sB + 25) (v := W.v2) (by simp), kn29.get (x := V.sB + 35) (v := W.lam / 4) (by simp)]
  have hX : lineHalve ev τ W = some (if Bw.spread < Aw.spread then Bw else Aw) := by
    simp only [lineHalve, hu1, hu2, hu3, hu5, hu6, hu7, Option.pure_def]
    rfl
  rw [hX]
  have q35 := kn37.get (x := V.sB + 35) (v := W.lam / 4) (by simp)
  have q36 := kn37.get (x := V.sB + 36) (v := W.p0 + W.lam) (by simp)
  have q37 := kn37.get (x := V.sB + 37) (v := W.p0 + 2 * W.lam) (by simp)
  have q24 := kn37.get (x := V.sB + 24) (v := W.v1) (by simp)
  have q25 := kn37.get (x := V.sB + 25) (v := W.v2) (by simp)
  have q26 := kn37.get (x := V.sB + 26) (v := W.v3) (by simp)
  have q40 := kn37.get (x := V.sB + 40) (v := u1) (by simp)
  have q41 := kn37.get (x := V.sB + 41) (v := u2) (by simp)
  have q42 := kn37.get (x := V.sB + 42) (v := u3) (by simp)
  have q43 := kn37.get (x := V.sB + 43) (v := u5) (by simp)
  have q44 := kn37.get (x := V.sB + 44) (v := u6) (by simp)
  have q45 := kn37.get (x := V.sB + 45) (v := u7) (by simp)
  have q28 := kn37.get (x := V.sB + 28) (v := 1) (by simp)
  have q29 := kn37.get (x := V.sB + 29) (v := 1) (by simp)
  have q32 := kn37.get (x := V.sB + 32) (v := 0) (by simp)
  by_cases hc : Bw.spread < Aw.spread
  · rw [ite_eq_left hc]
    refine runs_mono (K := (1 + (1 + (1 + (1 + (1 + (1 + 1)))))) + 1)
      (runs_ifS_t (by lay) (by lay) (by rw [spA, spB]; exact hc) ?_) (by norm_num) (fun _ h => h)
    refine runs_seq (runs_smov (by lay) (by lay)) (fun t1 f1 => ?_)
    refine runs_seq (runs_smov (by lay) (by lay)) (fun t2 f2 => ?_)
    refine runs_seq (runs_smov (by lay) (by lay)) (fun t3 f3 => ?_)
    refine runs_seq (runs_smov (by lay) (by lay)) (fun t4 f4 => ?_)
    refine runs_seq (runs_smov (by lay) (by lay)) (fun t5 f5 => ?_)
    refine runs_seq (runs_smov (by lay) (by lay)) (fun t6 f6 => ?_)
    refine runs_mono (runs_smov (by lay) (by lay)) le_rfl (fun t7 f7 => ?_)
    refine ⟨?_, ?_, ?_⟩
    · rw [f7, f6, f5, f4, f3, f2, f1]
      simp only [Option.map_some, LRel, WinAt]
      simp [q37, q35, q25, q26, q43, q44, q45, q28, q29, Bw]
    · rw [f7, f6, f5, f4, f3, f2, f1]; simp [q32]
    · rw [f7, f6, f5, f4, f3, f2, f1]
      exact own _ _ _ (by lay) (by lay) (own _ _ _ (by lay) (by lay) (own _ _ _ (by lay) (by lay)
        (own _ _ _ (by lay) (by lay) (own _ _ _ (by lay) (by lay) (own _ _ _ (by lay) (by lay)
        (own _ _ _ (by lay) (by lay) g37))))))
  · rw [ite_eq_right hc]
    refine runs_mono (K := (1 + (1 + (1 + (1 + (1 + (1 + 1)))))) + 2)
      (runs_ifS_f (by lay) (by lay) (by rw [spA, spB]; exact hc) ?_) (by norm_num) (fun _ h => h)
    refine runs_seq (runs_smov (by lay) (by lay)) (fun t1 f1 => ?_)
    refine runs_seq (runs_smov (by lay) (by lay)) (fun t2 f2 => ?_)
    refine runs_seq (runs_smov (by lay) (by lay)) (fun t3 f3 => ?_)
    refine runs_seq (runs_smov (by lay) (by lay)) (fun t4 f4 => ?_)
    refine runs_seq (runs_smov (by lay) (by lay)) (fun t5 f5 => ?_)
    refine runs_seq (runs_smov (by lay) (by lay)) (fun t6 f6 => ?_)
    refine runs_mono (runs_smov (by lay) (by lay)) le_rfl (fun t7 f7 => ?_)
    refine ⟨?_, ?_, ?_⟩
    · rw [f7, f6, f5, f4, f3, f2, f1]
      simp only [Option.map_some, LRel, WinAt]
      simp [q36, q35, q24, q25, q40, q41, q42, q28, q29, Aw]
    · rw [f7, f6, f5, f4, f3, f2, f1]; simp [q32]
    · rw [f7, f6, f5, f4, f3, f2, f1]
      exact own _ _ _ (by lay) (by lay) (own _ _ _ (by lay) (by lay) (own _ _ _ (by lay) (by lay)
        (own _ _ _ (by lay) (by lay) (own _ _ _ (by lay) (by lay) (own _ _ _ (by lay) (by lay)
        (own _ _ _ (by lay) (by lay) g37))))))

/-! ## The check of a window and the loop -/

set_option maxHeartbeats 1000000 in
/-- The check of the current window: above `τ λ/2`, `more`; else the stop at `(p₀ + 2λ, λ)`. -/
theorem runs_lineCheck {Iq : Env d → Prop} {nsQ ssQ asQ : List ℕ} (hp : V.Ok L nsQ ssQ asQ) (hIq : IqRule V Iq)
    {more : Cmd} {Km : ℕ} {Post : Env d → Prop}
    (σ : Env d) (hI : Iq σ) (W : LineWin) (hW : LRel V (some (.inl W)) σ) (hz : σ.sc (V.sB + 32) = 0)
    (hmore : ∀ σ', LRel V (some (.inl W)) σ' → σ'.sc (V.sB + 32) = 0 →
      σ.sc (V.sB + 100) * W.lam / 2 < W.sd →
      KP Iq nsQ ssQ asQ [] [V.sB + 33, V.sB + 34, V.sB + 48, V.sB + 49] [] σ σ' → Runs L w more σ' Km Post)
    (hdone : ∀ σ', W.sd ≤ σ.sc (V.sB + 100) * W.lam / 2 →
      LRel V (some (.inr (W.p0 + 2 * W.lam, W.lam))) σ' → σ'.sc (V.sB + 32) = 0 →
      KP Iq nsQ ssQ asQ [] [V.sB + 29, V.sB + 30, V.sB + 31, V.sB + 33, V.sB + 34, V.sB + 48, V.sB + 49] []
        σ σ' → Post σ') :
    Runs L w (lineCheck L V more) σ (6 + (Km + 6)) Post := by
  layout_facts
  obtain ⟨f28, f29, w21, w22, w23, w24, w25, w26, w27⟩ := hW
  let OS : List ℕ := [V.sB + 29, V.sB + 30, V.sB + 31, V.sB + 33, V.sB + 34, V.sB + 48, V.sB + 49]
  have hOS : ∀ j ∈ OS, j ∈ apS V := by
    intro j hj; simp only [OS, apS, List.mem_cons, List.mem_range'_1, List.not_mem_nil, or_false] at hj ⊢; omega
  let S4 : List ℕ := [V.sB + 33, V.sB + 34, V.sB + 48, V.sB + 49]
  have hS4 : ∀ j ∈ S4, j ∈ apS V := by
    intro j hj; simp only [S4, apS, List.mem_cons, List.mem_range'_1, List.not_mem_nil, or_false] at hj ⊢; omega
  have own : ∀ σa (q : ℕ) (v : ℝ), q ∈ OS → KP Iq nsQ ssQ asQ [] OS [] σ σa →
      KP Iq nsQ ssQ asQ [] OS [] σ (σa.setSc q v) :=
    fun σa q v hq g => keep_own hIq (by simp) hOS (by simp) g (frame_setSc _ _ _) (by simp) (by simpa using hq)
      (by simp)
  have own4 : ∀ σa (q : ℕ) (v : ℝ), q ∈ S4 → KP Iq nsQ ssQ asQ [] S4 [] σ σa →
      KP Iq nsQ ssQ asQ [] S4 [] σ (σa.setSc q v) :=
    fun σa q v hq g => keep_own hIq (by simp) hS4 (by simp) g (frame_setSc _ _ _) (by simp) (by simpa using hq)
      (by simp)
  unfold lineCheck
  refine runs_mono (K := 1 + (1 + (1 + (1 + (1 + (1 + (Km + 6))))))) ?_ (by omega) (fun _ h => h)
  refine runs_seq (runs_sop2 (by lay) (by lay) (by lay) .add) (fun σ1 e1 => ?_)
  refine runs_seq (runs_sconst (by lay) 2) (fun σ2 e2 => ?_)
  refine runs_seq (runs_sop2 (by lay) (by lay) (by lay) .mul) (fun σ3 e3 => ?_)
  refine runs_seq (runs_sop2 (by lay) (by lay) (by lay) .sub) (fun σ4 e4 => ?_)
  refine runs_seq (runs_sop2 (by lay) (by lay) (by lay) .mul) (fun σ5 e5 => ?_)
  refine runs_seq (runs_sop2 (by lay) (by lay) (by lay) .div) (fun σ6 e6 => ?_)
  have k6 : KP Iq nsQ ssQ asQ [] S4 [] σ σ6 := by
    rw [e6, e5, e4, e3, e2, e1]
    exact own4 _ _ _ (by simp [S4]) (own4 _ _ _ (by simp [S4]) (own4 _ _ _ (by simp [S4]) (own4 _ _ _ (by simp [S4])
      (own4 _ _ _ (by simp [S4]) (own4 _ _ _ (by simp [S4]) (keep_refl hI))))))
  have sd6 : σ6.sc (V.sB + 34) = W.sd := by
    rw [e6, e5, e4, e3, e2, e1]; simp [Op2.eval, LineWin.sd, w24, w25, w26]
  have t6 : σ6.sc (V.sB + 33) = σ.sc (V.sB + 100) * W.lam / 2 := by
    rw [e6, e5, e4, e3, e2, e1]; simp [Op2.eval, w22]
  have kk : ∀ x, x ∉ S4 → σ6.sc x = σ.sc x := fun x hx => by
    rw [e6, e5, e4, e3, e2, e1]
    simp only [S4, List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    simp [hx.1, hx.2.1, hx.2.2.1, hx.2.2.2]
  by_cases hc : σ.sc (V.sB + 100) * W.lam / 2 < W.sd
  · refine runs_mono (K := Km + 1) (runs_ifS_t (by lay) (by lay) (by rw [t6, sd6]; exact hc) ?_) (by omega)
      (fun _ h => h)
    refine hmore σ6 ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ ?_ hc k6
    · rw [kk (V.sB + 28) (by simp [S4])]; exact f28
    · rw [kk (V.sB + 29) (by simp [S4])]; exact f29
    · rw [kk (V.sB + 21) (by simp [S4])]; exact w21
    · rw [kk (V.sB + 22) (by simp [S4])]; exact w22
    · rw [kk (V.sB + 23) (by simp [S4])]; exact w23
    · rw [kk (V.sB + 24) (by simp [S4])]; exact w24
    · rw [kk (V.sB + 25) (by simp [S4])]; exact w25
    · rw [kk (V.sB + 26) (by simp [S4])]; exact w26
    · rw [kk (V.sB + 27) (by simp [S4])]; exact w27
    · rw [kk (V.sB + 32) (by simp [S4])]; exact hz
  · refine runs_mono (K := (1 + (1 + (1 + 1))) + 2) (runs_ifS_f (by lay) (by lay) (by rw [t6, sd6]; exact hc) ?_)
      (by omega) (fun _ h => h)
    unfold lineDone
    refine runs_seq (runs_sop2 (by lay) (by lay) (by lay) .mul) (fun σ7 e7 => ?_)
    refine runs_seq (runs_sop2 (by lay) (by lay) (by lay) .add) (fun σ8 e8 => ?_)
    refine runs_seq (runs_smov (by lay) (by lay)) (fun σ9 e9 => ?_)
    refine runs_mono (runs_sconst (by lay) 0) le_rfl (fun σ10 e10 => ?_)
    have h49 : σ6.sc (V.sB + 49) = 2 := by rw [e6, e5, e4, e3, e2]; simp
    refine hdone σ10 (not_lt.1 hc) ⟨?_, ?_, ?_, ?_⟩ ?_ ?_
    · rw [e10, e9, e8, e7]; simp [kk (V.sB + 28) (by simp [S4]), f28]
    · rw [e10]; simp
    · rw [e10, e9, e8, e7]; simp [Op2.eval, kk (V.sB + 21) (by simp [S4]), kk (V.sB + 22) (by simp [S4]), w21, w22,
        h49]
    · rw [e10, e9, e8, e7]; simp [kk (V.sB + 22) (by simp [S4]), w22]
    · rw [e10, e9, e8, e7]; simp [kk (V.sB + 32) (by simp [S4]), hz]
    · rw [e10, e9, e8, e7]
      exact own _ _ _ (by simp [OS]) (own _ _ _ (by simp [OS]) (own _ _ _ (by simp [OS]) (own _ _ _ (by simp [OS])
        (keep_mono (ON' := []) (OS' := OS) (OA' := []) k6 (fun _ h => h)
          (by intro j hj; simp only [S4, OS, List.mem_cons, List.not_mem_nil, or_false] at hj ⊢; omega) (fun _ h => h)))))

theorem LRel.setNat {st : Option (LineWin ⊕ (ℝ × ℝ))} {σ : Env d} (h : LRel V st σ) (j v : ℕ) :
    LRel V st (σ.setNat j v) := by
  rcases st with _ | W | p <;> exact h

/-- The step bound of one pass of the loop of LINE. -/
def kLB (d Kq B : ℕ) : ℕ := kLH d Kq B + 13

set_option maxHeartbeats 2000000 in
open Classical in
/-- One pass of the loop of LINE: `lineSt` on the state. -/
theorem runs_lineBody {Q : Set (Fin d → ℝ)} {Iq : Env d → Prop} {Kq : ℕ} {nsQ ssQ asQ : List ℕ}
    (hp : V.Ok L nsQ ssQ asQ) (hmem : MemRule L w memQ V Q Iq Kq nsQ ssQ asQ) (hIq : IqRule V Iq)
    (σ : Env d) (hd : σ.nat V.dv = d) (h1 : σ.nat V.one = 1) (hI : Iq σ) (i : Fin d)
    (hi : σ.nat (V.nB + 6) = i) (st : Option (LineWin ⊕ (ℝ × ℝ))) (hst : LRel V st σ)
    (hz : σ.sc (V.sB + 32) = 0) :
    Runs L w (ifS L (V.sB + 32) (V.sB + 29) (lineCheck L V (lineHalveCode L memQ V)) .skip) σ
      (kLB d Kq (σ.nat (V.nB + 11)))
      (fun σ' => LRel V (lineSt (lev Q V σ i) (σ.sc (V.sB + 100)) st) σ' ∧ σ'.sc (V.sB + 32) = 0 ∧
        KP Iq nsQ ssQ asQ (lineN V) (lineS V) (lineA V) σ σ') := by
  layout_facts
  have skip : ¬ σ.sc (V.sB + 32) < σ.sc (V.sB + 29) → lineSt (lev Q V σ i) (σ.sc (V.sB + 100)) st = st →
      Runs L w (ifS L (V.sB + 32) (V.sB + 29) (lineCheck L V (lineHalveCode L memQ V)) .skip) σ
      (kLB d Kq (σ.nat (V.nB + 11)))
      (fun σ' => LRel V (lineSt (lev Q V σ i) (σ.sc (V.sB + 100)) st) σ' ∧ σ'.sc (V.sB + 32) = 0 ∧
        KP Iq nsQ ssQ asQ (lineN V) (lineS V) (lineA V) σ σ') := fun hc hs =>
    runs_mono (runs_ifS_f (by lay) (by lay) hc (runs_skip σ)) (by unfold kLB; omega)
      (fun σ' e => by subst e; rw [hs]; exact ⟨hst, hz, keep_refl hI⟩)
  rcases st with _ | W | p
  · obtain ⟨-, h29⟩ := hst
    exact skip (by rw [hz, h29]; exact lt_irrefl 0) rfl
  · obtain ⟨h28, h29, hW⟩ := id hst
    refine runs_mono (K := 6 + (kLH d Kq (σ.nat (V.nB + 11)) + 6) + 1)
      (runs_ifS_t (by lay) (by lay) (by rw [hz, h29]; exact one_pos) ?_) (by unfold kLB; omega) (fun _ h => h)
    refine runs_lineCheck hp hIq σ hI W hst hz (fun σ' hW' hz' hc k' => ?_) (fun σ' hc hW' hz' k' => ?_)
    · have e11 : σ'.nat (V.nB + 11) = σ.nat (V.nB + 11) := k'.nat (by simp) (hp.nN_nQ (by omega) (by omega))
      refine runs_mono (runs_lineHalveCode hp hmem hIq σ' (by rw [k'.nat (by simp) hp.dv_nQ, hd])
        (by rw [k'.nat (by simp) hp.one_nQ, h1]) k'.1 i
        (by rw [k'.nat (by simp) (hp.nN_nQ (by omega) (by omega)), hi]) W hW' hz')
        (le_of_eq (by rw [e11])) (fun σ'' h'' => ⟨?_, h''.2.1, ?_⟩)
      · have el : lev Q V σ' i = lev Q V σ i :=
          lev_congr hp k' i (by simp) (by nmem_tac) (by nmem_tac) (by simp) (by simp)
        have e100 : σ'.sc (V.sB + 100) = σ.sc (V.sB + 100) := k'.sc (by nmem_tac) (hp.sB_sQ (by omega) (by omega))
        have hL := h''.1
        rw [el, e100] at hL
        simp only [lineSt, not_le.2 hc, ite_false]
        exact hL
      · exact keep_trans (keep_mono (ON' := lineN V) (OS' := lineS V) (OA' := lineA V) k' (fun _ h => by simp at h)
          (by intro j hj; simp only [List.mem_cons, List.mem_range'_1, List.not_mem_nil, or_false] at hj ⊢; omega)
          (fun _ h => by simp at h)) h''.2.2
    · simp only [lineSt, hc, ite_true]
      exact ⟨hW', hz', keep_mono (ON' := lineN V) (OS' := lineS V) (OA' := lineA V) k' (fun _ h => by simp at h)
          (by intro j hj; simp only [List.mem_cons, List.mem_range'_1, List.not_mem_nil, or_false] at hj ⊢; omega)
          (fun _ h => by simp at h)⟩
  · obtain ⟨-, h29, -⟩ := id hst
    exact skip (by rw [hz, h29]; exact lt_irrefl 0) rfl

set_option maxHeartbeats 1000000 in
/-- The last check of LINE: `lineEnd` on the state. -/
theorem runs_lineEndCode {Iq : Env d → Prop} {nsQ ssQ asQ : List ℕ} (hp : V.Ok L nsQ ssQ asQ) (hIq : IqRule V Iq)
    (σ : Env d) (hI : Iq σ) (st : Option (LineWin ⊕ (ℝ × ℝ))) (hst : LRel V st σ) (hz : σ.sc (V.sB + 32) = 0) :
    Runs L w (ifS L (V.sB + 32) (V.sB + 29) (lineCheck L V (lineFail L V)) .skip) σ 15
      (fun σ' => LRes V (lineEnd (σ.sc (V.sB + 100)) st) σ' ∧ KP Iq nsQ ssQ asQ [] (lineS V) [] σ σ') := by
  layout_facts
  have hOS : ∀ j ∈ lineS V, j ∈ apS V := by mem_tac
  have own : ∀ σa (q : ℕ) (v : ℝ), V.sB ≤ q → q < V.sB + 50 → KP Iq nsQ ssQ asQ [] (lineS V) [] σ σa →
      KP Iq nsQ ssQ asQ [] (lineS V) [] σ (σa.setSc q v) :=
    fun σa q v h1 h2 g => keep_own hIq (by simp) hOS (by simp) g (frame_setSc _ _ _) (by simp)
      (by intro j hj; simp only [List.mem_singleton] at hj; subst hj; simp only [List.mem_range'_1]; omega) (by simp)
  rcases st with _ | W | p
  · obtain ⟨h28, h29⟩ := id hst
    refine runs_mono (runs_ifS_f (by lay) (by lay) (by rw [hz, h29]; exact lt_irrefl 0) (runs_skip σ)) (by omega)
      (fun σ' e => ?_)
    subst e
    exact ⟨h28, keep_refl hI⟩
  · obtain ⟨h28, h29, hW⟩ := id hst
    refine runs_mono (K := 6 + (2 + 6) + 1)
      (runs_ifS_t (by lay) (by lay) (by rw [hz, h29]; exact one_pos) ?_) le_rfl (fun _ h => h)
    refine runs_lineCheck hp hIq σ hI W hst hz (fun σ' hW' hz' hc k' => ?_) (fun σ' hc hW' hz' k' => ?_)
    · have k0 := keep_mono (ON' := []) (OS' := lineS V) (OA' := []) k' (fun _ h => h)
        (by intro j hj; simp only [List.mem_cons, List.mem_range'_1, List.not_mem_nil, or_false] at hj ⊢; omega)
        (fun _ h => h)
      unfold lineFail
      refine runs_mono (K := 1 + 1) ?_ le_rfl (fun _ h => h)
      refine runs_seq (runs_sconst (by lay) 0) (fun σ1 e1 => ?_)
      refine runs_mono (runs_sconst (by lay) 0) le_rfl (fun σ2 e2 => ?_)
      have hn : ¬ W.sd ≤ σ.sc (V.sB + 100) * W.lam / 2 := not_le.2 hc
      refine ⟨?_, ?_⟩
      · simp only [lineEnd, hn, ite_false, LRes]
        rw [e2, e1]; simp
      · rw [e2, e1]
        exact own _ _ _ (by lay) (by lay) (own _ _ _ (by lay) (by lay) k0)
    · obtain ⟨g28, -, g30, g31⟩ := hW'
      refine ⟨?_, ?_⟩
      · simp only [lineEnd, hc, ite_true, LRes]
        exact ⟨g28, g30, g31⟩
      · exact keep_mono (ON' := []) (OS' := lineS V) (OA' := []) k' (fun _ h => h)
          (by intro j hj; simp only [List.mem_cons, List.mem_range'_1, List.not_mem_nil, or_false] at hj ⊢; omega)
          (fun _ h => h)
  · obtain ⟨h28, h29, h30, h31⟩ := id hst
    refine runs_mono (runs_ifS_f (by lay) (by lay) (by rw [hz, h29]; exact lt_irrefl 0) (runs_skip σ)) (by omega)
      (fun σ' e => ?_)
    subst e
    exact ⟨⟨h28, h30, h31⟩, keep_refl hI⟩

/-- `nmem_tac` through the lists of LINE. -/
macro "nmem'" : tactic => `(tactic| ((try simp only [lineN, lineS, lineA]); nmem_tac))

/-- The step bound of LINE with at most `J` halvings. -/
def kLC (d Kq B J : ℕ) : ℕ := kLF d Kq B + ((J * (kLB d Kq B + 3) + 3) + 15)

set_option maxHeartbeats 4000000 in
open Classical in
/-- The rule of LINE: the result of `line` on the values `lev`, with `ℓ` the scalar `sB + 60`, `τ` the scalar
`sB + 100` and the cap `J` the natural variable `nB + 10`. -/
theorem runs_lineCode {Q : Set (Fin d → ℝ)} {Iq : Env d → Prop} {Kq : ℕ} {nsQ ssQ asQ : List ℕ}
    (hp : V.Ok L nsQ ssQ asQ) (hmem : MemRule L w memQ V Q Iq Kq nsQ ssQ asQ) (hIq : IqRule V Iq)
    (σ : Env d) (hd : σ.nat V.dv = d) (h1 : σ.nat V.one = 1) (hI : Iq σ) (i : Fin d)
    (hi : σ.nat (V.nB + 6) = i) :
    Runs L w (lineCode L memQ V) σ (kLC d Kq (σ.nat (V.nB + 11)) (σ.nat (V.nB + 10)))
      (fun σ' => LRes V (line (lev Q V σ i) (σ.sc (V.sB + 60)) (σ.sc (V.sB + 100)) (σ.nat (V.nB + 10))) σ' ∧
        KP Iq nsQ ssQ asQ (List.range' V.nB 6) (lineS V) (lineA V) σ σ') := by
  layout_facts
  have hON : ∀ j ∈ List.range' V.nB 6, j ∈ apN V := by mem_tac
  have hOS : ∀ j ∈ lineS V, j ∈ apS V := by mem_tac
  have hOA : ∀ j ∈ lineA V, j ∈ apA V := by mem_tac
  have up : ∀ σa σb, KP Iq nsQ ssQ asQ (lineN V) (lineS V) (lineA V) σa σb →
      KP Iq nsQ ssQ asQ (List.range' V.nB 6) (lineS V) (lineA V) σa σb := fun σa σb k =>
    keep_mono k (by intro j hj; simp only [List.mem_range'_1] at hj ⊢; omega) (fun _ h => h) (fun _ h => h)
  have own5 : ∀ σa (v : ℕ), KP Iq nsQ ssQ asQ (List.range' V.nB 6) (lineS V) (lineA V) σ σa →
      KP Iq nsQ ssQ asQ (List.range' V.nB 6) (lineS V) (lineA V) σ (σa.setNat (V.nB + 5) v) :=
    fun σa v g => keep_own hIq hON hOS hOA g (frame_setNat _ _ _)
      (by intro j hj; simp only [List.mem_singleton] at hj; subst hj; simp only [List.mem_range'_1]; omega)
      (by simp) (by simp)
  refine runs_mono (K := kLF d Kq (σ.nat (V.nB + 11)) + ((σ.nat (V.nB + 10) *
    (kLB d Kq (σ.nat (V.nB + 11)) + 3) + 3) + 15)) ?_ (le_of_eq rfl) (fun _ h => h)
  unfold lineCode
  refine runs_seq (runs_lineFirstCode hp hmem hIq σ hd h1 hI i hi) (fun σ1 h1' => ?_)
  obtain ⟨hL1, hz1, k1⟩ := h1'
  let J : ℕ → Env d → Prop := fun t σ' =>
    LRel V ((lineSt (lev Q V σ i) (σ.sc (V.sB + 100)))^[t]
      ((lineFirst (lev Q V σ i) (σ.sc (V.sB + 60)) (σ.sc (V.sB + 100))).map .inl)) σ' ∧
      σ'.sc (V.sB + 32) = 0 ∧ KP Iq nsQ ssQ asQ (List.range' V.nB 6) (lineS V) (lineA V) σ σ'
  have kN1 : σ1.nat (V.nB + 10) = σ.nat (V.nB + 10) := k1.nat (by nmem') (hp.nN_nQ (by omega) (by omega))
  have k1one : σ1.nat V.one = 1 := by rw [k1.nat (by nmem') hp.one_nQ, h1]
  refine runs_seq (runs_forN (i := V.nB + 5) (n := V.nB + 10) (one := V.one) (by lay) (by lay) (by lay)
    (by omega) (by lay) (σ.nat (V.nB + 10)) (kLB d Kq (σ.nat (V.nB + 11))) J σ1 kN1 k1one
    ⟨hL1.setNat _ _, by simpa using hz1, own5 _ _ (up _ _ k1)⟩ ?_) (fun σ2 h2 => ?_)
  · intro t _ σ' hJ hit hnt hot
    obtain ⟨hL, hz, k⟩ := hJ
    have e11 : σ'.nat (V.nB + 11) = σ.nat (V.nB + 11) := k.nat (by nmem') (hp.nN_nQ (by omega) (by omega))
    refine runs_mono (runs_lineBody hp hmem hIq σ' (by rw [k.nat (by nmem') hp.dv_nQ, hd])
      (by rw [k.nat (by nmem') hp.one_nQ, h1]) k.1 i
      (by rw [k.nat (by nmem') (hp.nN_nQ (by omega) (by omega)), hi]) _ hL hz)
      (le_of_eq (by rw [e11])) (fun σ'' h'' => ?_)
    obtain ⟨hL', hz', k'⟩ := h''
    have el : lev Q V σ' i = lev Q V σ i := lev_congr hp k i (by nmem') (by nmem') (by nmem') (by nmem') (by nmem')
    have e100 : σ'.sc (V.sB + 100) = σ.sc (V.sB + 100) := k.sc (by nmem') (hp.sB_sQ (by omega) (by omega))
    rw [el, e100] at hL'
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [k'.nat (by nmem') (hp.nN_nQ (by omega) (by omega)), hit]
    · rw [k'.nat (by nmem') (hp.nN_nQ (by omega) (by omega)), hnt]
    · rw [k'.nat (by nmem') hp.one_nQ, hot]
    · show LRel V _ _
      rw [Function.iterate_succ_apply']; exact hL'.setNat _ _
    · simpa using hz'
    · exact own5 _ _ (keep_trans k (up _ _ k'))
  · obtain ⟨⟨hL2, hz2, k2⟩, -⟩ := h2
    refine runs_mono (runs_lineEndCode hp hIq σ2 k2.1 _ hL2 hz2) le_rfl (fun σ3 h3 => ⟨?_, ?_⟩)
    · have e100 : σ2.sc (V.sB + 100) = σ.sc (V.sB + 100) := k2.sc (by nmem') (hp.sB_sQ (by omega) (by omega))
      have h31 := h3.1
      rw [e100] at h31
      rw [line_eq_lineEnd]; exact h31
    · exact keep_trans k2 (keep_mono h3.2 (fun _ h => by simp at h) (fun _ h => h) (fun _ h => by simp at h))

end AdversarialBco.Poly.AP
