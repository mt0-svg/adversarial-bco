/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.MachAPOne

@[expose] public section

/-!
# The subroutine AP in VL

`runs_apCode`: for every membership code `memQ` with its rule `MemRule` (answer in `qo`, frame `nsQ, ssQ, asQ`,
invariant `Iq` kept by AP's own changes), the code `apCode` answers `apCall` in `ok` (`0` for `none`, `1` for
`some`) and `out`, within `kAP` steps, and changes nothing outside AP's variables and the frame of `memQ`.
`kAP_le`: under `0 < r̲ ≤ r ≤ R ≤ R̄`, `0 < e̲ ≤ e`, `0 ≤ tr P ≤ T` and `‖w‖ ≤ W`, the step bound is at most
`kAPcap d Kq r̲ R̄ T W e̲`, which reads none of `a₀`, `r`, `R`, `P`, `w`, `e`.
-/

namespace AdversarialBco.Poly.AP

open AdversarialBco AdversarialBco.RealRAM AdversarialBco.Poly.Mach AdversarialBco.Poly.Mach.VL Matrix

variable {d : ℕ} {L : Layout} {w : World d} {memQ : Cmd} {V : APVars}

/-- The step bound of AP: ELL-1 when `d = 1`, ELL-cap with the constants of `ellConsts` otherwise. -/
noncomputable def kAP (d Kq : ℕ) (r R : ℝ) (P : Matrix (Fin d) (Fin d) ℝ) (w : Fin d → ℝ) (e : ℝ) : ℕ :=
  if h : d = 1 then kOne Kq (oneCnt R (P ⟨0, by omega⟩ ⟨0, by omega⟩) (w ⟨0, by omega⟩) e) + 2
  else kCap d Kq (ellConsts r R P w e).N (ellConsts r R P w e).J (ellConsts r R P w e).B + 1

/-- The bound on `kAP` from `(d, Kq, r̲, R̄, T, W, e̲)`. -/
noncomputable def kAPcap (d Kq : ℕ) (rb Rb T W eb : ℝ) : ℕ :=
  if d = 1 then kOne Kq (cntBar Rb T W eb) + 2
  else kCap d Kq (nBar d rb Rb T W eb) (jBar d rb Rb T W eb) (bBar d rb Rb T W eb) + 1

theorem apOut_iff (o : Option (Fin d → ℝ)) (σ : Env d) :
    APOut V o σ ↔ (match o with
      | none => σ.sc V.ok = 0
      | some x => σ.sc V.ok = 1 ∧ σ.vec V.out = x) := by
  cases o <;> rfl

/-- The rule of AP. -/
theorem runs_apCode {Q : Set (Fin d → ℝ)} {Iq : Env d → Prop} {Kq : ℕ} {nsQ ssQ asQ : List ℕ}
    (hp : V.Ok L nsQ ssQ asQ) (hmem : MemRule L w memQ V Q Iq Kq nsQ ssQ asQ) (hIq : IqRule V Iq)
    (σ : Env d) (hd : σ.nat V.dv = d) (h1 : σ.nat V.one = 1) (hI : Iq σ) (h0 : 0 < d) :
    Runs L w (apCode L memQ V) σ (kAP d Kq (σ.sc V.r) (σ.sc V.R) (σ.mat V.P) (σ.vec V.w) (σ.sc V.e))
      (fun σ' => (match apCall Q (σ.vec V.a0) (σ.sc V.r) (σ.sc V.R) (σ.mat V.P) (σ.vec V.w) (σ.sc V.e) with
        | none => σ'.sc V.ok = 0
        | some x => σ'.sc V.ok = 1 ∧ σ'.vec V.out = x) ∧
        KP Iq nsQ ssQ asQ (apN V) (apS V) (apA V) σ σ') := by
  layout_facts
  unfold apCode
  by_cases h : d = 1
  · subst h
    have hk : kAP 1 Kq (σ.sc V.r) (σ.sc V.R) (σ.mat V.P) (σ.vec V.w) (σ.sc V.e) =
        kOne Kq (oneCnt (σ.sc V.R) (σ.arr V.P 0) (σ.arr V.w 0) (σ.sc V.e)) + 2 := by
      unfold kAP; rw [dif_pos rfl]; rfl
    have ha : apCall Q (σ.vec V.a0) (σ.sc V.r) (σ.sc V.R) (σ.mat V.P) (σ.vec V.w) (σ.sc V.e) =
        (ellOne {x | (fun _ => x) ∈ Q} (σ.arr V.a0 0) (σ.sc V.r) (σ.sc V.R) (σ.arr V.P 0) (σ.arr V.w 0)
          (σ.sc V.e)).map (fun x _ => x) := by
      unfold apCall; rw [dif_pos rfl]; rfl
    rw [hk, ha]
    refine runs_ifN_f (by lay) (by lay) (by rw [h1, hd]; exact lt_irrefl 1) ?_
    exact runs_mono (runs_ellOneCode hp hmem hIq rfl σ hd h1 hI) le_rfl
      (fun σ' h' => ⟨(apOut_iff _ _).1 h'.1, h'.2⟩)
  · have hk : kAP d Kq (σ.sc V.r) (σ.sc V.R) (σ.mat V.P) (σ.vec V.w) (σ.sc V.e) =
        kCap d Kq (ellConsts (σ.sc V.r) (σ.sc V.R) (σ.mat V.P) (σ.vec V.w) (σ.sc V.e)).N
          (ellConsts (σ.sc V.r) (σ.sc V.R) (σ.mat V.P) (σ.vec V.w) (σ.sc V.e)).J
          (ellConsts (σ.sc V.r) (σ.sc V.R) (σ.mat V.P) (σ.vec V.w) (σ.sc V.e)).B + 1 := by
      unfold kAP; rw [dif_neg h]
    have ha : apCall Q (σ.vec V.a0) (σ.sc V.r) (σ.sc V.R) (σ.mat V.P) (σ.vec V.w) (σ.sc V.e) =
        ellCap Q (σ.vec V.a0) (σ.sc V.r) (σ.sc V.R) (σ.mat V.P) (σ.vec V.w) (σ.sc V.e) := by
      unfold apCall; rw [dif_neg h]
    rw [hk, ha]
    refine runs_ifN_t (by lay) (by lay) (by rw [h1, hd]; omega) ?_
    exact runs_mono (runs_ellCapCode hp hmem hIq σ hd h1 hI h0 rfl) le_rfl
      (fun σ' h' => ⟨(apOut_iff _ _).1 h'.1, h'.2⟩)

/-! ## The polynomial bound -/

theorem kCap_mono {d Kq N J B N' J' B' : ℕ} (hN : N ≤ N') (hJ : J ≤ J') (hB : B ≤ B') :
    kCap d Kq N J B ≤ kCap d Kq N' J' B' := by
  unfold kCap kCons kES kESq kSC kST kLC kLF kLB kLH kTail kPL kPT kML kMT kEV kGV
  gcongr

theorem oNorm_fin_one (v : Fin 1 → ℝ) : oNorm v = |v 0| := by
  simp [oNorm, dotProduct, Real.sqrt_mul_self_eq_abs]

theorem kAP_le {Kq : ℕ} {r R e rb Rb T W eb : ℝ} {P : Matrix (Fin d) (Fin d) ℝ} {w : Fin d → ℝ} (hrb : 0 < rb)
    (hr : rb ≤ r) (hrR : r ≤ R) (hR : R ≤ Rb) (heb : 0 < eb) (he : eb ≤ e) (hT0 : 0 ≤ P.trace) (hT : P.trace ≤ T)
    (hW : oNorm w ≤ W) : kAP d Kq r R P w e ≤ kAPcap d Kq rb Rb T W eb := by
  unfold kAP kAPcap
  by_cases h : d = 1
  · subst h
    rw [dif_pos rfl, if_pos rfl]
    have htr : P.trace = P 0 0 := Matrix.trace_fin_one P
    refine Nat.add_le_add_right (kOne_mono (one_cnt_le (by linarith) hR (htr ▸ hT0) (htr ▸ hT) ?_ heb he)) 2
    exact (show |w 0| ≤ W by rw [← oNorm_fin_one]; exact hW)
  · rw [dif_neg h, if_neg h]
    have hJ := ellConsts_J_le hrb hr hrR hR heb he hT0 hT hW
    exact Nat.add_le_add_right (kCap_mono (ellConsts_N_le hrb hr hrR hR heb he hT0 hT hW) hJ
      (bBar_of_J hJ (ellConsts_B_le_J hrb hr hrR hR heb he hT0 hT hW))) 1

end AdversarialBco.Poly.AP
