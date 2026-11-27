/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XBLR2q

@[expose] public section

/-!
# BL's round on the machine, R3 PLAY: the play leaf and the persistent cells

The play leaf reads a point in the form of the play leaf (`ptE`); `ptE_eq` reads it as BL's rational point.
`SamePers`: the persistent cells are unchanged (`SamePers.trans`, `SamePers.ofFrame`, `samePers_setSc`,
`samePers_play`); `BLInv.next` carries the invariant to the next round when the persistent cells are unchanged.
-/

namespace AdversarialBco.Bit.Transfer.BLM

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.BLP Matrix
open AdversarialBco.BitRAM (toE)

variable {d : ℕ}

/-! ## The play leaf -/

theorem ptE_eq {σ : Env d} {v : ℕ} {D : ℤ} {u : Fin d → ℤ} {q : Fin d → ℚ} (h0 : σ.arr v 0 = (D : ℝ))
    (hu : ∀ j : Fin d, σ.arr v (1 + j) = (u j : ℝ)) (hq : ∀ j, (u j : ℚ) / D = q j) : ptE σ v = toE q := by
  unfold ptE toE
  congr 1
  funext j
  rw [hu j, h0, ← hq j]
  push_cast
  rfl

theorem ptE_of_rep {σ : Env d} {v : ℕ} {c : Fin d → ℚ} (h : PtRep σ v c) : ptE σ v = toE c := by
  obtain ⟨D, -, h0, hj⟩ := h
  choose u hu hq using hj
  exact ptE_eq h0 (fun j => by rw [add_comm]; exact hu j) hq

/-! ## The invariant at the next round -/

/-- The persistent cells of `σ'` are those of `σ`. -/
def SamePers (σ σ' : Env d) : Prop :=
  (∀ j < 8, σ'.nat j = σ.nat j) ∧ (∀ y < nSP, σ'.sc y = σ.sc y) ∧ ∀ a < nAP, ∀ k, σ'.arr a k = σ.arr a k

theorem modeRep_pers {σ σ' : Env d} {p : ℕ} {mo : Mode d} (hs : SamePers σ σ') (h : ModeRep σ p mo) :
    ModeRep σ' p mo := by
  obtain ⟨-, hS, hA⟩ := hs
  have e : ∀ y < nSP, σ'.sc y = σ.sc y := hS
  cases mo with
  | off => simp only [ModeRep] at h ⊢; rw [e _ (by decide), h]
  | guard => simp only [ModeRep] at h ⊢; rw [e _ (by decide), h]
  | run st =>
    obtain ⟨h0, h1, ⟨Dm, hDm, hDm', hmu⟩, h3, h4, h5, h6, h7, h8⟩ := h
    refine ⟨by rw [e _ (by decide), h0], by rw [e _ (by decide), h1], ⟨Dm, hDm, by rw [e _ (by decide), hDm'],
      fun j => by rw [hA _ (by decide)]; exact hmu j⟩, fun i j => by rw [hA _ (by decide)]; exact h3 i j,
      fun i j => by rw [hA _ (by decide)]; exact h4 i j, fun j => by rw [hA _ (by decide)]; exact h5 j,
      by rw [e _ (by decide)]; exact h6, fun j => by rw [hA _ (by decide)]; exact h7 j,
      by rw [e _ (by decide)]; exact h8⟩

/-- The invariant passes to the next round when the persistent cells are unchanged, one round was played and the
coins of the round were read. -/
theorem BLInv.next {L : Layout} {n m K0 E : ℕ} {cfg : Cfg d} {mo : Mode d} {t : ℕ} {σ σ' : Env d}
    (h : BLInv L n m K0 E cfg mo t σ) (hs : SamePers σ σ') (hr : σ'.rounds = t + 1)
    (hd : σ'.draws = Sched.blkStart d K0 cfg.par.B (t + 1) 0) : BLInv L n m K0 E cfg mo (t + 1) σ' := by
  obtain ⟨hN, hS, hA⟩ := hs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7⟩ := h.regs
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8⟩ := h.consts
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10⟩ := h.par
  obtain ⟨DS, hDS, hDS', hmu, hAS⟩ := h.pos
  obtain ⟨Dc, hDc, hDc', hc⟩ := h.ctr
  refine ⟨h.lay, ?_, ?_, ?_, ⟨DS, hDS, by rw [hS _ (by decide), hDS'], fun j => by rw [hA _ (by decide)]; exact hmu j,
    fun i j => by rw [hA _ (by decide)]; exact hAS i j⟩, ⟨Dc, hDc, by rw [hA _ (by decide), hDc'],
    fun j => by rw [hA _ (by decide)]; exact hc j⟩, modeRep_pers ⟨hN, hS, hA⟩ h.mode, hr, hd,
    ⟨fun y hy => by rw [hS y hy]; exact h.bnd.1 y hy, fun a ha k hk => by rw [hA a ha]; exact h.bnd.2 a ha k hk⟩⟩
  · exact ⟨by rw [hN _ (by decide), r0], by rw [hN _ (by decide), r1], by rw [hN _ (by decide), r2],
      by rw [hN _ (by decide), r3], by rw [hN _ (by decide), r4], by rw [hN _ (by decide), r5],
      by rw [hN _ (by decide), r6], by rw [hN _ (by decide), r7]⟩
  · exact ⟨by rw [hS _ (by decide), c0], by rw [hS _ (by decide), c1], by rw [hS _ (by decide), c2],
      by rw [hS _ (by decide), c3], by rw [hS _ (by decide), c4], by rw [hS _ (by decide), c5],
      by rw [hS _ (by decide), c6], by rw [hS _ (by decide), c7], by rw [hS _ (by decide), c8]⟩
  · exact ⟨by rw [hS _ (by decide), p0], by rw [hS _ (by decide), p1], by rw [hS _ (by decide), p2],
      by rw [hS _ (by decide), p3], by rw [hS _ (by decide), p4], by rw [hS _ (by decide), p5],
      by rw [hS _ (by decide), p6], by rw [hS _ (by decide), p7], by rw [hS _ (by decide), p8],
      by rw [hS _ (by decide), p9], by rw [hS _ (by decide), p10]⟩

theorem SamePers.trans {σ σ' σ'' : Env d} (h : SamePers σ σ') (h' : SamePers σ' σ'') : SamePers σ σ'' :=
  ⟨fun j hj => (h'.1 j hj).trans (h.1 j hj), fun y hy => (h'.2.1 y hy).trans (h.2.1 y hy),
    fun a ha k => (h'.2.2 a ha k).trans (h.2.2 a ha k)⟩

/-- A frame whose cells avoid the persistent ones keeps them. -/
theorem SamePers.ofFrame {S N : ℕ → Prop} {Ar : ℕ → ℕ → Prop} {σ σ' : Env d} (h : FrameA S N Ar σ σ')
    (hS : ∀ y, S y → nSP ≤ y) (hN : ∀ j, N j → 8 ≤ j) (hA : ∀ a k, Ar a k → nAP ≤ a) : SamePers σ σ' :=
  ⟨fun j hj => h.1 j fun h' => by have := hN j h'; omega, fun y hy => h.2.1 y fun h' => by have := hS y h'; omega,
    fun a ha k => h.2.2.1 a k fun h' => by have := hA a k h'; omega⟩

/-! ## The round in the modes `off` and `guard` -/

theorem samePers_setSc {σ : Env d} {y : ℕ} (hy : nSP ≤ y) (v : ℝ) : SamePers σ (σ.setSc y v) :=
  SamePers.ofFrame ((FrameA.refl (fun z => z = y) (fun _ => False) (fun _ _ => False) σ).setSc rfl v)
    (fun _ h => h ▸ hy) (fun _ h => h.elim) (fun _ _ h => h.elim)

theorem samePers_play {σ : Env d} (r : ℕ) (p : ℕ → E d) : SamePers σ { σ with rounds := r, pts := p } :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl⟩

end AdversarialBco.Bit.Transfer.BLM
