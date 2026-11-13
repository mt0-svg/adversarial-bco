/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XBLEnd

@[expose] public section

/-!
# The two ends of a round of BL: the invariant with a new state

`BLInv.setSt`: from `BLInv` in mode `run` with the state `st`, a change of BL's cells within the frame of the two ends
(`SEnd`, `NEnd`, `AEnd`) that keeps the coins read, writes the state `st'` (`StRep`) and leaves every persistent cell
unchanged or a new integer at most `2^E` ends in `BLInv` in mode `run` with `st'`, at the same round.
-/

namespace AdversarialBco.Bit.Transfer.BLM

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.BLP Matrix

variable {d : ℕ}

/-- **BL's invariant with a new state.** -/
theorem BLInv.setSt {L : Layout} {n m K0 E : ℕ} {cfg : Cfg d} {st st' : St d} {t : ℕ} {σ σ' : Env d}
    (h : BLInv L n m K0 E cfg (.run st) t σ) (hF : FrameA SEnd NEnd AEnd σ σ') (hd : σ'.draws = σ.draws)
    (hst : StRep σ' cfg.par.p st')
    (hbS : ∀ y < nSP, σ'.sc y = σ.sc y ∨ ∃ z : ℤ, σ'.sc y = z ∧ |z| ≤ 2 ^ E)
    (hbA : ∀ a < nAP, ∀ k < asz d, σ'.arr a k = σ.arr a k ∨ ∃ z : ℤ, σ'.arr a k = z ∧ |z| ≤ 2 ^ E) :
    BLInv L n m K0 E cfg (.run st') t σ' := by
  have hN : ∀ j < 8, σ'.nat j = σ.nat j := fun j hj => hF.1 j fun h' => by simp only [NEnd] at h'; omega
  have hS : ∀ y < nSP, y ≠ sFirst → y ≠ sDmu → y ≠ sK → y ≠ sL → σ'.sc y = σ.sc y := fun y hy h1 h2 h3 h4 =>
    hF.2.1 y fun h' => by simp only [SEnd] at h'; omega
  have hA : ∀ a < aMu, ∀ k, σ'.arr a k = σ.arr a k := fun a ha k =>
    hF.2.2.1 a k fun h' => by simp only [AEnd] at h'; omega
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7⟩ := h.regs
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8⟩ := h.consts
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10⟩ := h.par
  obtain ⟨DS, hDS, hDS', hmu, hAS⟩ := h.pos
  obtain ⟨Dc, hDc, hDc', hc⟩ := h.ctr
  have hmo : σ.sc sMode = 2 := h.mode.1
  refine ⟨h.lay, ?_, ?_, ?_, ⟨DS, hDS, by rw [hS _ (by decide) (by decide) (by decide) (by decide) (by decide), hDS'],
    fun j => by rw [hA _ (by decide)]; exact hmu j, fun i j => by rw [hA _ (by decide)]; exact hAS i j⟩,
    ⟨Dc, hDc, by rw [hA _ (by decide), hDc'], fun j => by rw [hA _ (by decide)]; exact hc j⟩,
    ⟨by rw [hS _ (by decide) (by decide) (by decide) (by decide) (by decide), hmo], hst⟩,
    by rw [hF.2.2.2.1, h.rounds], by rw [hd, h.draws], ⟨fun y hy => ?_, fun a ha k hk => ?_⟩⟩
  · exact ⟨by rw [hN _ (by decide), r0], by rw [hN _ (by decide), r1], by rw [hN _ (by decide), r2],
      by rw [hN _ (by decide), r3], by rw [hN _ (by decide), r4], by rw [hN _ (by decide), r5],
      by rw [hN _ (by decide), r6], by rw [hN _ (by decide), r7]⟩
  · exact ⟨by rw [hS _ (by decide) (by decide) (by decide) (by decide) (by decide), c0],
      by rw [hS _ (by decide) (by decide) (by decide) (by decide) (by decide), c1],
      by rw [hS _ (by decide) (by decide) (by decide) (by decide) (by decide), c2],
      by rw [hS _ (by decide) (by decide) (by decide) (by decide) (by decide), c3],
      by rw [hS _ (by decide) (by decide) (by decide) (by decide) (by decide), c4],
      by rw [hS _ (by decide) (by decide) (by decide) (by decide) (by decide), c5],
      by rw [hS _ (by decide) (by decide) (by decide) (by decide) (by decide), c6],
      by rw [hS _ (by decide) (by decide) (by decide) (by decide) (by decide), c7],
      by rw [hS _ (by decide) (by decide) (by decide) (by decide) (by decide), c8]⟩
  · exact ⟨by rw [hS _ (by decide) (by decide) (by decide) (by decide) (by decide), p0],
      by rw [hS _ (by decide) (by decide) (by decide) (by decide) (by decide), p1],
      by rw [hS _ (by decide) (by decide) (by decide) (by decide) (by decide), p2],
      by rw [hS _ (by decide) (by decide) (by decide) (by decide) (by decide), p3],
      by rw [hS _ (by decide) (by decide) (by decide) (by decide) (by decide), p4],
      by rw [hS _ (by decide) (by decide) (by decide) (by decide) (by decide), p5],
      by rw [hS _ (by decide) (by decide) (by decide) (by decide) (by decide), p6],
      by rw [hS _ (by decide) (by decide) (by decide) (by decide) (by decide), p7],
      by rw [hS _ (by decide) (by decide) (by decide) (by decide) (by decide), p8],
      by rw [hS _ (by decide) (by decide) (by decide) (by decide) (by decide), p9],
      by rw [hS _ (by decide) (by decide) (by decide) (by decide) (by decide), p10]⟩
  · rcases hbS y hy with e | e
    · rw [e]; exact h.bnd.1 y hy
    · exact e
  · rcases hbA a ha k hk with e | e
    · rw [e]; exact h.bnd.2 a ha k hk
    · exact e

end AdversarialBco.Bit.Transfer.BLM
