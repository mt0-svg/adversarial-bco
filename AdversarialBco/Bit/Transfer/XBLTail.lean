/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XBLEnd
public import AdversarialBco.Bit.Transfer.XBLCall
public import AdversarialBco.Bit.Transfer.XBLSplit
public import AdversarialBco.Bit.Transfer.XBLR3

@[expose] public section

/-!
# The ends of BL's round in mode `run`

The specification of R15 COMMIT as a named proposition (`ComSpec`, the body of `CommitBL`), the frame of the two
data commands (`SDat`, `NDat`, `ADat`), the post of a tail (`RPost`), the guard `xG` (`sMode := 1`, from `BLInv` in
mode `run` to `BLInv` in mode `guard`), and the invariant moved to another round, a frame or a larger bound
(`BLInv.ofPers`, `BLInv.frame`, `BLInv.mono`).
-/

namespace AdversarialBco.Bit.Transfer.BLM

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.BLP AdversarialBco.Bit.RQ Matrix

variable {d : ℕ}

/-! ## The specifications -/

/-- The body of `CommitBL`. -/
def ComSpec (xcom : Layout → XCmd) (C k : ℕ) : Prop :=
  ∀ (d : ℕ) (L : Layout) (X : XCtx d) (ℓa ℓ n m K0 E t : ℕ) (cfg : Cfg d) (st : St d)
    (Ap Bp : Matrix (Fin d) (Fin d) ℚ) (bp Gp : Fin d → ℚ) (kp lp : ℚ) (x : Fin d → ℤ) (e : ℕ) (σ : Env d),
    1 ≤ d → LayOK L d ℓa → BLLay L → BLInv L n m K0 E cfg (.run st) t σ →
    (∀ i j : Fin d, σ.arr 26 (d * i + j) = qn cfg.par.p (Ap i j) ∧ OnG cfg.par.p (Ap i j) ∧
      |qn cfg.par.p (Ap i j)| ≤ 2 ^ E) →
    (∀ i j : Fin d, σ.arr 27 (d * i + j) = qn cfg.par.p (Bp i j) ∧ OnG cfg.par.p (Bp i j) ∧
      |qn cfg.par.p (Bp i j)| ≤ 2 ^ E) →
    (∀ j : Fin d, σ.arr 28 j = qn cfg.par.p (bp j) ∧ OnG cfg.par.p (bp j) ∧ |qn cfg.par.p (bp j)| ≤ 2 ^ E) →
    (∀ j : Fin d, σ.arr 29 j = qn cfg.par.p (Gp j) ∧ OnG cfg.par.p (Gp j) ∧ |qn cfg.par.p (Gp j)| ≤ 2 ^ E) →
    σ.sc 59 = qn cfg.par.p kp → OnG cfg.par.p kp → |qn cfg.par.p kp| ≤ 2 ^ E →
    σ.sc 63 = qn cfg.par.p lp → OnG cfg.par.p lp → |qn cfg.par.p lp| ≤ 2 ^ E →
    EllOut blkBL (some x) e σ → (∀ j, |x j| ≤ 2 ^ E) → e ≤ E →
    C * (d + E + 1) ^ k ≤ ℓ → C * (d + E + 1) ^ k < 2 ^ ℓa →
    XRunsB L X ℓa ℓ (xcom L) σ (C * (d + E + 1) ^ k) (fun σ' =>
      BLInv L n m K0 E cfg (.run ⟨false, fun j => (x j : ℚ) / 2 ^ e, Ap, Bp, bp, kp, Gp, lp⟩) t σ' ∧
      σ'.draws = σ.draws ∧ FrameA SEnd NEnd AEnd σ σ')

/-- The frame of the two data commands. -/
def SDat (y : ℕ) : Prop := (sPl ≤ y ∧ y < sPl + 6) ∨ 256 ≤ y
def NDat (j : ℕ) : Prop := 19 ≤ j ∧ j < 32
def ADat (a _k : ℕ) : Prop := (aPHn ≤ a ∧ a ≤ aPfd) ∨ a = 30

/-! ## The invariant -/

/-- The post of a tail: BL's invariant with the mode `mo` at the round `t`, the points `P0`. -/
def RPost (L : Layout) (n m K0 E : ℕ) (cfg : Cfg d) (mo : Mode d) (t : ℕ) (P0 : ℕ → EuclideanSpace ℝ (Fin d))
    (σ : Env d) : Prop :=
  BLInv L n m K0 E cfg mo t σ ∧ σ.pts = P0

/-- The invariant moves to the round `t'` when the persistent cells are unchanged, `t'` rounds were played and the
coins of the rounds `< t'` read. -/
theorem BLInv.ofPers {L : Layout} {n m K0 E : ℕ} {cfg : Cfg d} {mo : Mode d} {t t' : ℕ} {σ σ' : Env d}
    (h : BLInv L n m K0 E cfg mo t σ) (hs : SamePers σ σ') (hr : σ'.rounds = t')
    (hd : σ'.draws = Sched.blkStart d K0 cfg.par.B t' 0) : BLInv L n m K0 E cfg mo t' σ' := by
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

/-- The invariant within a frame that avoids the persistent cells and keeps the coins read. -/
theorem BLInv.frame {L : Layout} {n m K0 E : ℕ} {cfg : Cfg d} {mo : Mode d} {t : ℕ} {σ σ' : Env d}
    {S N : ℕ → Prop} {Ar : ℕ → ℕ → Prop} (h : BLInv L n m K0 E cfg mo t σ) (hF : FrameA S N Ar σ σ')
    (hS : ∀ y, S y → nSP ≤ y) (hN : ∀ j, N j → 8 ≤ j) (hA : ∀ a k, Ar a k → nAP ≤ a) (hd : σ'.draws = σ.draws) :
    BLInv L n m K0 E cfg mo t σ' :=
  h.ofPers (SamePers.ofFrame hF hS hN hA) (by rw [hF.2.2.2.1, h.rounds]) (by rw [hd, h.draws])

/-- A larger bound. -/
theorem BLInv.mono {L : Layout} {n m K0 E E' : ℕ} {cfg : Cfg d} {mo : Mode d} {t : ℕ} {σ : Env d}
    (h : BLInv L n m K0 E cfg mo t σ) (hE : E ≤ E') : BLInv L n m K0 E' cfg mo t σ := by
  have hp : (2 : ℤ) ^ E ≤ 2 ^ E' := pow_le_pow_right₀ (by norm_num) hE
  refine { h with bnd := ⟨fun y hy => ?_, fun a ha k hk => ?_⟩ }
  · obtain ⟨z, hz, bz⟩ := h.bnd.1 y hy
    exact ⟨z, hz, bz.trans hp⟩
  · obtain ⟨z, hz, bz⟩ := h.bnd.2 a ha k hk
    exact ⟨z, hz, bz.trans hp⟩

/-! ## The guard -/

/-- BL's guard: `sMode := 1`. -/
def xG (L : Layout) : XCmd := toX (VL.sconst L sMode 1)

/-- **The guard** from mode `run`. -/
theorem BLInv.toGuard {L : Layout} {n m K0 E : ℕ} {cfg : Cfg d} {st : St d} {t : ℕ} {σ : Env d}
    (h : BLInv L n m K0 E cfg (.run st) t σ) : BLInv L n m K0 E cfg .guard t (σ.setSc sMode ((1 : ℚ) : ℝ)) := by
  have e : ∀ y, y ≠ sMode → (σ.setSc sMode ((1 : ℚ) : ℝ)).sc y = σ.sc y := fun y hy => by simp [hy]
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8⟩ := h.consts
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10⟩ := h.par
  obtain ⟨DS, hDS, hDS', hmu, hAS⟩ := h.pos
  refine ⟨h.lay, h.regs, ⟨by rw [e _ (by decide), c0], by rw [e _ (by decide), c1], by rw [e _ (by decide), c2],
      by rw [e _ (by decide), c3], by rw [e _ (by decide), c4], by rw [e _ (by decide), c5],
      by rw [e _ (by decide), c6], by rw [e _ (by decide), c7], by rw [e _ (by decide), c8]⟩,
    ⟨by rw [e _ (by decide), p0], by rw [e _ (by decide), p1], by rw [e _ (by decide), p2],
      by rw [e _ (by decide), p3], by rw [e _ (by decide), p4], by rw [e _ (by decide), p5],
      by rw [e _ (by decide), p6], by rw [e _ (by decide), p7], by rw [e _ (by decide), p8],
      by rw [e _ (by decide), p9], by rw [e _ (by decide), p10]⟩,
    ⟨DS, hDS, by rw [e _ (by decide), hDS'], hmu, hAS⟩, h.ctr, by simp [ModeRep], h.rounds, h.draws,
    ⟨fun y hy => ?_, fun a ha k hk => h.bnd.2 a ha k hk⟩⟩
  by_cases hy' : y = sMode
  · subst hy'
    exact ⟨1, by simp, by rw [abs_one]; exact one_le_pow₀ (by norm_num)⟩
  · rw [e y hy']; exact h.bnd.1 y hy

/-- Small constants fit. -/
theorem abs_small_lt {ℓ : ℕ} (hℓ : 1 ≤ ℓ) {v : ℤ} (hv : 0 ≤ v ∧ v ≤ 1) : |((v : ℤ) : ℝ)| < 2 ^ ℓ := by
  have h2 : (2 : ℝ) ≤ 2 ^ ℓ := by
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ ℓ := pow_le_pow_right₀ (by norm_num) hℓ
  have : |((v : ℤ) : ℝ)| ≤ 1 := by
    rw [abs_le]; exact ⟨by exact_mod_cast (by omega : (-1 : ℤ) ≤ v), by exact_mod_cast hv.2⟩
  linarith

end AdversarialBco.Bit.Transfer.BLM
