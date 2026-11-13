/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XBLEnd
public import AdversarialBco.Bit.Transfer.XBLData
public import AdversarialBco.Bit.Transfer.XBLSplit
public import AdversarialBco.Bit.Transfer.XBLR3

@[expose] public section

/-!
# The ends of BL's round in mode `run`

The specifications of the separated pieces as named propositions (`ComSpec`, `FireSpec`, `DTSpec`, `DLSpec`,
`CallSpec`: the bodies of `CommitBL`, `FireBL`, `DataT`, `DataL`, `CallBL`), the guard `xG` (`sMode := 1`, from
`BLInv` in mode `run` to `BLInv` in mode `guard`), the invariant moved to another round or a larger bound
(`BLInv.ofPers`, `BLInv.mono`), and the last tail of the round: R15 COMMIT behind the test of the routine's flag
(`XV.tCom`).
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

/-- The body of `FireBL`. -/
def FireSpec (xfire : Layout → XCmd) (C k : ℕ) : Prop :=
  ∀ (d : ℕ) (L : Layout) (X : XCtx d) (ℓa ℓ n m K0 E t : ℕ) (cfg : Cfg d) (st : St d) (σ : Env d),
    1 ≤ d → 1 ≤ n → cfg.par = par d n → LayOK L d ℓa → BLLay L → BLInv L n m K0 E cfg (.run st) t σ →
    C * (d + E + 1) ^ k ≤ ℓ → C * (d + E + 1) ^ k < 2 ^ ℓa →
    XRunsB L X ℓa ℓ (xfire L) σ (C * (d + E + 1) ^ k) (fun σ' =>
      BLInv L n m K0 E cfg (.run (init cfg.par d)) t σ' ∧ σ'.draws = σ.draws ∧ FrameA SEnd NEnd AEnd σ σ')


/-- The body of `DataT`. -/
def DTSpec (xdt : Layout → XCmd) (C k : ℕ) : Prop :=
  ∀ (d : ℕ) (L : Layout) (X : XCtx d) (ℓa ℓ n m K0 E t : ℕ) (cfg : Cfg d) (st : St d)
    (Bp : Matrix (Fin d) (Fin d) ℚ) (bp Gp : Fin d → ℚ) (σ : Env d),
    1 ≤ d → 1 ≤ n → cfg.par = par d n → LayOK L d ℓa → BLLay L → BLInv L n m K0 E cfg (.run st) t σ →
    (∀ i j : Fin d, σ.arr 27 (d * i + j) = qn cfg.par.p (Bp i j) ∧ OnG cfg.par.p (Bp i j) ∧
      |qn cfg.par.p (Bp i j)| ≤ 2 ^ E) →
    (∀ j : Fin d, σ.arr 28 j = qn cfg.par.p (bp j) ∧ OnG cfg.par.p (bp j) ∧ |qn cfg.par.p (bp j)| ≤ 2 ^ E) →
    (∀ j : Fin d, σ.arr 29 j = qn cfg.par.p (Gp j) ∧ OnG cfg.par.p (Gp j) ∧ |qn cfg.par.p (Gp j)| ≤ 2 ^ E) →
    C * (d + E + 1) ^ k ≤ ℓ → C * (d + E + 1) ^ k < 2 ^ ℓa →
    XRunsB L X ℓa ℓ (xdt L) σ (C * (d + E + 1) ^ k) (fun σ' =>
      PrepIn σ' cfg (C * (d + E + 1) ^ k) (if st.first then 0 else st.B * st.Bᵀ) (if st.first then 0 else st.b)
        (if st.first then 0 else LT cfg.par - st.k) (if st.first then 1 - cfg.par.eps else BLP.rB cfg.par / 2)
        (Bp * Bpᵀ) (bp - (cfg.par.eta / 2) • Gp)
        (if st.first then (1 - cfg.par.eps) ^ 2 / (cfg.par.Ne * d * 8)
          else BLP.rB cfg.par ^ 2 / (cfg.par.Ne * d * 8)) ∧
      σ'.draws = σ.draws ∧
      FrameA (fun y => (sPl ≤ y ∧ y < sPl + 6) ∨ 256 ≤ y) (fun j => 19 ≤ j ∧ j < 32)
        (fun a _ => (aPHn ≤ a ∧ a ≤ aPfd) ∨ a = 30) σ σ')

/-- The body of `DataL`. -/
def DLSpec (xdl : Layout → XCmd) (C k : ℕ) : Prop :=
  ∀ (d : ℕ) (L : Layout) (X : XCtx d) (ℓa ℓ n m K0 E t : ℕ) (cfg : Cfg d) (st : St d)
    (Bp : Matrix (Fin d) (Fin d) ℚ) (bp : Fin d → ℚ) (kp : ℚ) (wh : Fin d → ℤ) (Dw : ℤ) (σ : Env d),
    1 ≤ d → 1 ≤ n → cfg.par = par d n → LayOK L d ℓa → BLLay L → BLInv L n m K0 E cfg (.run st) t σ →
    (∀ i j : Fin d, σ.arr 27 (d * i + j) = qn cfg.par.p (Bp i j) ∧ OnG cfg.par.p (Bp i j) ∧
      |qn cfg.par.p (Bp i j)| ≤ 2 ^ E) →
    (∀ j : Fin d, σ.arr 28 j = qn cfg.par.p (bp j) ∧ OnG cfg.par.p (bp j) ∧ |qn cfg.par.p (bp j)| ≤ 2 ^ E) →
    σ.sc 59 = qn cfg.par.p kp → OnG cfg.par.p kp → |qn cfg.par.p kp| ≤ 2 ^ E →
    0 < Dw → Dw ≤ 2 ^ E → σ.sc 91 = Dw → (∀ j : Fin d, σ.arr 31 j = wh j ∧ |wh j| ≤ 2 ^ E) →
    C * (d + E + 1) ^ k ≤ ℓ → C * (d + E + 1) ^ k < 2 ^ ℓa →
    XRunsB L X ℓa ℓ (xdl L) σ (C * (d + E + 1) ^ k) (fun σ' =>
      PrepIn σ' cfg (C * (d + E + 1) ^ k) (Bp * Bpᵀ) bp (Lmu cfg.par - kp) (BLP.rB cfg.par / 2) (Bp * Bpᵀ)
        ((Bp * Bpᵀ) *ᵥ fun j => (wh j : ℚ) / Dw) (eBL cfg.par d n) ∧
      σ'.draws = σ.draws ∧
      FrameA (fun y => (sPl ≤ y ∧ y < sPl + 6) ∨ 256 ≤ y) (fun j => 19 ≤ j ∧ j < 32)
        (fun a _ => (aPHn ≤ a ∧ a ≤ aPfd) ∨ a = 30) σ σ')

/-- The body of `CallBL`. -/
def CallSpec (xcall : Layout → XCmd) (C k nS nN nA : ℕ) : Prop :=
  ∀ (d : ℕ) (L : Layout) (w : BitRAM.World d) (n m M E ℓa ℓ s : ℕ) (A : Matrix (Fin m) (Fin d) ℚ)
    (b : Fin m → ℚ) (c : Fin d → ℚ) (S : (Fin d → ℚ) × Matrix (Fin d) (Fin d) ℚ) (H : Matrix (Fin d) (Fin d) ℚ)
    (g : Fin d → ℚ) (ℓq r : ℚ) (P : Matrix (Fin d) (Fin d) ℚ) (f : Fin d → ℚ) (e : ℚ) (σ : Env d),
    1 ≤ d → LayOK L d ℓa → blkBL.OK L nS nN nA → RealRAM.HeightLE A b M →
    OnG (par d n).pF (par d n).eps → 0 ≤ (par d n).eps → (par d n).eps ≤ 1 →
    RowCtx L m E (mkCfg d n m A b c S) σ → PrepIn σ (mkCfg d n m A b c S) s H g ℓq r P f e →
    C * (d + m + M.size + E + s + 1) ^ k ≤ ℓ → C * (d + m + M.size + E + s + 1) ^ k < 2 ^ ℓa →
    XRunsB L (ctxOf w n m A b) ℓa ℓ (xcall L) σ (C * (d + m + M.size + E + s + 1) ^ k) (fun σ' =>
      EllOut blkBL (ellRI (clearQ (callOf (mkCfg d n m A b c S) H g ℓq r P f e)))
        (ellExp (clearQ (callOf (mkCfg d n m A b c S) H g ℓq r P f e))) σ' ∧ σ'.draws = σ.draws ∧
      FrameA (fun y => oE ≤ y ∨ SPrep y) (fun j => rEE ≤ j ∨ NPrep j) (fun a _ => aWE ≤ a ∨ APrep a) σ σ')

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

/-- What the row command reads holds under BL's invariant. -/
theorem BLInv.rowCtx {L : Layout} {n m K0 E : ℕ} {cfg : Cfg d} {mo : Mode d} {t : ℕ} {σ : Env d}
    (h : BLInv L n m K0 E cfg mo t σ) (hlay : BLLay L) : RowCtx L m E cfg σ := by
  obtain ⟨r0, r1, r2, r3, -, r5, -⟩ := h.regs
  obtain ⟨c0, -, -, c3, -⟩ := h.consts
  obtain ⟨p0, -⟩ := h.par
  refine ⟨hlay, ⟨r0, r1, r2, r3, r5⟩, ⟨c0, c3, p0⟩, h.pos, ⟨fun y hy => ?_, fun a ha k hk => ?_⟩⟩
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hy
    exact h.bnd.1 y (by rcases hy with rfl | rfl | rfl <;> decide)
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at ha
    exact h.bnd.2 a (by rcases ha with rfl | rfl <;> decide) k hk

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

/-- **The guard on the machine.** -/
theorem XV.guard {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} (hL : LayOK L d ℓa) {n m K0 E : ℕ} {cfg : Cfg d}
    {st : St d} {t : ℕ} {σ : Env d} {P0 : ℕ → EuclideanSpace ℝ (Fin d)}
    (hI : BLInv L n m K0 E cfg (.run st) t σ) (hp : σ.pts = P0) (hℓ : 1 ≤ ℓ) :
    XRunsB L X ℓa ℓ (xG L) σ 1 (RPost L n m K0 E cfg .guard t P0) := by
  have hS := hI.lay.2.1
  refine XV.mono (XV.sconst hL (x := sMode) (by simp only [nS0, sMode] at hS ⊢; omega) (1 : ℚ) rfl
    (by rw [Rat.cast_one, abs_one]; exact one_lt_pow₀ (by norm_num) (by omega))) le_rfl fun σ' e => ?_
  subst e
  exact ⟨hI.toGuard, by simp [hp]⟩

/-- Small constants fit. -/
theorem abs_small_lt {ℓ : ℕ} (hℓ : 1 ≤ ℓ) {v : ℤ} (hv : 0 ≤ v ∧ v ≤ 1) : |((v : ℤ) : ℝ)| < 2 ^ ℓ := by
  have h2 : (2 : ℝ) ≤ 2 ^ ℓ := by
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ ℓ := pow_le_pow_right₀ (by norm_num) hℓ
  have : |((v : ℤ) : ℝ)| ≤ 1 := by
    rw [abs_le]; exact ⟨by exact_mod_cast (by omega : (-1 : ℤ) ≤ v), by exact_mod_cast hv.2⟩
  linarith

/-! ## R15 COMMIT behind the flag -/

/-- **R15 behind the routine's flag**: the flag `0` leaves for `guard`, the flag `1` commits the new state. -/
theorem XV.tCom {xcom : Layout → XCmd} {Cc kc : ℕ} (hcom : ComSpec xcom Cc kc) {L : Layout} {X : XCtx d}
    {ℓa ℓ n m K0 E t : ℕ} {cfg : Cfg d} {st : St d} {σ : Env d} {P0 : ℕ → EuclideanSpace ℝ (Fin d)}
    {Ap Bp : Matrix (Fin d) (Fin d) ℚ} {bp Gp : Fin d → ℚ} {kp lp : ℚ} {r : Option (Fin d → ℤ)} {e : ℕ}
    (hd1 : 1 ≤ d) (hL : LayOK L d ℓa) (hlay : BLLay L) (hI : BLInv L n m K0 E cfg (.run st) t σ)
    (hp : σ.pts = P0)
    (hA : ∀ i j : Fin d, σ.arr 26 (d * i + j) = qn cfg.par.p (Ap i j) ∧ OnG cfg.par.p (Ap i j) ∧
      |qn cfg.par.p (Ap i j)| ≤ 2 ^ E)
    (hB : ∀ i j : Fin d, σ.arr 27 (d * i + j) = qn cfg.par.p (Bp i j) ∧ OnG cfg.par.p (Bp i j) ∧
      |qn cfg.par.p (Bp i j)| ≤ 2 ^ E)
    (hb : ∀ j : Fin d, σ.arr 28 j = qn cfg.par.p (bp j) ∧ OnG cfg.par.p (bp j) ∧ |qn cfg.par.p (bp j)| ≤ 2 ^ E)
    (hG : ∀ j : Fin d, σ.arr 29 j = qn cfg.par.p (Gp j) ∧ OnG cfg.par.p (Gp j) ∧ |qn cfg.par.p (Gp j)| ≤ 2 ^ E)
    (hk : σ.sc 59 = qn cfg.par.p kp) (hkg : OnG cfg.par.p kp) (hkb : |qn cfg.par.p kp| ≤ 2 ^ E)
    (hl : σ.sc 63 = qn cfg.par.p lp) (hlg : OnG cfg.par.p lp) (hlb : |qn cfg.par.p lp| ≤ 2 ^ E)
    (hout : EllOut blkBL r e σ) (hx : ∀ x, r = some x → (∀ j, |x j| ≤ 2 ^ E) ∧ e ≤ E)
    (hT : Cc * (d + E + 1) ^ kc ≤ ℓ) (hTa : Cc * (d + E + 1) ^ kc < 2 ^ ℓa) (hℓ : 1 ≤ ℓ) :
    XRunsB L X ℓa ℓ (xifS L sZ oE (xcom L) (xG L)) σ (Cc * (d + E + 1) ^ kc + 3)
      (RPost L n m K0 E cfg (match r with
        | none => .guard
        | some x => .run ⟨false, fun j => (x j : ℚ) / 2 ^ e, Ap, Bp, bp, kp, Gp, lp⟩) t P0) := by
  have hz : σ.sc sZ = 0 := hI.consts.1
  have hS := hlay.1
  have h0 : |σ.sc sZ| < 2 ^ ℓ := by rw [hz]; exact_mod_cast abs_small_lt (v := 0) hℓ (by norm_num)
  cases r with
  | none =>
    have hf : σ.sc oE = 0 := hout
    exact XV.mono (XV.ifS_f hL (by simp only [oE, sZ] at hS ⊢; omega) (by simp only [oE] at hS ⊢; omega) h0
      (by rw [hf]; exact_mod_cast abs_small_lt (v := 0) hℓ (by norm_num)) (by rw [hz, hf]; exact lt_irrefl 0)
      (XV.guard hL hI hp hℓ)) (by omega) fun _ h => h
  | some x =>
    have hf : σ.sc oE = 1 := hout.1
    obtain ⟨bx, he⟩ := hx x rfl
    exact XV.mono (XV.ifS_t hL (by simp only [oE, sZ] at hS ⊢; omega) (by simp only [oE] at hS ⊢; omega) h0
      (by rw [hf]; exact_mod_cast abs_small_lt (v := 1) hℓ (by norm_num)) (by rw [hz, hf]; exact one_pos)
      (hcom d L X ℓa ℓ n m K0 E t cfg st Ap Bp bp Gp kp lp x e σ hd1 hL hlay hI hA hB hb hG hk hkg hkb
        hl hlg hlb hout bx he hT hTa)) (by omega) fun σ' ⟨hI', _, hF'⟩ => ⟨hI', by rw [hF'.2.2.2.2, hp]⟩

end AdversarialBco.Bit.Transfer.BLM
