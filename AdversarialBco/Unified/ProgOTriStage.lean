/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.ProgOTri
public import AdversarialBco.Bit.Transfer.XTriStage

@[expose] public section

/-!
# TRI-OGD-O on the oracle machine: one stage from the core step

`TriStageSpec` (Unified/ProgOTri.lean) for the stage `xstageO xstep`, from a named contract of the core step:

* **The constants of the core** (`TriKV`): the core's cells at the bases `oT`, `rT`, `aT` (`d` in `rD`, `d + 1`,
  `B_g`, `N' = 2^{n_e'}`, `d²` in registers, `0, 1, -1` and the constants of a draw `tzDCO d ℓ` in the slots
  `oT + 1, ..., oT + 13`, `2^{G_c'}` in `oT + 35`); the other constants of the block (those of SEP, of the gauge, of the
  stage test) form an abstract predicate `KX` whose cells lie outside the cells v2.1's pieces write (`KXStable`).
* **The core step** (`TriStepSpec xstep KX`): from the iterate `X̂` in `aT + 2`, `aT + 3` and the draw `Y` in `aT + 6`,
  `X̂ := tzUpd c X̂ (gvO .. j P ẑ) Y 2^{stEu + 1}`: the base point `ẑ`, its rounding to SEP's grid, SEP on the gauge of
  the stage test, the update; it keeps `KX` and writes only `stpS`, `stpN`, `stpA`.
* **The draws** (v2.1's `xdraw`, `XV.draw`, through `base`): BM-INT on the next `2 B_g d` coins into `aT + 6`.
* **The composition** (v2.1's `xstageC`, `XV.stageC`, through `base`): `pgComp` in integers (`tzComp`).
* `TriExpO`: polynomial bounds of the exponents and of the number of draws of a stage (a property of the constants).

The stage: the core of TRI-M with the step `xstep` (`xcoreO`), then `xstageC` (after `2^e := 1`, `2^j D := 0`, cells it
reads and this program does not use), then `2^{j+1} := 2^{j+2}` in `oT + 36`. `triStageSpec_of`: `TriStageSpec` for
`xstageO xstep` and the constants `TriKV ∧ KX`, from `TriStepSpec`, `TriExpO` and `KXStable`.
-/

namespace AdversarialBco.Unified.ProgO.TriO

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.Transfer AdversarialBco.Bit.Transfer.BLM
open AdversarialBco.Uni
open AdversarialBco.Unified.BLO AdversarialBco.Bit AdversarialBco.Bit.RQ AdversarialBco.Bit.TriM
open AdversarialBco.Unified.ProgO
open BitRAM BitRAMO

variable {d : ℕ}

/-! ## The constants of the core -/

/-- **The constants of the core** in the core's cells at the bases of the block. -/
structure TriKV (d n : ℕ) (δ r0 R0 : ℚ) (σ : Env d) : Prop where
  rd : σ.nat rD = d
  r1 : σ.nat (rT + 1) = d + 1
  rB : σ.nat (rT + 12) = triBgQ d
  rN : σ.nat (rT + 24) = 2 ^ triNeTQ d (ellO d n δ r0 R0)
  rdd : σ.nat (rT + 25) = d * d
  z : σ.sc (oT + 1) = 0
  o : σ.sc (oT + 2) = 1
  m : σ.sc (oT + 3) = -1
  pb : σ.sc (oT + 4) = (tzDCO d (ellO d n δ r0 R0)).PB
  p2 : σ.sc (oT + 5) = (tzDCO d (ellO d n δ r0 R0)).P2
  pg : σ.sc (oT + 6) = (tzDCO d (ellO d n δ r0 R0)).PG
  pj : σ.sc (oT + 7) = (tzDCO d (ellO d n δ r0 R0)).Pj
  r : σ.sc (oT + 8) = (tzDCO d (ellO d n δ r0 R0)).R
  mr : σ.sc (oT + 9) = -(tzDCO d (ellO d n δ r0 R0)).R
  al : σ.sc (oT + 10) = (tzDCO d (ellO d n δ r0 R0)).Al
  bh : σ.sc (oT + 11) = (tzDCO d (ellO d n δ r0 R0)).Bh
  mb : σ.sc (oT + 12) = ((-(tzDCO d (ellO d n δ r0 R0)).Bh : ℤ) : ℝ)
  d8 : σ.sc (oT + 13) = ((8 * (tzDCO d (ellO d n δ r0 R0)).dd : ℤ) : ℝ)
  gc : σ.sc (oT + 35) = ((2 ^ tGcT d (ellO d n δ r0 R0) : ℤ) : ℝ)

/-- The constants of the core survive every change that keeps their cells. -/
theorem TriKV.frame {n : ℕ} {δ r0 R0 : ℚ} {S N : ℕ → Prop} {Ar : ℕ → ℕ → Prop} {σ σ' : Env d}
    (h : TriKV d n δ r0 R0 σ) (hF : FrameA S N Ar σ σ')
    (hS : ∀ k, (1 ≤ k ∧ k < 14) ∨ k = 35 → ¬ S (oT + k))
    (hN : ¬ N rD ∧ ¬ N (rT + 1) ∧ ¬ N (rT + 12) ∧ ¬ N (rT + 24) ∧ ¬ N (rT + 25)) : TriKV d n δ r0 R0 σ' := by
  obtain ⟨n1, n2, n3, n4, n5⟩ := hN
  have s : ∀ k, (1 ≤ k ∧ k < 14) ∨ k = 35 → σ'.sc (oT + k) = σ.sc (oT + k) := fun k hk => hF.2.1 _ (hS k hk)
  exact ⟨(hF.1 _ n1).trans h.rd, (hF.1 _ n2).trans h.r1, (hF.1 _ n3).trans h.rB, (hF.1 _ n4).trans h.rN,
    (hF.1 _ n5).trans h.rdd, (s 1 (by omega)).trans h.z, (s 2 (by omega)).trans h.o, (s 3 (by omega)).trans h.m,
    (s 4 (by omega)).trans h.pb, (s 5 (by omega)).trans h.p2, (s 6 (by omega)).trans h.pg,
    (s 7 (by omega)).trans h.pj, (s 8 (by omega)).trans h.r, (s 9 (by omega)).trans h.mr,
    (s 10 (by omega)).trans h.al, (s 11 (by omega)).trans h.bh, (s 12 (by omega)).trans h.mb,
    (s 13 (by omega)).trans h.d8, (s 35 (by omega)).trans h.gc⟩

/-- The cells v2.1's pieces of a stage may write: the slots from `oT`, the registers `rT, ..., rT + 29`, the arrays
`aT, ..., aT + 15`. -/
def KXStable (KX : KPred) : Prop :=
  ∀ (d n : ℕ) (δ r0 R0 : ℚ) (a : Fin d → ℚ) (σ σ' : Env d), KX d n δ r0 R0 a σ →
    FrameA (fun y => oT ≤ y) (fun j => rT ≤ j ∧ j < rT + 30) (fun b _ => aT ≤ b ∧ b < aT + 16) σ σ' →
    KX d n δ r0 R0 a σ'

/-- The constants of the block: v2.1's and `KX`. -/
def KEv (KX : KPred) : KPred := fun d n δ r0 R0 a σ => TriKV d n δ r0 R0 σ ∧ KX d n δ r0 R0 a σ

theorem kCtr_of {KX : KPred} (hX : KXStable KX) : KCtr (KEv KX) := by
  intro d n δ r0 R0 a σ v ⟨h1, h2⟩
  refine ⟨h1.frame ((FrameA.refl (fun _ => False) (fun j => j = rT + 27) (fun _ _ => False) σ).setNat rfl v)
    (fun _ _ h => h) (by simp only [rD]; omega), hX _ _ _ _ _ _ σ _ h2 ?_⟩
  exact ((FrameA.refl (fun y => oT ≤ y) (fun j => rT ≤ j ∧ j < rT + 30) (fun b _ => aT ≤ b ∧ b < aT + 16) σ).setNat
    (by omega) v)

/-! ## The core step -/

/-- The slots the core step may write. -/
abbrev stpS (y : ℕ) : Prop := (oT + 16 ≤ y ∧ y < oT + 35) ∨ oT + 40 ≤ y

/-- The registers the core step may write. -/
abbrev stpN (j : ℕ) : Prop := (rT + 3 ≤ j ∧ j < rT + 11) ∨ (rT + 13 ≤ j ∧ j < rT + 24) ∨ rT + 30 ≤ j

/-- The array cells the core step may write. -/
abbrev stpA (b _k : ℕ) : Prop := (aT + 2 ≤ b ∧ b < aT + 4) ∨ aT + 6 ≤ b

/-- **The core step**: from the constants, the stage `j` at the position `P`, the iterate `X̂` (entries at most
`B_h`) in `aT + 2`, `aT + 3` and the draw `Y` (entries at most `2^{4p}`) in `aT + 6`, `xstep L` writes
`tzUpd c X̂ (gvO .. j P ẑ) Y 2^{stEu + 1}` into `aT + 2`, `aT + 3` (`ẑ = tzZ X̂ Y P_2`: the SEP field of the stage at
the base point), within `C (W + B + 1)^k` units; it keeps `KX` and the draws, and writes only `stpS`, `stpN`, `stpA`. -/
def TriStepSpec (xstep : Layout → XCmdO) (KX : KPred) (C k nS nN nA : ℕ) : Prop :=
  ∀ (d : ℕ) (L : Layout) (w : WorldO d) (n : ℕ) (δ r0 R0 : ℚ) (a : Fin d → ℚ) (ℓa ℓ : ℕ) (σ : Env d) (j B : ℕ)
    (P : StZ d) (X : PosZ d) (Y : Fin d → ℤ),
    InU d n δ r0 R0 → LayOK L d ℓa → RoomO L nS nN nA → TriKV d n δ r0 R0 σ → KX d n δ r0 R0 a σ →
    StAtO σ j P → StBnd P B → j < triMstQ r0 R0 → σ.nat rT = 1 →
    (∀ l : Fin d, σ.arr (aT + 2) l = X.1 l) → (∀ i l : Fin d, σ.arr (aT + 3) (d * i + l) = X.2 i l) →
    (∀ l : Fin d, σ.arr (aT + 6) l = Y l) →
    (∀ i, |X.1 i| ≤ (tzDCO d (ellO d n δ r0 R0)).Bh) → (∀ i l, |X.2 i l| ≤ (tzDCO d (ellO d n δ r0 R0)).Bh) →
    (∀ l, |Y l| ≤ 2 ^ (4 * tzP d)) →
    C * (WT d n δ r0 R0 a + B + 1) ^ k ≤ ℓ → C * (WT d n δ r0 R0 a + B + 1) ^ k < 2 ^ ℓa →
    XRunsBO L (ctxU w n δ r0 R0 a) ℓa ℓ (xstep L) σ (C * (WT d n δ r0 R0 a + B + 1) ^ k) (fun σ' =>
      (∀ l : Fin d, σ'.arr (aT + 2) l = (tzUpd (tzDCO d (ellO d n δ r0 R0)) X
        (gvO w.orc a r0 R0 (ellO d n δ r0 R0) j P (tzZ X Y (tzDCO d (ellO d n δ r0 R0)).P2)) Y (tBb d)).1 l) ∧
      (∀ i l : Fin d, σ'.arr (aT + 3) (d * i + l) = (tzUpd (tzDCO d (ellO d n δ r0 R0)) X
        (gvO w.orc a r0 R0 (ellO d n δ r0 R0) j P (tzZ X Y (tzDCO d (ellO d n δ r0 R0)).P2)) Y (tBb d)).2 i l) ∧
      KX d n δ r0 R0 a σ' ∧ σ'.draws = σ.draws ∧ FrameA stpS stpN stpA σ σ')

/-- **The exponents of TRI-OGD-O**: the grids, the box and a draw below `C (W + 1)^k`, and the number of draws of a
stage and the units of one BM-INT draw below `C (W + 1)^k`. -/
def TriExpO (C k : ℕ) : Prop :=
  ∀ (d n : ℕ) (δ r0 R0 : ℚ) (a : Fin d → ℚ), InU d n δ r0 R0 →
    triLa (triSQ d) + tGcT d (ellO d n δ r0 R0) + 4 * tzP d + d + 8 ≤ C * (WT d n δ r0 R0 a + 1) ^ k ∧
    2 ^ triNeTQ d (ellO d n δ r0 R0) ≤ C * (WT d n δ r0 R0 a + 1) ^ k ∧
    bmUnits (triBgQ d) ≤ C * (WT d n δ r0 R0 a + 1) ^ k

/-! ## The stage -/

/-- One draw of the core: `Ŝ += X̂`, the draw, the step. -/
def xcoreBodyO (xstep : Layout → XCmdO) (L : Layout) : XCmdO :=
  .seq (.base (xacc L (oT + 1) (oT + 40) (aT + 4) (aT + 2) (rT + 4) rT (rT + 5) rD rT))
  (.seq (.base (xacc L (oT + 1) (oT + 40) (aT + 5) (aT + 3) (rT + 4) rT (rT + 5) (rT + 25) rT))
  (.seq (.base (xdraw L (oT + 70) (rT + 12) (aT + 6) (rT + 7) rD rT)) (xstep L)))

/-- The core: `X̂ := (0, P_G I)`, `Ŝ := 0`, then `N'` draws (`N'` in `rT + 24`, the counter in `rT + 11`). -/
def xcoreO (xstep : Layout → XCmdO) (L : Layout) : XCmdO :=
  .seq (.base (xfill L (oT + 1) (oT + 40) (oT + 1) (aT + 2) (rT + 4) rT (rT + 5) rD rT))
  (.seq (.base (xscalI L (oT + 1) (oT + 40) (oT + 6) (aT + 3) (rT + 4) rT (rT + 1) (rT + 5) rD (rT + 25) rT))
  (.seq (.base (xfill L (oT + 1) (oT + 40) (oT + 1) (aT + 4) (rT + 4) rT (rT + 5) rD rT))
  (.seq (.base (xfill L (oT + 1) (oT + 40) (oT + 1) (aT + 5) (rT + 4) rT (rT + 5) (rT + 25) rT))
  (xforNO (rT + 11) (rT + 24) rT (xcoreBodyO xstep L)))))

/-- **One stage of TRI-OGD-O**: the core, then the composition (v2.1's `xstageC`), then `2^{j+2}` in `oT + 36`. -/
def xstageO (xstep : Layout → XCmdO) (L : Layout) : XCmdO :=
  .seq (xcoreO xstep L)
  (.seq (.base (toX (VL.sconst L (oT + 14) ((1 : ℤ) : ℚ))))
  (.seq (.base (toX (VL.sconst L (oT + 15) ((0 : ℤ) : ℚ))))
  (.seq (.base (xstageC L oT rT aT rD))
  (.base (toX (VL.sop2 L .add (oT + 36) (oT + 36) (oT + 36)))))))

end AdversarialBco.Unified.ProgO.TriO
