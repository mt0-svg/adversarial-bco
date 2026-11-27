/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.TailOPure

@[expose] public section

/-!
# The sub-block contracts of BL-O's tail

`SpecTail` (ProgOSplit.lean) is assembled (TailOAsm.lean) from v2.1's generic machine lemmas (R5 to R9, R10, R12,
R13, the guard, R15's commit `commitBL`), the magnitude statements `MagBLO`, `ExpBLO` (Unified/Mag*.lean) and four
named contracts:

* `DTSpecO`, `DLSpecO`, `FireSpecO`: the data of R11 TEST and of R14 LINE as integer pairs (`PrepIn`), and R12's new
  epoch, at BL-O's PARAM `cfg.par = parN ne d n` with `1 ≤ ne`.
* `CallSpecO`: one ELL-O call of BL-O. From BL-O's invariant (any mode, any round) and the call data as pairs below
  `2^s` (`PrepIn`), the command writes ELL-O's integer answer `apI` on the call `callO c H g ℓ r P f e` and its
  exponent `ellExpO` into the output cells of v2.1's block `blkBL` (`EllOut`, read by `commitBL` and by R12), within
  `C (W + E + s + 1)^k` units; it reads no coin and writes only the cells of v2.1's call (`oE` up, the preparation's).

The statements `DataTO`, `DataLO`, `FireO`, `CallO` are the existence of a command meeting each contract.
-/

namespace AdversarialBco.Unified.ProgO

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.Transfer AdversarialBco.Bit.Transfer.BLM
open AdversarialBco.Uni
open AdversarialBco.Unified.BLO
open AdversarialBco.Bit.BLP (Cfg Mode St CallQ init LT Lmu eBL)
open BitRAM BitRAMO Matrix

variable {d : ℕ}

/-! ## The data of the calls and the fire at BL-O's PARAM -/

/-- **The data of R11 TEST** at BL-O's PARAM, `cfg.par = parN ne d n`. -/
def DTSpecO (xdt : Layout → XCmd) (C k : ℕ) : Prop :=
  ∀ (d : ℕ) (L : Layout) (X : XCtx d) (ℓa ℓ n m K0 E t ne : ℕ) (cfg : Cfg d) (st : St d)
    (Bp : Matrix (Fin d) (Fin d) ℚ) (bp Gp : Fin d → ℚ) (σ : Env d),
    1 ≤ d → 1 ≤ n → 1 ≤ ne → cfg.par = parN ne d n → LayOK L d ℓa → BLLay L → BLInv L n m K0 E cfg (.run st) t σ →
    (∀ i j : Fin d, σ.arr 27 (d * i + j) = qn cfg.par.p (Bp i j) ∧ OnG cfg.par.p (Bp i j) ∧
      |qn cfg.par.p (Bp i j)| ≤ 2 ^ E) →
    (∀ j : Fin d, σ.arr 28 j = qn cfg.par.p (bp j) ∧ OnG cfg.par.p (bp j) ∧ |qn cfg.par.p (bp j)| ≤ 2 ^ E) →
    (∀ j : Fin d, σ.arr 29 j = qn cfg.par.p (Gp j) ∧ OnG cfg.par.p (Gp j) ∧ |qn cfg.par.p (Gp j)| ≤ 2 ^ E) →
    C * (d + E + 1) ^ k ≤ ℓ → C * (d + E + 1) ^ k < 2 ^ ℓa →
    XRunsB L X ℓa ℓ (xdt L) σ (C * (d + E + 1) ^ k) (fun σ' =>
      PrepIn σ' cfg (C * (d + E + 1) ^ k) (if st.first then 0 else st.B * st.Bᵀ) (if st.first then 0 else st.b)
        (if st.first then 0 else LT cfg.par - st.k) (if st.first then 1 - cfg.par.eps else Bit.BLP.rB cfg.par / 2)
        (Bp * Bpᵀ) (bp - (cfg.par.eta / 2) • Gp)
        (if st.first then (1 - cfg.par.eps) ^ 2 / (cfg.par.Ne * d * 8)
          else Bit.BLP.rB cfg.par ^ 2 / (cfg.par.Ne * d * 8)) ∧
      σ'.draws = σ.draws ∧ FrameA SDat NDat ADat σ σ')

/-- **The data of R14 LINE** at BL-O's PARAM, `cfg.par = parN ne d n`. -/
def DLSpecO (xdl : Layout → XCmd) (C k : ℕ) : Prop :=
  ∀ (d : ℕ) (L : Layout) (X : XCtx d) (ℓa ℓ n m K0 E t ne : ℕ) (cfg : Cfg d) (st : St d)
    (Bp : Matrix (Fin d) (Fin d) ℚ) (bp : Fin d → ℚ) (kp : ℚ) (wh : Fin d → ℤ) (Dw : ℤ) (σ : Env d),
    1 ≤ d → 1 ≤ n → 1 ≤ ne → cfg.par = parN ne d n → LayOK L d ℓa → BLLay L → BLInv L n m K0 E cfg (.run st) t σ →
    (∀ i j : Fin d, σ.arr 27 (d * i + j) = qn cfg.par.p (Bp i j) ∧ OnG cfg.par.p (Bp i j) ∧
      |qn cfg.par.p (Bp i j)| ≤ 2 ^ E) →
    (∀ j : Fin d, σ.arr 28 j = qn cfg.par.p (bp j) ∧ OnG cfg.par.p (bp j) ∧ |qn cfg.par.p (bp j)| ≤ 2 ^ E) →
    σ.sc 59 = qn cfg.par.p kp → OnG cfg.par.p kp → |qn cfg.par.p kp| ≤ 2 ^ E →
    0 < Dw → Dw ≤ 2 ^ E → σ.sc 91 = Dw → (∀ j : Fin d, σ.arr 31 j = wh j ∧ |wh j| ≤ 2 ^ E) →
    C * (d + E + 1) ^ k ≤ ℓ → C * (d + E + 1) ^ k < 2 ^ ℓa →
    XRunsB L X ℓa ℓ (xdl L) σ (C * (d + E + 1) ^ k) (fun σ' =>
      PrepIn σ' cfg (C * (d + E + 1) ^ k) (Bp * Bpᵀ) bp (Lmu cfg.par - kp) (Bit.BLP.rB cfg.par / 2) (Bp * Bpᵀ)
        ((Bp * Bpᵀ) *ᵥ fun j => (wh j : ℚ) / Dw) (eBL cfg.par d n) ∧
      σ'.draws = σ.draws ∧ FrameA SDat NDat ADat σ σ')

/-- **R12's new epoch** at BL-O's PARAM, `cfg.par = parN ne d n`. -/
def FireSpecO (xfire : Layout → XCmd) (C k : ℕ) : Prop :=
  ∀ (d : ℕ) (L : Layout) (X : XCtx d) (ℓa ℓ n m K0 E t ne : ℕ) (cfg : Cfg d) (st : St d) (σ : Env d),
    1 ≤ d → 1 ≤ n → 1 ≤ ne → cfg.par = parN ne d n → LayOK L d ℓa → BLLay L → BLInv L n m K0 E cfg (.run st) t σ →
    C * (d + E + 1) ^ k ≤ ℓ → C * (d + E + 1) ^ k < 2 ^ ℓa →
    XRunsB L X ℓa ℓ (xfire L) σ (C * (d + E + 1) ^ k) (fun σ' =>
      BLInv L n m K0 E cfg (.run (init cfg.par d)) t σ' ∧ σ'.draws = σ.draws ∧ FrameA SEnd NEnd AEnd σ σ')

/-! ## The ELL-O call -/

/-- The cells a call writes: v2.1's (the block from `oE`, `rEE`, `aWE`, and the preparation's own cells). -/
def SCall (y : ℕ) : Prop := oE ≤ y ∨ SPrep y
def NCall (j : ℕ) : Prop := rEE ≤ j ∨ NPrep j
def ACall (a _k : ℕ) : Prop := aWE ≤ a ∨ APrep a

/-- **One ELL-O call of BL-O**: from BL-O's invariant and the call data as integer pairs below `2^s`, ELL-O's answer
on `callO c H g ℓ r P f e` and its exponent in the output cells of `blkBL`, within `C (W + E + s + 1)^k` units, with
room `nS, nN, nA` in the layout. -/
def CallSpecO (xcall : Layout → XCmdO) (C k nS nN nA : ℕ) : Prop :=
  ∀ (d : ℕ) (L : Layout) (w : WorldO d) (n : ℕ) (δ r0 R0 : ℚ) (a : Fin d → ℚ) (K0 E ℓa ℓ s t : ℕ) (mo : Mode d)
    (H : Matrix (Fin d) (Fin d) ℚ) (g : Fin d → ℚ) (ℓq r : ℚ) (P : Matrix (Fin d) (Fin d) ℚ) (f : Fin d → ℚ) (e : ℚ)
    (σ : Env d),
    InU d n δ r0 R0 → LayOK L d ℓa → RoomO L nS nN nA →
    BLOInv L n K0 E (cfgW d n δ r0 R0 a w) mo t σ → PrepIn σ (cfgV (cfgW d n δ r0 R0 a w)) s H g ℓq r P f e →
    C * (wU d n δ r0 R0 a + E + s + 1) ^ k ≤ ℓ → C * (wU d n δ r0 R0 a + E + s + 1) ^ k < 2 ^ ℓa →
    XRunsBO L (ctxU w n δ r0 R0 a) ℓa ℓ (xcall L) σ (C * (wU d n δ r0 R0 a + E + s + 1) ^ k) (fun σ' =>
      EllOut blkBL (apI w.orc (cfgW d n δ r0 R0 a w) (callO (cfgW d n δ r0 R0 a w) H g ℓq r P f e))
        (ellExpO (clearO (callO (cfgW d n δ r0 R0 a w) H g ℓq r P f e))) σ' ∧ σ'.draws = σ.draws ∧
      FrameA SCall NCall ACall σ σ')

/-! ## The statements of the four contracts -/

def DataTO : Prop := ∃ (xdt : Layout → XCmd) (C k : ℕ), DTSpecO xdt C k
def DataLO : Prop := ∃ (xdl : Layout → XCmd) (C k : ℕ), DLSpecO xdl C k
def FireO : Prop := ∃ (xfire : Layout → XCmd) (C k : ℕ), FireSpecO xfire C k
def CallO : Prop := ∃ (xcall : Layout → XCmdO) (C k nS nN nA : ℕ), CallSpecO xcall C k nS nN nA

end AdversarialBco.Unified.ProgO
