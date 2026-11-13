/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XBLCall

@[expose] public section

/-!
# The two ends of a round of BL in mode `run` (frozen statements)

* `CommitBL` (R15 COMMIT): the new state `⟨false, μ', A', B', b', k', G', l'⟩` into BL's persistent cells: `μ' = x/2^e`
  from the output of the projection routine (`EllOut`: `1` in the slot `768`, `e` in `769`, `x` in the array `32`),
  `A'`, `B'`, `b'`, `G'` from the arrays `26`, `27`, `28`, `29` (numerators on the grid `2^{-p}`, matrices in the cells
  `d i + j`), `k'`, `l'` from the slots `59`, `63`.
* `FireBL` (R12 FIRE): the epoch start `init` into BL's persistent cells.

From `BLInv` in mode `run` with any state, both end in `BLInv` in mode `run` with the new state, at the same round.
Every value read at most `2^E` in absolute value, `e ≤ E`. Work term `W = d + E + 1`: within `C W^k` units, under
`C W^k ≤ ℓ` and `C W^k < 2^ℓa`. The commands read no coin and change only the state's slots (`sFirst`, `sDmu`, `sK`,
`sL`), the slots from `26` on, the registers from `8` on and the arrays from `3` on.
-/

namespace AdversarialBco.Bit.Transfer.BLM

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.BLP AdversarialBco.Bit.RQ Matrix

/-- The cells the two ends may change. -/
def SEnd (y : ℕ) : Prop := y = sFirst ∨ y = sDmu ∨ y = sK ∨ y = sL ∨ nSP ≤ y
def NEnd (j : ℕ) : Prop := 8 ≤ j
def AEnd (a _k : ℕ) : Prop := aMu ≤ a

/-- **R15 COMMIT (frozen).** -/
def CommitBL : Prop :=
  ∃ (xcom : Layout → XCmd) (C k : ℕ),
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

/-- **R12 FIRE (frozen).** -/
def FireBL : Prop :=
  ∃ (xfire : Layout → XCmd) (C k : ℕ),
    ∀ (d : ℕ) (L : Layout) (X : XCtx d) (ℓa ℓ n m K0 E t : ℕ) (cfg : Cfg d) (st : St d) (σ : Env d),
      1 ≤ d → 1 ≤ n → cfg.par = par d n → LayOK L d ℓa → BLLay L → BLInv L n m K0 E cfg (.run st) t σ →
      C * (d + E + 1) ^ k ≤ ℓ → C * (d + E + 1) ^ k < 2 ^ ℓa →
      XRunsB L X ℓa ℓ (xfire L) σ (C * (d + E + 1) ^ k) (fun σ' =>
        BLInv L n m K0 E cfg (.run (init cfg.par d)) t σ' ∧ σ'.draws = σ.draws ∧ FrameA SEnd NEnd AEnd σ σ')

end AdversarialBco.Bit.Transfer.BLM
