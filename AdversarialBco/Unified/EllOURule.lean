/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.EllOUBlock
public import AdversarialBco.Unified.EllORule

@[expose] public section

/-!
# The ELL-O block uniform in `d`

`xellOU L B` is `xellO` (EllORule.lean) with SEP and gauge blocks whose texts do not depend on `d` (`xsepU`,
`xgaugeU`, which read `d` in the register `0`): one code for every dimension. `ellOBlockOKU` is `ellORule` for it:
`EllOBlockOKU` is `EllOBlockOK` (EllSpec.lean) when the test's data puts `d` in the register `0` (`hT0`) and the test
block keeps that register (`hNt0`), with the same constants `C = 10^10`, `k₀ = 8` and sizes `215`, `112`, `14`.
-/

namespace AdversarialBco.Uni.EllO

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.Transfer AdversarialBco.Bit.RQ Matrix

variable {d : ℕ}

/-- `EllOBlockOK` with `d` in the register `0` in the test's data and the register `0` kept by the test block. -/
def EllOBlockOKU (L : Layout) (XO : XCtxO d) (ℓa ℓ : ℕ) (B : EllOBlk) (nS nN nA C k₀ : ℕ)
    (ellc : XCmdO → XCmdO) : Prop :=
  ∀ (I : EllOI d) (κ : ℕ) (TB : XCmdO) (TDat : Env d → Prop) (T : ℕ → (Fin d → ℚ) → Bool) (Kt bt : ℕ)
    (St Nt : ℕ → Prop) (Art : ℕ → ℕ → Prop) (σ : Env d),
    LayOK L d ℓa → B.OK L nS nN nA → 1 ≤ d → 0 < I.Dc →
    TestOK L XO ℓa ℓ TB (TDatK B TDat (I.eK + κ)) (B.aW + 1) B.rE bt (T (I.eK + κ)) Kt St Nt Art →
    B.TestAvoid St Nt Art →
    Stable TDat (fun y => B.ownS y ∨ St y) (fun j => B.ownN j ∨ Nt j) (fun b k => B.ownA b k ∨ Art b k) →
    (∀ τ : Env d, TDat τ → τ.nat 0 = d) → (∀ j, Nt j → j ≠ 0) →
    TDat σ → EllOIn B I κ σ →
    C * (d + ellOSz I + κ + 1) ^ k₀ ≤ bt → bt + 4 ≤ ℓ → C * (d + ellOSz I + κ + 1) ^ k₀ < 2 ^ ℓa →
    XRunsBO L XO ℓa ℓ (ellc TB) σ (C * (d + ellOSz I + κ + Kt + 1) ^ k₀) (fun σ' =>
      EllOOut B (ellOI I (T (I.eK + κ))) (ellExpO I) σ' ∧ σ'.draws = σ.draws ∧
        FrameA (fun y => B.ownS y ∨ St y) (fun j => B.ownN j ∨ Nt j) (fun b k => B.ownA b k ∨ Art b k)
          σ σ')

/-- The ELL-O block with SEP and gauge blocks uniform in `d`. -/
def xellOU (L : Layout) (B : EllOBlk) : XCmdO → XCmdO :=
  xellO L B (xsepU L (sepLayO B)) (xgaugeU L (gaugeLayO B))

/-- **The rule of the ELL-O block uniform in `d`.** -/
theorem ellOBlockOKU (L : Layout) (XO : XCtxO d) (ℓa ℓ : ℕ) (B : EllOBlk) :
    EllOBlockOKU L XO ℓa ℓ B 215 112 14 10000000000 8 (xellOU L B) := by
  intro I κ TB TDat T Kt bt St Nt Art σ hL hB hd hDc hTB hav hst hT0 hNt0 hTD hin hbt hℓ hℓa
  have hS := sepBlockOKU L XO ℓa ℓ (sepLayO B)
  have hG := gaugeBlockOKU L XO ℓa ℓ (gaugeLayO B)
  set W := d + ellOSz I + κ + 1 with hW
  have hW1 : 1 ≤ W := by omega
  have hW2 : W ^ 2 ≤ W ^ 8 := pow_le_pow_right₀ hW1 (by norm_num)
  have hW3 : W ^ 3 ≤ W ^ 8 := pow_le_pow_right₀ hW1 (by norm_num)
  have hW1' : W ≤ W ^ 8 := by
    calc W = W ^ 1 := (pow_one W).symm
      _ ≤ W ^ 8 := pow_le_pow_right₀ hW1 (by norm_num)
  have h3 : (d + ellOSz I + 1) ^ 3 ≤ W ^ 3 := Nat.pow_le_pow_left (by omega) 3
  have hB' : ∀ hr : 0 < I.r, ∀ he : 0 < I.e, bigO I κ ≤ 10000000000 * W ^ 8 := fun hr he => by
    have := bigO_le I κ hd hr he
    rw [← hW] at this
    omega
  exact XVO.mono (XVO.ellOD hL hd hB hDc hS hG hT0 hNt0 hTB hav hst hTD hin (fun hr he => (hB' hr he).trans hbt) hℓ
    (fun hr he => (hB' hr he).trans_lt hℓa) (by omega) (by omega)) (ellOU_le I κ Kt hd) (fun _ h => h)

end AdversarialBco.Uni.EllO
