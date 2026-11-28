/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.ProgOBL
public import AdversarialBco.Unified.XRunsO
public import AdversarialBco.Bit.Transfer.XBLHeadR

@[expose] public section

/-!
# BL-O's round in six sub-blocks

BL-O's round (ProgOBL.lean) in six sub-blocks, with one named contract each. The round's code:

* `xAO`: R1a (the draw blocks `0, ..., nBlk - 2` of the round, `Γ` in `aGam`), then the dispatch on the mode: R2 in
  mode `run` (`X'`, the gauge `π̃(X')`, `pt'`, the play point `μ_S + A_S (X'/pt')` in `aPl`), the frame centre `a`
  into `aPl` in the modes `off` and `guard`;
* `xMO`: the play leaf on `aPl`;
* `xBO`: R3 (the clipped reading into `sObs`), R1b (the dither block, `Γ_ζ` in `sZeta`), then in mode `run` R5 to
  R15 (the tail, with the two ELL-O calls).

The six contracts have each their own constants `BlkK` (the budget `C (W + E + 1)^k`, the condition
`Cn (W + E₀ + 1)^kn ≤ E` on the exponent of the invariant, the room `nS, nN, nA`). R2 hands the tail `RunDat U` (the
scale `pt' = pt_N/pt_D` below `2^U` with `U` its own budget, and `Â Γ` in `aWv`), and the tail runs within
`C (W + E + U + 1)^k`. R3 and R1b are stated with their frames, so the data of R2 pass through them.
-/

namespace AdversarialBco.Unified.ProgO

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.Transfer AdversarialBco.Bit.Transfer.BLM
open AdversarialBco.Uni
open AdversarialBco.Unified.BLO
open AdversarialBco.Bit.BLP (Cfg Mode St)
open BitRAM BitRAMO Matrix

variable {d : ℕ}

/-! ## A round of BL-O -/

/-- The constants of a sub-block: the budget `C (W + E + 1)^k`, the condition `Cn (W + E₀ + 1)^kn ≤ E`, the room. -/
structure BlkK where
  C : ℕ
  k : ℕ
  Cn : ℕ
  kn : ℕ
  nS : ℕ
  nN : ℕ
  nA : ℕ

/-- The cells R3 may change: `sObs` and the slots from `tR` on, the registers from `8` on, the arrays from `32` on. -/
def SR3 (y : ℕ) : Prop := y = sObs ∨ tR ≤ y

/-- The cells R1b may change: `sZeta` and the slots from `tR` on, the registers from `8` on, the arrays from `32` on. -/
def SR1b (y : ℕ) : Prop := y = sZeta ∨ tR ≤ y

/-- The scratch registers. -/
def NScr (j : ℕ) : Prop := 8 ≤ j

/-- The scratch arrays. -/
def AScr (b _k : ℕ) : Prop := 32 ≤ b

/-! ## The round's code -/

/-- Segment A: R1a, then R2 in mode `run` (`sMode = 2`), the play of the frame centre otherwise. -/
def xAO (x1a x2 xog : Layout → XCmdO) (L : Layout) : XCmdO :=
  .seq (x1a L) (.seq (.base (toX (VL.sconst L sC2 2))) (xifSO L sMode sC2 (xog L) (x2 L)))

/-- Segment M: the play leaf on `aPl`. -/
def xMO (L : Layout) : XCmdO := .base (xplay L aPl)

/-- Segment B: R3, R1b, then the tail in mode `run`. -/
def xBO (x3 x1b xt : Layout → XCmdO) (L : Layout) : XCmdO :=
  .seq (x3 L) (.seq (x1b L) (.seq (.base (toX (VL.sconst L sC2 2))) (xifSO L sMode sC2 (.base .skip) (xt L))))

/-! ## The constants of the assembled round -/

/-- The six constants. -/
structure SplitK where
  r1a : BlkK
  r2 : BlkK
  og : BlkK
  r3 : BlkK
  r1b : BlkK
  tl : BlkK

namespace SplitK

variable (S : SplitK)

/-- The coefficient of the round's segments. -/
def C : ℕ := S.r1a.C + S.r2.C + S.og.C + S.r3.C + S.r1b.C + S.tl.C * (S.r2.C + 1) ^ S.tl.k + 8

/-- The exponent of the round's segments. -/
def k : ℕ := max (max (max S.r1a.k S.r2.k) (max S.og.k S.r3.k)) (max S.r1b.k ((S.r2.k + 1) * S.tl.k)) + 1

/-- The coefficient of the condition on `E`. -/
def Cn : ℕ := S.r1a.Cn + S.r2.Cn + S.og.Cn + S.r3.Cn + S.r1b.Cn + S.tl.Cn

/-- The exponent of the condition on `E`. -/
def kn : ℕ := max (max (max S.r1a.kn S.r2.kn) (max S.og.kn S.r3.kn)) (max S.r1b.kn S.tl.kn)

/-- The room. -/
def nS : ℕ := max (max (max S.r1a.nS S.r2.nS) (max S.og.nS S.r3.nS)) (max S.r1b.nS S.tl.nS) + 64
def nN : ℕ := max (max (max S.r1a.nN S.r2.nN) (max S.og.nN S.r3.nN)) (max S.r1b.nN S.tl.nN) + 32
def nA : ℕ := max (max (max S.r1a.nA S.r2.nA) (max S.og.nA S.r3.nA)) (max S.r1b.nA S.tl.nA) + 32

end SplitK

/-! ## The assembly -/

theorem pow_le_pow_one {x i j : ℕ} (hx : 1 ≤ x) (h : i ≤ j) : x ^ i ≤ x ^ j := Nat.pow_le_pow_right hx h

/-- A block's budget below the round's. -/
theorem blk_le {x C k C' k' : ℕ} (hx : 1 ≤ x) (hC : C ≤ C') (hk : k ≤ k') : C * x ^ k ≤ C' * x ^ k' :=
  Nat.mul_le_mul hC (pow_le_pow_one hx hk)

/-- The tail's budget at `U = C₂ x^{k₂}`, `x = W + E + 1`. -/
theorem tail_le {W E C2 k2 Ct kt : ℕ} :
    Ct * (W + E + C2 * (W + E + 1) ^ k2 + 1) ^ kt ≤
      Ct * (C2 + 1) ^ kt * (W + E + 1) ^ ((k2 + 1) * kt) := by
  have hx : 1 ≤ W + E + 1 := by omega
  have h1 : W + E + C2 * (W + E + 1) ^ k2 + 1 ≤ (C2 + 1) * (W + E + 1) ^ (k2 + 1) := by
    have a1 : W + E + 1 ≤ (W + E + 1) ^ (k2 + 1) := by
      calc W + E + 1 = (W + E + 1) ^ 1 := (pow_one _).symm
        _ ≤ _ := pow_le_pow_one hx (by omega)
    have a2 : (W + E + 1) ^ k2 ≤ (W + E + 1) ^ (k2 + 1) := pow_le_pow_one hx (by omega)
    have a3 : C2 * (W + E + 1) ^ k2 ≤ C2 * (W + E + 1) ^ (k2 + 1) := Nat.mul_le_mul_left _ a2
    calc W + E + C2 * (W + E + 1) ^ k2 + 1 = (W + E + 1) + C2 * (W + E + 1) ^ k2 := by ring
      _ ≤ (W + E + 1) ^ (k2 + 1) + C2 * (W + E + 1) ^ (k2 + 1) := Nat.add_le_add a1 a3
      _ = (C2 + 1) * (W + E + 1) ^ (k2 + 1) := by ring
  calc Ct * (W + E + C2 * (W + E + 1) ^ k2 + 1) ^ kt ≤ Ct * ((C2 + 1) * (W + E + 1) ^ (k2 + 1)) ^ kt :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h1 _)
    _ = Ct * (C2 + 1) ^ kt * (W + E + 1) ^ ((k2 + 1) * kt) := by rw [mul_pow, ← pow_mul]; ring

/-- The scalar `sMode` holds `0`, `1` or `2`, below `2` exactly in the modes `off` and `guard`. -/
theorem sMode_cases {L : Layout} {n K0 E t : ℕ} {c : CfgO d} {mo : Mode d} {σ0 σ : Env d}
    (hI : BLOInv L n K0 E c mo t σ0) (hP : SamePers σ0 σ) :
    (σ.sc sMode = 0 ∨ σ.sc sMode = 1 ∨ σ.sc sMode = 2) ∧ (σ.sc sMode < 2 ↔ (mo = .off ∨ mo = .guard)) := by
  have e : σ.sc sMode = σ0.sc sMode := hP.2.1 sMode (by decide)
  have hm := hI.mode
  rw [e]
  cases mo with
  | off => simp only [ModeRep] at hm; rw [hm]; norm_num
  | guard => simp only [ModeRep] at hm; rw [hm]; norm_num
  | run st =>
    simp only [ModeRep] at hm
    rw [hm.1]
    refine ⟨by norm_num, by norm_num⟩

/-- A small value is below `2^ℓ`. -/
theorem small_lt {v : ℝ} {ℓ : ℕ} (hℓ : 2 ≤ ℓ) (hv : v = 0 ∨ v = 1 ∨ v = 2) : |v| < 2 ^ ℓ := by
  have : (4 : ℝ) ≤ 2 ^ ℓ := by
    calc (4 : ℝ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ ℓ := pow_le_pow_right₀ (by norm_num) hℓ
  rcases hv with rfl | rfl | rfl <;> norm_num <;> linarith

/-- A frame of scratch cells keeps the persistent ones. -/
theorem samePers_ofC {S N : ℕ → Prop} {Ar : ℕ → ℕ → Prop} {σ σ' : Env d} (h : FrameC S N Ar σ σ')
    (hS : ∀ y, S y → nSP ≤ y) (hN : ∀ j, N j → 8 ≤ j) (hA : ∀ a k, Ar a k → nAP ≤ a) : SamePers σ σ' :=
  ⟨fun j hj => h.1 j fun h' => by have := hN j h'; omega, fun y hy => h.2.1 y fun h' => by have := hS y h'; omega,
    fun a ha k => h.2.2 a k fun h' => by have := hA a k h'; omega⟩

theorem SR3_pers : ∀ y, SR3 y → nSP ≤ y := by
  intro y h
  rcases h with rfl | h
  · decide
  · exact le_trans (by decide) h

theorem SR1b_pers : ∀ y, SR1b y → nSP ≤ y := by
  intro y h
  rcases h with rfl | h
  · decide
  · exact le_trans (by decide) h

theorem AScr_pers : ∀ a k, AScr a k → nAP ≤ a := fun _ _ h => le_trans (by decide) h

end AdversarialBco.Unified.ProgO
