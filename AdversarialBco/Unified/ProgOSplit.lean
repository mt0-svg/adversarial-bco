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

`RoundSpecO` (ProgOBL.lean) from six named contracts, one per sub-block of the round. The round's code:

* `xAO`: R1a (the draw blocks `0, ..., nBlk - 2` of the round, `Γ` in `aGam`), then the dispatch on the mode: R2 in
  mode `run` (`X'`, the gauge `π̃(X')`, `pt'`, the play point `μ_S + A_S (X'/pt')` in `aPl`), the frame centre `a`
  into `aPl` in the modes `off` and `guard`;
* `xMO`: the play leaf on `aPl`;
* `xBO`: R3 (the clipped reading into `sObs`), R1b (the dither block, `Γ_ζ` in `sZeta`), then in mode `run` R5 to
  R15 (the tail, with the two ELL-O calls).

The six contracts, each at its own constants `BlkK` (the budget `C (W + E + 1)^k`, the condition
`Cn (W + E₀ + 1)^kn ≤ E` on the exponent of the invariant, the room `nS, nN, nA`): `SpecR1a`, `SpecR2`, `SpecOG`,
`SpecR3`, `SpecR1b`, `SpecTail`. R2 hands the tail `RunDat U` (the scale `pt' = pt_N/pt_D` below `2^U` with `U` its
own budget, and `Â Γ` in `aWv`), and the tail runs within `C (W + E + U + 1)^k`. R3 and R1b are stated with their
frames, so the data of R2 pass through them.

`roundSpecO_of`: the six contracts give `RoundSpecO` of the assembled round; `progRoundO_of`: `ProgRoundO` from the
six statements `ProgR1a`, ..., `ProgTail`.
-/

namespace AdversarialBco.Unified.ProgO

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.Transfer AdversarialBco.Bit.Transfer.BLM
open AdversarialBco.Uni
open AdversarialBco.Unified.BLO
open AdversarialBco.Bit.BLP (Cfg Mode St)
open BitRAM BitRAMO Matrix

variable {d : ℕ}

/-! ## A round of BL-O -/

/-- What fixes round `t` of BL-O: the layout, the world, the input, the exponents `E₀` (the position) and `E` (the
invariant), the widths `ℓa`, `ℓ`, the round. -/
structure RdO (d : ℕ) where
  L : Layout
  w : WorldO d
  n : ℕ
  δ : ℚ
  r0 : ℚ
  R0 : ℚ
  a : Fin d → ℚ
  E0 : ℕ
  E : ℕ
  ℓa : ℕ
  ℓ : ℕ
  t : ℕ

/-- The constants of a sub-block: the budget `C (W + E + 1)^k`, the condition `Cn (W + E₀ + 1)^kn ≤ E`, the room. -/
structure BlkK where
  C : ℕ
  k : ℕ
  Cn : ℕ
  kn : ℕ
  nS : ℕ
  nN : ℕ
  nA : ℕ

namespace RdO

variable (R : RdO d)

/-- BL-O's configuration on the world. -/
def c : CfgO d := cfgW d R.n R.δ R.r0 R.R0 R.a R.w

/-- The prologue's coins. -/
def K0 : ℕ := K0O d R.n R.δ R.r0 R.R0

/-- The block parameter of the schedule. -/
def pB : ℕ := (parO d R.n R.δ).B

/-- The context of the run. -/
def ctx : XCtxO d := ctxU R.w R.n R.δ R.r0 R.R0 R.a

/-- The work term `W`. -/
def W : ℕ := wU d R.n R.δ R.r0 R.R0 R.a

/-- The mode before the round. -/
noncomputable def mo : Mode d := modeO d R.n R.δ R.r0 R.R0 R.a R.w R.t

/-- The draw `ξ'` of the round. -/
def ξ : Fin d → ℚ := (drawO d R.n R.δ R.r0 R.R0 R.w.cs R.t).1

/-- The integers `Γ` of the draw. -/
def Γ : Fin d → ℤ := fun i => gamI R.w.cs R.K0 R.pB d R.t i

/-- The integer `Γ_ζ` of the dither. -/
def gz : ℤ := zetI R.w.cs R.K0 R.pB d R.t

/-- BL-O's play of the round. -/
noncomputable def play : Fin d → ℚ := playO d R.n R.δ R.r0 R.R0 R.a R.w R.t

/-- BL-O's reading of the round. -/
noncomputable def obs : ℤ := readO d R.n R.δ R.r0 R.R0 R.a R.w R.t

/-- The budget `C (W + E + 1)^k` of a sub-block. -/
def bud (b : BlkK) : ℕ := b.C * (R.W + R.E + 1) ^ b.k

/-- BL-O's invariant before the round. -/
def Inv (σ : Env d) : Prop := BLOInv R.L R.n R.K0 R.E R.c R.mo R.t σ

/-- BL-O's invariant before the next round. -/
def Inv1 (σ : Env d) : Prop :=
  BLOInv R.L R.n R.K0 R.E R.c (modeO d R.n R.δ R.r0 R.R0 R.a R.w (R.t + 1)) (R.t + 1) σ

/-- A run of a command of the round. -/
def RunsO (x : XCmdO) (σ : Env d) (K : ℕ) (Q : Env d → Prop) : Prop := XRunsBO R.L R.ctx R.ℓa R.ℓ x σ K Q

/-- The hypotheses of a sub-block at the constants `b` within the budget `K`. -/
structure Hyp (b : BlkK) (K : ℕ) : Prop where
  inU : InU d R.n R.δ R.r0 R.R0
  ht : R.t < R.n
  lay : LayOK R.L d R.ℓa
  room : RoomO R.L b.nS b.nN b.nA
  pos : PosBnd (cfgV R.c) R.E0
  hE : b.Cn * (R.W + R.E0 + 1) ^ b.kn ≤ R.E
  hℓ : K ≤ R.ℓ
  hℓa : K < 2 ^ R.ℓa

/-- After R1a: the persistent cells of the round's start `σ0`, `t` rounds, `D' t` coins, `Γ` in `aGam`. -/
structure PostR1a (σ0 σ : Env d) : Prop where
  pers : SamePers σ0 σ
  rounds : σ.rounds = R.t
  draws : σ.draws = DO' d R.n R.δ R.r0 R.R0 R.a R.t
  gam : ∀ i : Fin d, σ.arr aGam i = R.Γ i

/-- After the play's computation: R1a's facts and BL-O's play in `aPl`, in the form of the play leaf. -/
structure PostA (σ0 σ : Env d) : Prop where
  r1a : R.PostR1a σ0 σ
  pt : PtRep σ aPl R.play
  ptb : ∀ j ≤ d, |σ.arr aPl j| < 2 ^ R.ℓ

/-- What R2 leaves for the tail in mode `run` with the state `st`: `pt' = pt_N/pt_D` in `sPtN`, `sPtD`, below
`2^U`, and `Â Γ` in `aWv`. -/
def RunDat (U : ℕ) (st : St d) (σ : Env d) : Prop :=
  (∃ pN pD : ℤ, 0 < pN ∧ 0 < pD ∧ σ.sc sPtN = pN ∧ σ.sc sPtD = pD ∧
    ptO R.w.orc R.c (XO R.c st R.ξ) = (pN : ℚ) / pD ∧ |pN| ≤ 2 ^ U ∧ |pD| ≤ 2 ^ U) ∧
  ∀ i : Fin d, σ.arr aWv i = ((fun i k => qn R.c.par.p (st.A i k) : Matrix (Fin d) (Fin d) ℤ) *ᵥ R.Γ) i

/-- Before the tail: the persistent cells of `σ0`, `t + 1` rounds, the coins of round `t` read, `Γ`, `Γ_ζ`, the
reading, and R2's data. -/
structure PostT (U : ℕ) (st : St d) (σ0 σ : Env d) : Prop where
  pers : SamePers σ0 σ
  rounds : σ.rounds = R.t + 1
  draws : σ.draws = Bit.Sched.blkStart d R.K0 R.pB (R.t + 1) 0
  gam : ∀ i : Fin d, σ.arr aGam i = R.Γ i
  zeta : σ.sc sZeta = R.gz
  obs : σ.sc sObs = R.obs
  dat : R.RunDat U st σ

end RdO

/-- The cells R3 may change: `sObs` and the slots from `tR` on, the registers from `8` on, the arrays from `32` on. -/
def SR3 (y : ℕ) : Prop := y = sObs ∨ tR ≤ y

/-- The cells R1b may change: `sZeta` and the slots from `tR` on, the registers from `8` on, the arrays from `32` on. -/
def SR1b (y : ℕ) : Prop := y = sZeta ∨ tR ≤ y

/-- The scratch registers. -/
def NScr (j : ℕ) : Prop := 8 ≤ j

/-- The scratch arrays. -/
def AScr (b _k : ℕ) : Prop := 32 ≤ b

/-! ## The six contracts -/

/-- **R1a, the draw blocks**: from BL-O's invariant before round `t`, the blocks `0, ..., nBlk - 2` of the round:
`Γ` in `aGam`, the coins `D' t`. -/
def SpecR1a (x : Layout → XCmdO) (b : BlkK) : Prop :=
  ∀ (d : ℕ) (R : RdO d) (σ : Env d), R.Hyp b (R.bud b) → R.Inv σ → R.RunsO (x R.L) σ (R.bud b) (R.PostR1a σ)

/-- **R2, the play in mode `run`**: from R1a's end, `X'`, the gauge, `pt'`, BL-O's play in `aPl`, and the data of the
tail below `2^{budget}`. -/
def SpecR2 (x : Layout → XCmdO) (b : BlkK) : Prop :=
  ∀ (d : ℕ) (R : RdO d) (st : St d) (σ0 σ : Env d), R.Hyp b (R.bud b) → R.Inv σ0 → R.mo = .run st →
    R.PostR1a σ0 σ → R.RunsO (x R.L) σ (R.bud b) (fun σ' => R.PostA σ0 σ' ∧ R.RunDat (R.bud b) st σ')

/-- **The play in the modes `off` and `guard`**: from R1a's end, the frame centre `a` in `aPl`. -/
def SpecOG (x : Layout → XCmdO) (b : BlkK) : Prop :=
  ∀ (d : ℕ) (R : RdO d) (σ0 σ : Env d), R.Hyp b (R.bud b) → R.Inv σ0 → (R.mo = .off ∨ R.mo = .guard) →
    R.PostR1a σ0 σ → R.RunsO (x R.L) σ (R.bud b) (R.PostA σ0)

/-- **R3, the clipped reading**: after the play of round `t`, `sObs := clip qO ⌊2^p (f_t(x'_t) + noise_t)⌋`
(`readO`), in the frame `SR3`. -/
def SpecR3 (x : Layout → XCmdO) (b : BlkK) : Prop :=
  ∀ (d : ℕ) (R : RdO d) (σ0 σ : Env d), R.Hyp b (R.bud b) → R.Inv σ0 → SamePers σ0 σ → σ.rounds = R.t + 1 →
    σ.pts R.t = toE R.play →
    R.RunsO (x R.L) σ (R.bud b) (fun σ' => σ'.sc sObs = R.obs ∧ σ'.rounds = σ.rounds ∧ σ'.draws = σ.draws ∧
      FrameC SR3 NScr AScr σ σ')

/-- **R1b, the dither block**: from the coins `D' t`, the last block of round `t`: `Γ_ζ` in `sZeta`, the coins of the
start of round `t + 1`, in the frame `SR1b`. -/
def SpecR1b (x : Layout → XCmdO) (b : BlkK) : Prop :=
  ∀ (d : ℕ) (R : RdO d) (σ0 σ : Env d), R.Hyp b (R.bud b) → R.Inv σ0 → SamePers σ0 σ →
    σ.draws = DO' d R.n R.δ R.r0 R.R0 R.a R.t →
    R.RunsO (x R.L) σ (R.bud b) (fun σ' => σ'.sc sZeta = R.gz ∧ σ'.rounds = σ.rounds ∧
      σ'.draws = Bit.Sched.blkStart d R.K0 R.pB (R.t + 1) 0 ∧ FrameC SR1b NScr AScr σ σ')

/-- **R5 to R15 in mode `run`**: from the draw, the dither, the reading and R2's data below `2^U`, BL-O's invariant
before round `t + 1` with the mode `stepO` gives (`modeO_succ`), within `C (W + E + U + 1)^k`. -/
def SpecTail (x : Layout → XCmdO) (b : BlkK) : Prop :=
  ∀ (d : ℕ) (R : RdO d) (st : St d) (U : ℕ) (σ0 σ : Env d),
    R.Hyp b (b.C * (R.W + R.E + U + 1) ^ b.k) → R.Inv σ0 → R.mo = .run st → R.PostT U st σ0 σ →
    R.RunsO (x R.L) σ (b.C * (R.W + R.E + U + 1) ^ b.k) R.Inv1

/-- The six statements of the sub-blocks. -/
def ProgR1a : Prop := ∃ (x : Layout → XCmdO) (b : BlkK), SpecR1a x b
def ProgR2 : Prop := ∃ (x : Layout → XCmdO) (b : BlkK), SpecR2 x b
def ProgOG : Prop := ∃ (x : Layout → XCmdO) (b : BlkK), SpecOG x b
def ProgR3 : Prop := ∃ (x : Layout → XCmdO) (b : BlkK), SpecR3 x b
def ProgR1b : Prop := ∃ (x : Layout → XCmdO) (b : BlkK), SpecR1b x b
def ProgTail : Prop := ∃ (x : Layout → XCmdO) (b : BlkK), SpecTail x b

/-! ## The round's code -/

/-- Segment A: R1a, then R2 in mode `run` (`sMode = 2`), the play of the frame centre otherwise. -/
def xAO (x1a x2 xog : Layout → XCmdO) (L : Layout) : XCmdO :=
  .seq (x1a L) (.seq (.base (toX (VL.sconst L sC2 2))) (xifSO L sMode sC2 (xog L) (x2 L)))

/-- Segment M: the play leaf on `aPl`. -/
def xMO (L : Layout) : XCmdO := .base (xplay L aPl)

/-- Segment B: R3, R1b, then the tail in mode `run`. -/
def xBO (x3 x1b xt : Layout → XCmdO) (L : Layout) : XCmdO :=
  .seq (x3 L) (.seq (x1b L) (.seq (.base (toX (VL.sconst L sC2 2))) (xifSO L sMode sC2 (.base .skip) (xt L))))

/-! ## BL-O's run, one round on -/

/-- The mode after round `t`: `stepO` on the mode, the draw, the dither and the reading of round `t`. -/
theorem modeO_succ (n : ℕ) (δ r0 R0 : ℚ) (a : Fin d → ℚ) (w : WorldO d) (t : ℕ) :
    modeO d n δ r0 R0 a w (t + 1) = stepO w.orc (cfgW d n δ r0 R0 a w) n (modeO d n δ r0 R0 a w t)
      (drawO d n δ r0 R0 w.cs t).1 (drawO d n δ r0 R0 w.cs t).2 (readO d n δ r0 R0 a w t) := rfl

/-- The modes `off` and `guard` stay. -/
theorem modeO_succ_og {n : ℕ} {δ r0 R0 : ℚ} {a : Fin d → ℚ} {w : WorldO d} {t : ℕ}
    (h : modeO d n δ r0 R0 a w t = .off ∨ modeO d n δ r0 R0 a w t = .guard) :
    modeO d n δ r0 R0 a w (t + 1) = modeO d n δ r0 R0 a w t := by
  rw [modeO_succ]
  rcases h with h | h <;> rw [h] <;> rfl

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

/-- R2's data pass through a frame that avoids `sPtN`, `sPtD`, `aWv`. -/
theorem RdO.RunDat.frame {R : RdO d} {U : ℕ} {st : St d} {σ σ' : Env d} {S N : ℕ → Prop} {Ar : ℕ → ℕ → Prop}
    (h : R.RunDat U st σ) (hF : FrameC S N Ar σ σ') (hN : ¬ S sPtN) (hD : ¬ S sPtD) (hW : ∀ k, ¬ Ar aWv k) :
    R.RunDat U st σ' := by
  obtain ⟨⟨pN, pD, h1, h2, h3, h4, h5, h6, h7⟩, h8⟩ := h
  exact ⟨⟨pN, pD, h1, h2, by rw [hF.2.1 _ hN, h3], by rw [hF.2.1 _ hD, h4], h5, h6, h7⟩,
    fun i => by rw [hF.2.2 _ _ (hW _), h8 i]⟩

/-- R2's data pass through `sc sC2 := v`. -/
theorem RdO.RunDat.setSc {R : RdO d} {U : ℕ} {st : St d} {σ : Env d} (h : R.RunDat U st σ) (v : ℝ) :
    R.RunDat U st (σ.setSc sC2 v) := by
  obtain ⟨⟨pN, pD, h1, h2, h3, h4, h5, h6, h7⟩, h8⟩ := h
  exact ⟨⟨pN, pD, h1, h2, by simp [h3], by simp [h4], h5, h6, h7⟩, fun i => by simp [h8 i]⟩

/-- R1a's facts pass through `sc sC2 := v`. -/
theorem RdO.PostR1a.setSc {R : RdO d} {σ0 σ : Env d} (h : R.PostR1a σ0 σ) (v : ℝ) :
    R.PostR1a σ0 (σ.setSc sC2 v) :=
  ⟨h.pers.trans (samePers_setSc (by decide) v), h.rounds, h.draws, fun i => by simp [h.gam i]⟩

set_option maxHeartbeats 1000000 in
/-- **The round from its six sub-blocks.** -/
theorem roundSpecO_of {x1a x2 xog x3 x1b xt : Layout → XCmdO} (S : SplitK) (h1a : SpecR1a x1a S.r1a)
    (h2 : SpecR2 x2 S.r2) (hog : SpecOG xog S.og) (h3 : SpecR3 x3 S.r3) (h1b : SpecR1b x1b S.r1b)
    (ht : SpecTail xt S.tl) :
    RoundSpecO (xAO x1a x2 xog) xMO (xBO x3 x1b xt) S.C S.k S.Cn S.kn S.nS S.nN S.nA := by
  intro d L w n δ r0 R0 a E0 E ℓa ℓ t σ hIn htn hL hRm hP hE hℓ hℓa hInv
  let R : RdO d := ⟨L, w, n, δ, r0, R0, a, E0, E, ℓa, ℓ, t⟩
  have hx : 1 ≤ R.W + R.E + 1 := by omega
  have eKr : S.C * (wU d n δ r0 R0 a + E + 1) ^ S.k = S.C * (R.W + R.E + 1) ^ S.k := rfl
  -- every block's hypotheses
  have hyp : ∀ (b : BlkK) (K : ℕ), b.Cn ≤ S.Cn → b.kn ≤ S.kn → b.nS ≤ S.nS → b.nN ≤ S.nN → b.nA ≤ S.nA →
      K ≤ S.C * (R.W + R.E + 1) ^ S.k → R.Hyp b K := fun b K hc hk hs hn ha hK =>
    ⟨hIn, htn, hL, ⟨hs.trans hRm.1, hn.trans hRm.2.1, ha.trans hRm.2.2⟩, hP,
      le_trans (blk_le (by omega) hc hk) hE, hK.trans hℓ, lt_of_le_of_lt hK hℓa⟩
  have kC : ∀ {i : ℕ}, i ≤ S.k → ∀ {C : ℕ}, C ≤ S.C → C * (R.W + R.E + 1) ^ i ≤ S.C * (R.W + R.E + 1) ^ S.k :=
    fun hi _ hc => blk_le hx hc hi
  have hk1 : 1 ≤ S.k := by unfold SplitK.k; omega
  have hC8 : 8 ≤ S.C := by unfold SplitK.C; omega
  have hℓ8 : 8 ≤ ℓ := by
    have : 8 * 1 ≤ S.C * (R.W + R.E + 1) ^ S.k := Nat.mul_le_mul hC8 (Nat.one_le_pow _ _ (by omega))
    rw [← eKr] at this; omega
  have hRℓ : 8 ≤ R.ℓ := hℓ8
  have hd1 : 1 ≤ d := hIn.hd
  have hdW : d + 3 ≤ S.C * (R.W + R.E + 1) ^ S.k := by
    have h1 : d ≤ R.W := by show d ≤ wU d n δ r0 R0 a; unfold wU; omega
    have h2 : R.W + R.E + 1 ≤ (R.W + R.E + 1) ^ S.k := by
      calc R.W + R.E + 1 = (R.W + R.E + 1) ^ 1 := (pow_one _).symm
        _ ≤ _ := pow_le_pow_one hx hk1
    have h3 : 8 * (R.W + R.E + 1) ^ S.k ≤ S.C * (R.W + R.E + 1) ^ S.k := Nat.mul_le_mul_right _ hC8
    omega
  have hNS : 64 ≤ L.NS := le_trans (by unfold SplitK.nS; omega) hRm.1
  have hNA : 32 ≤ L.NA := le_trans (by unfold SplitK.nA; omega) hRm.2.2
  have hsC2 : sC2 < L.NS := by show 35 < L.NS; omega
  have hsM : sMode < L.NS := by show 1 < L.NS; omega
  have haPl : aPl < L.NA := by show 28 < L.NA; omega
  have hInvR : R.Inv σ := hInv
  -- the constants of each block
  have b1a := hyp S.r1a (R.bud S.r1a) (by unfold SplitK.Cn; omega) (by unfold SplitK.kn; omega)
    (by unfold SplitK.nS; omega) (by unfold SplitK.nN; omega) (by unfold SplitK.nA; omega)
    (kC (by unfold SplitK.k; omega) (by unfold SplitK.C; omega))
  have b2 := hyp S.r2 (R.bud S.r2) (by unfold SplitK.Cn; omega) (by unfold SplitK.kn; omega)
    (by unfold SplitK.nS; omega) (by unfold SplitK.nN; omega) (by unfold SplitK.nA; omega)
    (kC (by unfold SplitK.k; omega) (by unfold SplitK.C; omega))
  have bog := hyp S.og (R.bud S.og) (by unfold SplitK.Cn; omega) (by unfold SplitK.kn; omega)
    (by unfold SplitK.nS; omega) (by unfold SplitK.nN; omega) (by unfold SplitK.nA; omega)
    (kC (by unfold SplitK.k; omega) (by unfold SplitK.C; omega))
  have b3 := hyp S.r3 (R.bud S.r3) (by unfold SplitK.Cn; omega) (by unfold SplitK.kn; omega)
    (by unfold SplitK.nS; omega) (by unfold SplitK.nN; omega) (by unfold SplitK.nA; omega)
    (kC (by unfold SplitK.k; omega) (by unfold SplitK.C; omega))
  have b1b := hyp S.r1b (R.bud S.r1b) (by unfold SplitK.Cn; omega) (by unfold SplitK.kn; omega)
    (by unfold SplitK.nS; omega) (by unfold SplitK.nN; omega) (by unfold SplitK.nA; omega)
    (kC (by unfold SplitK.k; omega) (by unfold SplitK.C; omega))
  have hTk : S.tl.C * (R.W + R.E + R.bud S.r2 + 1) ^ S.tl.k ≤ S.C * (R.W + R.E + 1) ^ S.k :=
    le_trans tail_le (kC (by unfold SplitK.k; omega) (by unfold SplitK.C; omega))
  have btl := hyp S.tl _ (by unfold SplitK.Cn; omega) (by unfold SplitK.kn; omega)
    (by unfold SplitK.nS; omega) (by unfold SplitK.nN; omega) (by unfold SplitK.nA; omega) hTk
  have sumA : R.bud S.r1a + (1 + (max (R.bud S.og) (R.bud S.r2) + 2)) ≤ S.C * (R.W + R.E + 1) ^ S.k := by
    have e1 : R.bud S.r1a + R.bud S.og + R.bud S.r2 + 3 ≤ (S.r1a.C + S.og.C + S.r2.C + 3) * (R.W + R.E + 1) ^ S.k := by
      have := blk_le hx (le_refl S.r1a.C) (show S.r1a.k ≤ S.k by unfold SplitK.k; omega)
      have := blk_le hx (le_refl S.og.C) (show S.og.k ≤ S.k by unfold SplitK.k; omega)
      have := blk_le hx (le_refl S.r2.C) (show S.r2.k ≤ S.k by unfold SplitK.k; omega)
      have := Nat.one_le_pow S.k _ hx
      simp only [RdO.bud] at *
      nlinarith
    have e2 : (S.r1a.C + S.og.C + S.r2.C + 3) * (R.W + R.E + 1) ^ S.k ≤ S.C * (R.W + R.E + 1) ^ S.k :=
      Nat.mul_le_mul_right _ (by unfold SplitK.C; omega)
    have := max_le_add_of_nonneg (a := R.bud S.og) (b := R.bud S.r2) (Nat.zero_le _) (Nat.zero_le _)
    omega
  have sumB : R.bud S.r3 + (R.bud S.r1b + (1 + (S.tl.C * (R.W + R.E + R.bud S.r2 + 1) ^ S.tl.k + 2))) ≤
      S.C * (R.W + R.E + 1) ^ S.k := by
    have t1 := le_trans tail_le (blk_le hx (le_refl (S.tl.C * (S.r2.C + 1) ^ S.tl.k))
      (show (S.r2.k + 1) * S.tl.k ≤ S.k by unfold SplitK.k; omega))
    have := blk_le hx (le_refl S.r3.C) (show S.r3.k ≤ S.k by unfold SplitK.k; omega)
    have := blk_le hx (le_refl S.r1b.C) (show S.r1b.k ≤ S.k by unfold SplitK.k; omega)
    have := Nat.one_le_pow S.k _ hx
    have e2 : (S.r3.C + S.r1b.C + S.tl.C * (S.r2.C + 1) ^ S.tl.k + 3) * (R.W + R.E + 1) ^ S.k ≤
        S.C * (R.W + R.E + 1) ^ S.k := Nat.mul_le_mul_right _ (by unfold SplitK.C; omega)
    simp only [RdO.bud] at *
    nlinarith
  -- segment A
  have segA : R.RunsO (xAO x1a x2 xog L) σ (S.C * (R.W + R.E + 1) ^ S.k)
      (fun σA => R.PostA σ σA ∧ ∀ st, R.mo = .run st → R.RunDat (R.bud S.r2) st σA) := by
    refine XVO.mono (XVO.seq (h1a d R σ b1a hInvR) fun σ1 P1 => ?_) sumA fun _ h => h
    refine XVO.seq (XVO.ofX (XV.sconst hL (x := sC2) hsC2 2 rfl
      (small_lt (by omega) (by norm_num)))) fun σ2 e2 => ?_
    subst e2
    have P2 := P1.setSc ((2 : ℚ) : ℝ)
    obtain ⟨hm3, hmlt⟩ := sMode_cases hInv P2.pers
    have hv2 : (σ1.setSc sC2 ((2 : ℚ) : ℝ)).sc sC2 = 2 := by simp
    refine XVO.ifS hL hsM hsC2 (small_lt (by omega) hm3) (by rw [hv2]; exact small_lt (by omega) (by norm_num))
      (fun hc => ?_) (fun hc => ?_)
    · rw [hv2] at hc
      have hmo := hmlt.1 hc
      refine XVO.mono (hog d R σ _ bog hInvR hmo P2) (le_max_left _ _) fun σA hA => ⟨hA, fun st hst => ?_⟩
      rcases hmo with h | h <;> cases hst.symm.trans h
    · rw [hv2] at hc
      have hrun : ∃ st, R.mo = .run st := by
        cases hmo : R.mo with
        | off => exact absurd (hmlt.2 (Or.inl hmo)) hc
        | guard => exact absurd (hmlt.2 (Or.inr hmo)) hc
        | run st => exact ⟨st, rfl⟩
      obtain ⟨st, hst⟩ := hrun
      refine XVO.mono (h2 d R st σ _ b2 hInvR hst P2) (le_max_right _ _) fun σA ⟨hA, hD⟩ => ⟨hA, fun st' hst' => ?_⟩
      rw [hst] at hst'
      cases hst'
      exact hD
  -- segment B, from the play's end
  have segB : ∀ σM : Env d, SamePers σ σM → σM.rounds = t + 1 → σM.draws = DO' d n δ r0 R0 a t →
      (∀ i : Fin d, σM.arr aGam i = R.Γ i) → σM.pts t = toE R.play →
      (∀ st, R.mo = .run st → R.RunDat (R.bud S.r2) st σM) →
      R.RunsO (xBO x3 x1b xt L) σM (S.C * (R.W + R.E + 1) ^ S.k) R.Inv1 := by
    intro σM pM rM dM gM tM datM
    refine XVO.mono (XVO.seq (h3 d R σ σM b3 hInvR pM rM tM) fun σ3 ⟨o3, r3, d3, F3⟩ => ?_) sumB fun _ h => h
    have p3 : SamePers σ σ3 := pM.trans (samePers_ofC F3 SR3_pers (fun _ h => h) AScr_pers)
    refine XVO.seq (h1b d R σ σ3 b1b hInvR p3 (by rw [d3, dM])) fun σ4 ⟨z4, r4, d4, F4⟩ => ?_
    have p4 : SamePers σ σ4 := p3.trans (samePers_ofC F4 SR1b_pers (fun _ h => h) AScr_pers)
    refine XVO.seq (XVO.ofX (XV.sconst hL (x := sC2) hsC2 2 rfl
      (small_lt (by omega) (by norm_num)))) fun σ5 e5 => ?_
    subst e5
    have p5 : SamePers σ (σ4.setSc sC2 ((2 : ℚ) : ℝ)) := p4.trans (samePers_setSc (by decide) _)
    obtain ⟨hm3, hmlt⟩ := sMode_cases hInv p5
    have hv2 : (σ4.setSc sC2 ((2 : ℚ) : ℝ)).sc sC2 = 2 := by simp
    have r5 : (σ4.setSc sC2 ((2 : ℚ) : ℝ)).rounds = t + 1 := by simp [r4, r3, rM]
    have d5 : (σ4.setSc sC2 ((2 : ℚ) : ℝ)).draws = Bit.Sched.blkStart d R.K0 R.pB (t + 1) 0 := by simp [d4]; rfl
    refine XVO.ifS hL hsM hsC2 (small_lt (by omega) hm3) (by rw [hv2]; exact small_lt (by omega) (by norm_num))
      (fun hc => ?_) (fun hc => ?_)
    · -- `off`, `guard`: the invariant one round on, the mode kept
      rw [hv2] at hc
      have hmo := hmlt.1 hc
      refine XVO.mono (XVO.ofX (XV.skip _)) (Nat.zero_le _) fun σ' e => ?_
      subst e
      have := BLInv.next hInv p5 r5 d5
      show BLOInv L n R.K0 E R.c (modeO d n δ r0 R0 a w (t + 1)) (t + 1) _
      rw [modeO_succ_og hmo]
      exact this
    · rw [hv2] at hc
      have hrun : ∃ st, R.mo = .run st := by
        cases hmo : R.mo with
        | off => exact absurd (hmlt.2 (Or.inl hmo)) hc
        | guard => exact absurd (hmlt.2 (Or.inr hmo)) hc
        | run st => exact ⟨st, rfl⟩
      obtain ⟨st, hst⟩ := hrun
      have g5 : ∀ i : Fin d, (σ4.setSc sC2 ((2 : ℚ) : ℝ)).arr aGam i = R.Γ i := fun i => by
        simp only [Env.setSc_arr]
        rw [F4.2.2 _ _ (fun h => by simp only [AScr, aGam] at h; omega),
          F3.2.2 _ _ (fun h => by simp only [AScr, aGam] at h; omega), gM i]
      have z5 : (σ4.setSc sC2 ((2 : ℚ) : ℝ)).sc sZeta = R.gz := by
        rw [Env.setSc_sc, ite_eq_right (by decide), z4]
      have o5 : (σ4.setSc sC2 ((2 : ℚ) : ℝ)).sc sObs = R.obs := by
        rw [Env.setSc_sc, ite_eq_right (by decide), F4.2.1 _ (fun h => by
          rcases h with h | h <;> simp only [sObs, sZeta, tR] at h <;> omega), o3]
      have dat5 : R.RunDat (R.bud S.r2) st (σ4.setSc sC2 ((2 : ℚ) : ℝ)) :=
        (((datM st hst).frame F3 (by simp [SR3, sPtN, sObs, tR]) (by simp [SR3, sPtD, sObs, tR])
          (fun k h => by simp only [AScr, aWv] at h; omega)).frame F4 (by simp [SR1b, sPtN, sZeta, tR])
          (by simp [SR1b, sPtD, sZeta, tR]) (fun k h => by simp only [AScr, aWv] at h; omega)).setSc _
      exact ht d R st (R.bud S.r2) σ _ btl hInvR hst ⟨p5, r5, d5, g5, z5, o5, dat5⟩
  -- the three segments
  refine XVO.mono segA (le_of_eq eKr.symm) fun σA ⟨hA, hD⟩ => ⟨hA.r1a.rounds, hA.r1a.draws, ?_⟩
  have hrA : σA.rounds = t := hA.r1a.rounds
  have hpt : Function.update σA.pts σA.rounds (ptE σA aPl) t = toE R.play := by
    rw [hrA, Function.update_self]; exact ptE_of_rep hA.pt
  refine XVO.mono (XVO.ofX (XV.play hL hd1 (v := aPl) haPl hA.ptb)) (by rw [eKr]; omega) fun σM e => ?_
  subst e
  exact ⟨by simp only [hrA], hA.r1a.draws, hpt, segB _ (hA.r1a.pers.trans (samePers_play _ _)) (by simp only [hrA])
    hA.r1a.draws hA.r1a.gam hpt hD⟩

/-- **`ProgRoundO` from the six statements of the sub-blocks.** -/
theorem progRoundO_of (h1a : ProgR1a) (h2 : ProgR2) (hog : ProgOG) (h3 : ProgR3) (h1b : ProgR1b) (ht : ProgTail) :
    ProgRoundO := by
  obtain ⟨x1a, b1a, h1a⟩ := h1a
  obtain ⟨x2, b2, h2⟩ := h2
  obtain ⟨xog, bog, hog⟩ := hog
  obtain ⟨x3, b3, h3⟩ := h3
  obtain ⟨x1b, b1b, h1b⟩ := h1b
  obtain ⟨xt, bt, ht⟩ := ht
  let S : SplitK := ⟨b1a, b2, bog, b3, b1b, bt⟩
  exact ⟨_, _, _, S.C, S.k, S.Cn, S.kn, S.nS, S.nN, S.nA, roundSpecO_of S h1a h2 hog h3 h1b ht⟩

end AdversarialBco.Unified.ProgO
