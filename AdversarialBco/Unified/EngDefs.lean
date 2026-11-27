/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.AsmMain
public import AdversarialBco.Unified.BudA
public import AdversarialBco.Bit.BLRoundIface
public import AdversarialBco.Unified.BLOParam

@[expose] public section

/-!
# Step 1 of SHADOW for BL-O's record: the pieces of `EngineRecO`

Bit/BLEngine.lean, Bit/BLRun.lean (`Track`, `PlayC`, `RoundC`) and Bit/BLRoundIface.lean (C1 / C2) for BL-O at a free
`k` (`k = kDel δ` in the run), with the constants of Theorem BUD at `k` (Unified/BudDefs.lean). The pieces:

* `TrackK`: `Track` with the bounds of BUD at `k`.
* Piece C, on one round of an abstract configuration `c` (no record): `RCHypO` (the hypotheses of `RoundC` for
  BL-O: the frame of the oracle in place of the rows, the case `PgGood` at P°'s radius, the noisy coupled
  observation `Y° = pt'(f(x') + ε + Z/2)/2 + 2(pt' - 1)/ε'` with `|ε|` within the no-clip bound); `C1O` (R5 to R10,
  `C1OutK`), `C2O` (the test call, the fire, line μ, with `apO` and ELL-O's contract `apSpecO`), `RoundCO`
  (`roundCO_of : C1O → C2O → RoundCO`); `PlayCO` (`|X' - X°| ≤ X̄`, reads neither the loss nor the gauge).
* On the record `recO`: `EngInvO` (`IND(t)` of Proposition SHADOW), `IndO` (`IND(t)` before the first decoupling
  on `Case ∩ Ω_ref ∩ E_bits ∩ NoClip`), `RoundBndO` (the shift and the regret of a round in `IND(t)`:
  `0 < r`, `tvB ≤ κ + κ |ε_t|` with `κ = kapO`, and the loss gap `regO/n`).

The assembly `engineRecO_of : IndO → RoundBndO → EngineRecO` is in Unified/EngAsm.lean. `IndO` follows from
`RoundCO` with the virtual-epoch facts of P°'s run on `RunW` (Bit/BLEngine.lean's `vmode`, `detHyp_of_good` over
Unified/WorldShadowRef.lean); `RoundBndO` from `PlayCO`, `GaugeBandO` and Lemma SHIFT with the noise
(`tau_shift`, Unified/BLOParam.lean).
-/

open MeasureTheory

namespace AdversarialBco.Unified.Eng

open AdversarialBco AdversarialBco.Poly AdversarialBco.Poly.Layer2 AdversarialBco.Bit.Cpl
open AdversarialBco.Unified.World AdversarialBco.Unified.BLO AdversarialBco.Unified.Asm
open AdversarialBco.Unified.BudK (BudOK RunCaseK poK parK)
open AdversarialBco.Bit.BLP (Par St Mode init rnd sqrtDn rndM rndV frob2 cV cM opN)
open AdversarialBco.BitRAM (toE)
open AdversarialBco.BitRAMO (clip)
open Matrix

variable {d : ℕ}

/-! ## `Track` at `k` -/

/-- `Track` of Bit/BLRun.lean between BL-O's state `st` and P°'s state `so` at the round `j` of the epoch, with the
bounds of Theorem BUD at `k`. -/
structure TrackK (d n k : ℕ) (st : St d) (so : Df2St d) (j : ℕ) : Prop where
  first : st.first = so.first
  mu : cV st.mu = so.mu
  S_eq : so.S = so.A * so.Aᵀ
  PS : so.P * so.S = 1
  hA : ∃ H : Matrix (Fin d) (Fin d) ℝ, cM st.A = (1 + H) * so.A ∧ opN H ≤ BudK.hTr d n k j
  hB : ∃ H : Matrix (Fin d) (Fin d) ℝ, cM st.B = (1 + H) * (so.P * so.A) ∧ opN H ≤ BudK.hTr d n k j
  errb : oNorm (cV st.b - so.b) ≤ j * BudK.eb d n k
  errk : |(st.k : ℝ) - so.k| ≤ j * BudK.ek d n k
  errG : oNorm (cV st.G - so.G) ≤ j * BudK.eg d n k
  errl : |(st.l : ℝ) - so.l| ≤ j * BudK.el d n k

/-! ## Piece C: one round of a configuration -/

/-- P°'s epoch context of piece C for BL-O: P°'s parameters at `δ_BL = deltaO d n k`, the body `kTh` at the position
of `c`, the routines `ap`. -/
noncomputable abbrev ctxO (K : Set (E d)) (c : CfgO d) (k : ℕ) (ap : ℕ → ApFun d) : Df2Ctx d :=
  df2CtxAtF d c.n (deltaO d c.n k) (kTh c.n (deltaO d c.n k) K c.S) ap

/-- BL-O's play of a round in mode `run st`. -/
noncomputable abbrev xO (orc : (Fin d → ℚ) → ℕ → Bool) (c : CfgO d) (st : St d) (ξ' : Fin d → ℚ) : E d :=
  toE (playPtO orc c (.run st) ξ')

/-- BL-O's reading of a round in mode `run st` with the loss `f` and the noise `ε`: `clip q ⌊2^p (f(x') + ε)⌋`. -/
noncomputable def obsO (orc : (Fin d → ℚ) → ℕ → Bool) (c : CfgO d) (st : St d) (ξ' : Fin d → ℚ) (f : E d → ℝ)
    (ε : ℝ) : ℤ :=
  clip c.qO ⌊(2 : ℝ) ^ c.par.p * (f (xO orc c st ξ') + ε)⌋

/-- BL-O's values of R5 YOBS to R9 INCR in mode `run` (`rv` of Bit/BLRoundIface.lean with the gauge play `ptO`; the
`let`s of `stepO`). -/
def rvO (orc : (Fin d → ℚ) → ℕ → Bool) (c : CfgO d) (st : St d) (ξ : Fin d → ℚ) (ζ : ℚ) (obs : ℤ) :
    Bit.BLP.RC.RV d :=
  let P := c.par
  let w := st.A *ᵥ ξ
  let X := XO c st ξ
  let pt := ptO orc c X
  let Y := rnd P.p (pt * ((obs : ℚ) / 2 ^ P.p + ζ) / 2 + 2 * (pt - 1) / P.eps)
  let cc := P.kapc * Y
  let a := 1 - cc
  let q := a + cc * (ξ ⬝ᵥ ξ)
  let s1 := sqrtDn P.p (1 / a)
  let s3 := sqrtDn P.p a
  let rq := sqrtDn P.p q
  let s2 := rnd P.p (cc / (s3 * rq * (s3 + rq)))
  let s4 := rnd P.p (cc / (s3 + rq))
  let A' := rndM P.p (s1 • st.A - s2 • vecMulVec w ξ)
  let B' := rndM P.p (s3 • st.B + s4 • vecMulVec (st.B *ᵥ ξ) ξ)
  let u := st.B *ᵥ ξ
  let v := st.Bᵀ *ᵥ st.mu
  let b' := st.b + rndV P.p (cc • ((u ⬝ᵥ st.mu) • u - st.B *ᵥ v))
  let k' := st.k + rnd P.p (cc / 2 * ((u ⬝ᵥ st.mu) ^ 2 - v ⬝ᵥ v))
  let g := rndV P.p ((Y * P.nu) • u)
  let G' := st.G + g
  let l' := st.l + rnd P.p (g ⬝ᵥ st.mu)
  ⟨Y, cc, a, q, s1, s3, rq, s2, s4, A', B', b', k', g, G', l'⟩

/-- The hypotheses of piece C for BL-O (those of `RoundC` with the oracle's frame in place of the rows and the noisy
coupled observation) other than the advice. `c` is BL-O's configuration at `parK d n k`, `n = c.n`; P°'s context is
`ctxO K c k ap`; `Z` is the coupling coordinate, `ε` the noise of the round. -/
structure RCHypO (K : Set (E d)) (orc : (Fin d → ℚ) → ℕ → Bool) (c : CfgO d) (k : ℕ) (ap : ℕ → ApFun d)
    (π : Df2Path d) (s : ℕ) (st : St d) (ξ' : Fin d → ℚ) (ζ' : ℚ) (Z ε : ℝ) (f : E d → ℝ) : Prop where
  hd : 1 ≤ d
  hn : 1 ≤ c.n
  par : c.par = parK d c.n k
  hc : RunCaseK d c.n k
  bud : BudOK d c.n k
  frame : FrameO K orc c
  pg : PgGood d K (poK d c.n k).R (some c.S)
  hs : s < c.n
  det : DetHyp (ctxO K c k ap) (deltaO d c.n k) π (s + 1)
  tau : (ctxO K c k ap).tau π (s + 1) = s
  track : TrackK d c.n k st ((ctxO K c k ap).st π s) s
  adm : AdmLoss K f
  g : ∀ y, π.g s y = f (pgMu c.S + pgOp c.S y) / 2
  xi : ∀ i, |(ξ' i : ℝ) - π.xi s i| ≤ 4 / 2 ^ (c.par.B / 2)
  zt : |(ζ' : ℝ) - Z / 2| ≤ 2 / 2 ^ (c.par.B / 2)
  nz : |ε| ≤ 3 + 4 * Real.sqrt (Real.log (14 * c.n * c.par.Ne))
  Y : (ctxO K c k ap).Y π s =
    (ptO orc c (XO c st ξ') : ℝ) * (f (xO orc c st ξ') + ε + Z / 2) / 2 +
      2 * ((ptO orc c (XO c st ξ') : ℝ) - 1) / (c.par.eps : ℝ)

/-- C1's conclusions on BL-O's values `r` of R5 to R9 (`C1Out` of Bit/BLRoundIface.lean at `k`). -/
structure C1OutK (d n k : ℕ) (P : Par) (st : St d) (ξ' : Fin d → ℚ) (r : Bit.BLP.RC.RV d) (c : Df2Ctx d)
    (π : Df2Path d) (s : ℕ) : Prop where
  ga : ¬ (r.a < 1 / 2 ∨ r.q < 1 / 2)
  gt : ¬ (2 * (P.Lam : ℚ) < frob2 r.B ∨ 2 * (P.Lam : ℚ) < frob2 r.A)
  hA : ∃ H : Matrix (Fin d) (Fin d) ℝ, cM r.A = (1 + H) * c.An π s ∧ opN H ≤ BudK.hTr d n k (s + 1)
  hB : ∃ H : Matrix (Fin d) (Fin d) ℝ, cM r.B = (1 + H) * (c.Pn π s * c.An π s) ∧ opN H ≤ BudK.hTr d n k (s + 1)
  errb : oNorm (cV r.b - c.bn π s) ≤ (s + 1) * BudK.eb d n k
  errk : |(r.k : ℝ) - c.kn π s| ≤ (s + 1) * BudK.ek d n k
  errG : oNorm (cV r.G - c.Gn π s) ≤ (s + 1) * BudK.eg d n k
  errl : |(r.l : ℝ) - c.ln π s| ≤ (s + 1) * BudK.el d n k
  eY : |(r.Y : ℝ) - c.Y π s| ≤ BudK.eY d n k
  eq : |(r.q : ℝ) - c.qq π s| ≤ BudK.Dq d n k
  ew : oNorm (cV (st.A *ᵥ ξ') - c.w π s) ≤ BudK.Du d n k

/-- The checked advice of the round (`advQO` of Unified/AsmRec.lean at P°'s state and observation). -/
noncomputable abbrev advC (K : Set (E d)) (orc : (Fin d → ℚ) → ℕ → Bool) (c : CfgO d) (k : ℕ) (ap : ℕ → ApFun d)
    (π : Df2Path d) (s : ℕ) (st : St d) (ξ' : Fin d → ℚ) (ζ' : ℚ) (ε : ℝ) (f : E d → ℝ) : Adv d :=
  advQO orc c c.n st ξ' ζ' (obsO orc c st ξ' f ε) (ctxO K c k ap).p ((ctxO K c k ap).st π s) (π.xi s)
    ((ctxO K c k ap).Y π s)

/-- The conclusion of piece C: both learners fire, or both continue with `Track` at `s + 1`. -/
def RoundOut (K : Set (E d)) (orc : (Fin d → ℚ) → ℕ → Bool) (c : CfgO d) (k : ℕ) (ap : ℕ → ApFun d)
    (π : Df2Path d) (s : ℕ) (st : St d) (ξ' : Fin d → ℚ) (ζ' : ℚ) (ε : ℝ) (f : E d → ℝ) : Prop :=
  (stepO orc c c.n (.run st) ξ' ζ' (obsO orc c st ξ' f ε) = .run (init c.par d) ∧ (ctxO K c k ap).fire π s) ∨
    ∃ st' : St d, stepO orc c c.n (.run st) ξ' ζ' (obsO orc c st ξ' f ε) = .run st' ∧ (ctxO K c k ap).cont π s ∧
      TrackK d c.n k st' ((ctxO K c k ap).st π (s + 1)) (s + 1)

/-- **C1 for BL-O** (R5 to R10, Lemmas TRACK, TRACK-2, DOM with E1 to E11): under `RCHypO`, BL-O's round values
satisfy `C1OutK`. -/
def C1O : Prop :=
  ∀ (d : ℕ) (K : Set (E d)) (orc : (Fin d → ℚ) → ℕ → Bool) (c : CfgO d) (k : ℕ) (ap : ℕ → ApFun d)
    (π : Df2Path d) (s : ℕ) (st : St d) (ξ' : Fin d → ℚ) (ζ' : ℚ) (Z ε : ℝ) (f : E d → ℝ),
    RCHypO K orc c k ap π s st ξ' ζ' Z ε f →
    C1OutK d c.n k c.par st ξ' (rvO orc c st ξ' ζ' (obsO orc c st ξ' f ε)) (ctxO K c k ap) π s

/-- **C2 for BL-O** (the test call, the fire, line μ; Lemmas SEL, VAL, GUARD with E12 to E16, E18, ELL-O's contract
`apSpecO` on the region `QKs (1 - ε')⁻¹ ∩ regionC`): under `RCHypO`, the advice and C1's conclusions, both fire or
both continue with `Track` at `s + 1`. -/
def C2O : Prop :=
  ∀ (d : ℕ) (K : Set (E d)) (orc : (Fin d → ℚ) → ℕ → Bool) (c : CfgO d) (k : ℕ) (ap : ℕ → ApFun d)
    (π : Df2Path d) (s : ℕ) (st : St d) (ξ' : Fin d → ℚ) (ζ' : ℚ) (Z ε : ℝ) (f : E d → ℝ),
    RCHypO K orc c k ap π s st ξ' ζ' Z ε f →
    ap s = apAdv (advC K orc c k ap π s st ξ' ζ' ε f) →
    C1OutK d c.n k c.par st ξ' (rvO orc c st ξ' ζ' (obsO orc c st ξ' f ε)) (ctxO K c k ap) π s →
    RoundOut K orc c k ap π s st ξ' ζ' ε f

/-- **Piece C for BL-O, the round**: under `RCHypO` and the advice, both fire or both continue with `Track`. -/
def RoundCO : Prop :=
  ∀ (d : ℕ) (K : Set (E d)) (orc : (Fin d → ℚ) → ℕ → Bool) (c : CfgO d) (k : ℕ) (ap : ℕ → ApFun d)
    (π : Df2Path d) (s : ℕ) (st : St d) (ξ' : Fin d → ℚ) (ζ' : ℚ) (Z ε : ℝ) (f : E d → ℝ),
    RCHypO K orc c k ap π s st ξ' ζ' Z ε f →
    ap s = apAdv (advC K orc c k ap π s st ξ' ζ' ε f) →
    RoundOut K orc c k ap π s st ξ' ζ' ε f

theorem roundCO_of (h1 : C1O) (h2 : C2O) : RoundCO := fun d K orc c k ap π s st ξ' ζ' Z ε f H hap =>
  h2 d K orc c k ap π s st ξ' ζ' Z ε f H hap (h1 d K orc c k ap π s st ξ' ζ' Z ε f H)

/-- **Piece C for BL-O, the play** (`PlayC` at `k`; Lemma TRACK-2 and E6): BL-O's point `X'` is within `X̄` of P°'s
`X°_s`. It reads neither the loss, the observation, the gauge nor the routines of the round. -/
def PlayCO : Prop :=
  ∀ (d : ℕ) (K : Set (E d)) (c : CfgO d) (k : ℕ) (ap : ℕ → ApFun d) (π : Df2Path d) (s : ℕ) (st : St d)
    (ξ' : Fin d → ℚ),
    1 ≤ d → 1 ≤ c.n → c.par = parK d c.n k → RunCaseK d c.n k → BudOK d c.n k →
    PgGood d K (poK d c.n k).R (some c.S) → s < c.n →
    DetHyp (ctxO K c k ap) (deltaO d c.n k) π (s + 1) → (ctxO K c k ap).tau π (s + 1) = s →
    TrackK d c.n k st ((ctxO K c k ap).st π s) s →
    (∀ i, |(ξ' i : ℝ) - π.xi s i| ≤ 4 / 2 ^ (c.par.B / 2)) →
    oNorm (cV (XO c st ξ') - (ctxO K c k ap).X π s) ≤ BudK.Xb d c.n k

/-! ## The induction and the round bounds on the record -/

section Rec

variable {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} {K : Set (E d)} {coin : Ω → ℕ → Bool}
  {loss : ℕ → Ω → E d → ℝ} {noise : ℕ → Ω → ℝ}

/-- **`IND(t)`** (Proposition SHADOW) on BL-O's record: before round `t` both learners are in mode `run` on one
virtual epoch of P° started before a round `a0` at a fresh mode and continued through its rounds `< t - a0`, with
`TrackK` between BL-O's state and P°'s. -/
def EngInvO (n : ℕ) (δ r0 R0 : ℚ) (a : Fin d → ℚ) (orc : (Fin d → ℚ) → ℕ → Bool)
    (h : NoisyAdv K n (DO d n δ r0 R0 a) (DO' d n δ r0 R0 a) μ coin loss noise) (hK : Convex ℝ K)
    (ω : Ω × (ℕ → ℝ)) (t : ℕ) : Prop :=
  ∃ a0 s : ℕ, ∃ st : St d, a0 + s = t ∧
    (recO n δ r0 R0 a orc h hK).mode (dBL d n δ) a0 ω = .run (df2Init (poO d n δ) d) ∧
    (∀ u < s, ((recO n δ r0 R0 a orc h hK).ctx (dBL d n δ) a0 ω).cont
      ((recO n δ r0 R0 a orc h hK).path (dBL d n δ) a0 ω) u) ∧
    modeO d n δ r0 R0 a (envWorld orc coin loss noise ω.1) t = .run st ∧
    TrackK d n (kDel δ) st (((recO n δ r0 R0 a orc h hK).ctx (dBL d n δ) a0 ω).st
      ((recO n δ r0 R0 a orc h hK).path (dBL d n δ) a0 ω) s) s

end Rec

/-- **`IND(t)` before the first decoupling** on `Case ∩ Ω_ref ∩ E_bits ∩ NoClip`, at every round `t ≤ n`. -/
def IndO : Prop :=
  ∀ (d n : ℕ) (δ r0 R0 : ℚ) (a : Fin d → ℚ) (K : Set (E d)) (orc : (Fin d → ℚ) → ℕ → Bool)
    (hI : InpU n δ r0 R0 a K orc), RunCaseO d n δ →
    ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) (coin : Ω → ℕ → Bool) (loss : ℕ → Ω → E d → ℝ)
      (noise : ℕ → Ω → ℝ) (h : NoisyAdv K n (DO d n δ r0 R0 a) (DO' d n δ r0 R0 a) μ coin loss noise)
      (ω : Ω × (ℕ → ℝ)),
      (recO n δ r0 R0 a orc h hI.convex).Case (dBL d n δ) ω → (recO n δ r0 R0 a orc h hI.convex).Good (dBL d n δ) ω →
      ω ∈ (recO n δ r0 R0 a orc h hI.convex).bits →
      ∀ t ≤ n, (∀ u < t, ¬ (recO n δ r0 R0 a orc h hI.convex).D (dBL d n δ) u ω) →
        EngInvO n δ r0 R0 a orc h hI.convex ω t

/-- **The shift and the regret of a round** in `IND(t)` on `Case ∩ Ω_ref ∩ E_bits ∩ NoClip`: `r > 0` and
`tvB(m, r) ≤ κ + κ |ε_t|` with `κ = kapO` (Lemma SHIFT with the noise, `tau_shift`), and BL-O's loss exceeds P°'s by
at most `regO/n`. -/
def RoundBndO : Prop :=
  ∀ (d n : ℕ) (δ r0 R0 : ℚ) (a : Fin d → ℚ) (K : Set (E d)) (orc : (Fin d → ℚ) → ℕ → Bool)
    (hI : InpU n δ r0 R0 a K orc), RunCaseO d n δ →
    ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) (coin : Ω → ℕ → Bool) (loss : ℕ → Ω → E d → ℝ)
      (noise : ℕ → Ω → ℝ) (h : NoisyAdv K n (DO d n δ r0 R0 a) (DO' d n δ r0 R0 a) μ coin loss noise)
      (ω : Ω × (ℕ → ℝ)),
      (recO n δ r0 R0 a orc h hI.convex).Case (dBL d n δ) ω → (recO n δ r0 R0 a orc h hI.convex).Good (dBL d n δ) ω →
      ω ∈ (recO n δ r0 R0 a orc h hI.convex).bits →
      ∀ t < n, EngInvO n δ r0 R0 a orc h hI.convex ω t →
        (0 < ((recO n δ r0 R0 a orc h hI.convex).shR (dBL d n δ) t ω).2 ∧
          Bit.Cpl.tvB ((recO n δ r0 R0 a orc h hI.convex).shR (dBL d n δ) t ω).1
              ((recO n δ r0 R0 a orc h hI.convex).shR (dBL d n δ) t ω).2 ≤
            BudK.kapO d n (kDel δ) + BudK.kapO d n (kDel δ) * |(extO n δ r0 R0 a h).nz t ω|) ∧
        (recO n δ r0 R0 a orc h hI.convex).loss ω t ((recO n δ r0 R0 a orc h hI.convex).play t ω) ≤
          (recO n δ r0 R0 a orc h hI.convex).loss ω t ((recO n δ r0 R0 a orc h hI.convex).refPlay (dBL d n δ) t ω) +
            BudK.regO d n (kDel δ) / n

end AdversarialBco.Unified.Eng
