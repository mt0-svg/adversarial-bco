/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.UW.BudA
public import AdversarialBco.UW.BudEncOK
public import AdversarialBco.UW.DetRound
public import AdversarialBco.Unified.EngDefs

@[expose] public section

/-!
# Step 1 of SHADOW for BL-OW's record: the pieces of `EngineRecUW`

Unified/EngDefs.lean for BL-OW: Theorem U's pieces C and D with BL-OW's round
(`stepOW`, R5w), PARAM-W's record `parOW d n δ`, P° of Theorem UW at PARAM-W's reference `refW d n δ` on the weighted
path, and the constants of Theorem BUD-W at `rW d n δ = regW d n k_δ (refW d n δ)`:

* `TrackW`: `Track` with the bounds of BUD-W.
* Piece C, on one round of an abstract configuration: `RCHypOW` (the hypotheses of `RCHypO` with P°'s context
  `ctxOW` at T4U, DET with sure ranges `DetHypW` on the weighted path, event (a) at the level `EvGW`, and the
  coupled observation weighted: `Y° = φ(|ξ|²) clip(Ỹ, y0)` with `Ỹ` BL-OW's exact observation `YcO`); `C1OW` (R5,
  R5w to R10, `C1OutW`), `C2OW` (the test call, the fire, line μ), `RoundCOW`; `PlayCOW`.
* On the record `recUW`: `EngInvOW`, `IndOW`, `RoundBndOW`.
-/

open MeasureTheory

namespace AdversarialBco.UW.Eng

open AdversarialBco AdversarialBco.Poly AdversarialBco.Poly.Layer2 AdversarialBco.Bit.Cpl
open AdversarialBco.Unified.World AdversarialBco.Unified.BLO AdversarialBco.Unified.Asm
open AdversarialBco.Unified.Eng (xO obsO)
open AdversarialBco.UW AdversarialBco.UW.BudW AdversarialBco.UW.BLOW
open AdversarialBco.Bit.BLP (Par St Mode init rnd sqrtDn rndM rndV frob2 cV cM opN)
open AdversarialBco.BitRAM (toE)
open Matrix

variable {d : ℕ}

/-- The constants of Theorem BUD-W at the input: `regW` at `k_δ` and PARAM-W's reference. -/
noncomputable abbrev rW (d n : ℕ) (δ : ℚ) : RegW := regW d n (kDel δ) (refW d n δ)

/-! ## `Track` at `δ` -/

/-- `Track` between BL-OW's state `st` and P°'s state `so` at the round `j` of the epoch, with the bounds of
Theorem BUD-W at `δ`. -/
structure TrackW (d n : ℕ) (δ : ℚ) (st : St d) (so : Df2St d) (j : ℕ) : Prop where
  first : st.first = so.first
  mu : cV st.mu = so.mu
  S_eq : so.S = so.A * so.Aᵀ
  PS : so.P * so.S = 1
  hA : ∃ H : Matrix (Fin d) (Fin d) ℝ, cM st.A = (1 + H) * so.A ∧ opN H ≤ (rW d n δ).hTr j
  hB : ∃ H : Matrix (Fin d) (Fin d) ℝ, cM st.B = (1 + H) * (so.P * so.A) ∧ opN H ≤ (rW d n δ).hTr j
  errb : oNorm (cV st.b - so.b) ≤ j * (rW d n δ).eb
  errk : |(st.k : ℝ) - so.k| ≤ j * (rW d n δ).ek
  errG : oNorm (cV st.G - so.G) ≤ j * (rW d n δ).eg
  errl : |(st.l : ℝ) - so.l| ≤ j * (rW d n δ).el

/-! ## Piece C: one round of a configuration -/

/-- P°'s epoch context of piece C for BL-OW: T4U at PARAM-W's scaling, the body `kTh` at the level `δ_c` and the
position of `c`, the routines `ap`. -/
noncomputable abbrev ctxOW (K : Set (E d)) (c : CfgO d) (δ : ℚ) (ap : ℕ → ApFun d) : Df2Ctx d :=
  ⟨poW d c.n δ, c.n, kTh c.n (refW d c.n δ).δc K c.S, ap⟩

/-- The weighted path of the epoch at PARAM-W's thresholds. -/
noncomputable abbrev pwOW (K : Set (E d)) (c : CfgO d) (δ : ℚ) (ap : ℕ → ApFun d) (π : Df2Path d) : Df2Path d :=
  pathW (ctxOW K c δ ap) (refW d c.n δ).b0 (refW d c.n δ).y0 π

/-- BL-OW's exact unweighted observation of a coupled round: `pt' (f(x') + ε + Z/2)/2 + 2 (pt' - 1)/ε'`. -/
noncomputable def YcO (orc : (Fin d → ℚ) → ℕ → Bool) (c : CfgO d) (st : St d) (ξ' : Fin d → ℚ) (Z ε : ℝ)
    (f : E d → ℝ) : ℝ :=
  (ptO orc c (XO c st ξ') : ℝ) * (f (xO orc c st ξ') + ε + Z / 2) / 2 +
    2 * ((ptO orc c (XO c st ξ') : ℝ) - 1) / (c.par.eps : ℝ)

/-- BL-OW's values of R5 YOBS, R5w and R7 FACTOR to R9 INCR in mode `run` (the `let`s of `stepOW`); the field `Y` is
the weighted observation `Y'^w`. -/
def rvOW (b0 y0 : ℚ) (orc : (Fin d → ℚ) → ℕ → Bool) (c : CfgO d) (st : St d) (ξ : Fin d → ℚ) (ζ : ℚ) (obs : ℤ) :
    Bit.BLP.RC.RV d :=
  let P := c.par
  let w := st.A *ᵥ ξ
  let X := XO c st ξ
  let pt := ptO orc c X
  let Y0 := rnd P.p (pt * ((obs : ℚ) / 2 ^ P.p + ζ) / 2 + 2 * (pt - 1) / P.eps)
  let Y := ywQ P.p b0 y0 ξ Y0
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

/-- The hypotheses of piece C for BL-OW other than the advice. `c` is BL-OW's configuration at `parOW d n δ`,
`n = c.n`; P°'s context is `ctxOW K c δ ap`, its weighted path `pwOW K c δ ap π`; `Z` is the coupling coordinate,
`ε` the noise of the round. -/
structure RCHypOW (K : Set (E d)) (orc : (Fin d → ℚ) → ℕ → Bool) (c : CfgO d) (δ : ℚ) (ap : ℕ → ApFun d)
    (π : Df2Path d) (s : ℕ) (st : St d) (ξ' : Fin d → ℚ) (ζ' : ℚ) (Z ε : ℝ) (f : E d → ℝ) : Prop where
  hd : 1 ≤ d
  hn : 1 ≤ c.n
  hδ0 : 0 < δ
  hδ1 : δ < 1
  par : c.par = parOW d c.n δ
  hc : RunCaseUW d c.n δ
  reg : RegimeW d c.n (refW d c.n δ)
  bud : BudOKW d c.n (kDel δ) (refW d c.n δ)
  enc : EncOKW d c.n δ
  frame : FrameO K orc c
  pg : PgGood d K (poW d c.n δ).R (some c.S)
  hs : s < c.n
  det : DetHypW (ctxOW K c δ ap) (pwOW K c δ ap π) (s + 1) (refW d c.n δ)
  tau : (ctxOW K c δ ap).tau (pwOW K c δ ap π) (s + 1) = s
  evG : EvGW (ctxOW K c δ ap) π (pwOW K c δ ap π) (lgW c.n (refW d c.n δ).δc) (leW (refW d c.n δ).δc) (s + 1)
  track : TrackW d c.n δ st ((ctxOW K c δ ap).st (pwOW K c δ ap π) s) s
  adm : AdmLoss K f
  g : ∀ y, π.g s y = f (pgMu c.S + pgOp c.S y) / 2
  xi : ∀ i, |(ξ' i : ℝ) - π.xi s i| ≤ 4 / 2 ^ (c.par.B / 2)
  zt : |(ζ' : ℝ) - Z / 2| ≤ 2 / 2 ^ (c.par.B / 2)
  nz : |ε| ≤ 3 + 4 * Real.sqrt (Real.log (14 * c.n * c.par.Ne))
  Y : (ctxOW K c δ ap).Y (pwOW K c δ ap π) s =
    obsW (refW d c.n δ).b0 (refW d c.n δ).y0 (π.xi s) (YcO orc c st ξ' Z ε f)

/-- C1's conclusions on BL-OW's values `r` of R5 to R9 (`C1OutK` with the bounds of BUD-W; the bound on `A' ξ'`
reads the weighted rounds only, Lemma WR). -/
structure C1OutW (d n : ℕ) (δ : ℚ) (P : Par) (st : St d) (ξ' : Fin d → ℚ) (r : Bit.BLP.RC.RV d) (c : Df2Ctx d)
    (π : Df2Path d) (s : ℕ) : Prop where
  ga : ¬ (r.a < 1 / 2 ∨ r.q < 1 / 2)
  gt : ¬ (2 * (P.Lam : ℚ) < frob2 r.B ∨ 2 * (P.Lam : ℚ) < frob2 r.A)
  hA : ∃ H : Matrix (Fin d) (Fin d) ℝ, cM r.A = (1 + H) * c.An π s ∧ opN H ≤ (rW d n δ).hTr (s + 1)
  hB : ∃ H : Matrix (Fin d) (Fin d) ℝ, cM r.B = (1 + H) * (c.Pn π s * c.An π s) ∧ opN H ≤ (rW d n δ).hTr (s + 1)
  errb : oNorm (cV r.b - c.bn π s) ≤ (s + 1) * (rW d n δ).eb
  errk : |(r.k : ℝ) - c.kn π s| ≤ (s + 1) * (rW d n δ).ek
  errG : oNorm (cV r.G - c.Gn π s) ≤ (s + 1) * (rW d n δ).eg
  errl : |(r.l : ℝ) - c.ln π s| ≤ (s + 1) * (rW d n δ).el
  eY : |(r.Y : ℝ) - c.Y π s| ≤ (rW d n δ).eYw
  eq : |(r.q : ℝ) - c.qq π s| ≤ (rW d n δ).Dq
  ew : ((r.Y : ℝ) ≠ 0 ∨ c.Y π s ≠ 0) → oNorm (cV (st.A *ᵥ ξ') - c.w π s) ≤ (rW d n δ).Duw

/-- **C1 for BL-OW** (R5, R5w to R10; Lemmas E2w, WR, errors-W, TRACK, DOM-W): under `RCHypOW`, BL-OW's round
values satisfy `C1OutW`. -/
def C1OW : Prop :=
  ∀ (d : ℕ) (K : Set (E d)) (orc : (Fin d → ℚ) → ℕ → Bool) (c : CfgO d) (δ : ℚ) (ap : ℕ → ApFun d)
    (π : Df2Path d) (s : ℕ) (st : St d) (ξ' : Fin d → ℚ) (ζ' : ℚ) (Z ε : ℝ) (f : E d → ℝ),
    RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f →
    C1OutW d c.n δ c.par st ξ' (rvOW (b0OW d c.n δ) (y0OW d c.n δ) orc c st ξ' ζ' (obsO orc c st ξ' f ε))
      (ctxOW K c δ ap) (pwOW K c δ ap π) s

/-- The checked advice of the round (`advQOW` at P°'s state on the weighted path, its draw and its unweighted
observation, which on a coupled round is BL-OW's exact one). -/
noncomputable abbrev advCW (K : Set (E d)) (orc : (Fin d → ℚ) → ℕ → Bool) (c : CfgO d) (δ : ℚ) (ap : ℕ → ApFun d)
    (π : Df2Path d) (s : ℕ) (st : St d) (ξ' : Fin d → ℚ) (ζ' : ℚ) (Z ε : ℝ) (f : E d → ℝ) : Adv d :=
  advQOW (b0OW d c.n δ) (y0OW d c.n δ) orc c c.n st ξ' ζ' (obsO orc c st ξ' f ε) (ctxOW K c δ ap).p
    ((ctxOW K c δ ap).st (pwOW K c δ ap π) s) (π.xi s) (YcO orc c st ξ' Z ε f)

/-- The conclusion of piece C: both learners fire, or both continue with `TrackW` at `s + 1`. -/
def RoundOutW (K : Set (E d)) (orc : (Fin d → ℚ) → ℕ → Bool) (c : CfgO d) (δ : ℚ) (ap : ℕ → ApFun d)
    (π : Df2Path d) (s : ℕ) (st : St d) (ξ' : Fin d → ℚ) (ζ' : ℚ) (ε : ℝ) (f : E d → ℝ) : Prop :=
  (stepOW (b0OW d c.n δ) (y0OW d c.n δ) orc c c.n (.run st) ξ' ζ' (obsO orc c st ξ' f ε) = .run (init c.par d) ∧
      (ctxOW K c δ ap).fire (pwOW K c δ ap π) s) ∨
    ∃ st' : St d, stepOW (b0OW d c.n δ) (y0OW d c.n δ) orc c c.n (.run st) ξ' ζ' (obsO orc c st ξ' f ε) = .run st' ∧
      (ctxOW K c δ ap).cont (pwOW K c δ ap π) s ∧
      TrackW d c.n δ st' ((ctxOW K c δ ap).st (pwOW K c δ ap π) (s + 1)) (s + 1)

/-- **C2 for BL-OW** (the test call, the fire, line μ; Lemmas SEL, VAL, GUARD-W with E12 to E16w, E18w): under
`RCHypOW`, the advice and C1's conclusions, both fire or both continue with `TrackW` at `s + 1`. -/
def C2OW : Prop :=
  ∀ (d : ℕ) (K : Set (E d)) (orc : (Fin d → ℚ) → ℕ → Bool) (c : CfgO d) (δ : ℚ) (ap : ℕ → ApFun d)
    (π : Df2Path d) (s : ℕ) (st : St d) (ξ' : Fin d → ℚ) (ζ' : ℚ) (Z ε : ℝ) (f : E d → ℝ),
    RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f →
    ap s = apAdv (advCW K orc c δ ap π s st ξ' ζ' Z ε f) →
    C1OutW d c.n δ c.par st ξ' (rvOW (b0OW d c.n δ) (y0OW d c.n δ) orc c st ξ' ζ' (obsO orc c st ξ' f ε))
      (ctxOW K c δ ap) (pwOW K c δ ap π) s →
    RoundOutW K orc c δ ap π s st ξ' ζ' ε f

/-- **Piece C for BL-OW, the round**. -/
def RoundCOW : Prop :=
  ∀ (d : ℕ) (K : Set (E d)) (orc : (Fin d → ℚ) → ℕ → Bool) (c : CfgO d) (δ : ℚ) (ap : ℕ → ApFun d)
    (π : Df2Path d) (s : ℕ) (st : St d) (ξ' : Fin d → ℚ) (ζ' : ℚ) (Z ε : ℝ) (f : E d → ℝ),
    RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f →
    ap s = apAdv (advCW K orc c δ ap π s st ξ' ζ' Z ε f) →
    RoundOutW K orc c δ ap π s st ξ' ζ' ε f

theorem roundCOW_of (h1 : C1OW) (h2 : C2OW) : RoundCOW := fun d K orc c δ ap π s st ξ' ζ' Z ε f H hap =>
  h2 d K orc c δ ap π s st ξ' ζ' Z ε f H hap (h1 d K orc c δ ap π s st ξ' ζ' Z ε f H)

/-- **Piece C for BL-OW, the play** (`PlayCO` at BUD-W; Lemma TRACK-2 and E6): BL-OW's point `X'` is within `X̄` of
P°'s `X°_s` on the weighted path. -/
def PlayCOW : Prop :=
  ∀ (d : ℕ) (K : Set (E d)) (c : CfgO d) (δ : ℚ) (ap : ℕ → ApFun d) (π : Df2Path d) (s : ℕ) (st : St d)
    (ξ' : Fin d → ℚ),
    1 ≤ d → 1 ≤ c.n → c.par = parOW d c.n δ → RunCaseUW d c.n δ → RegimeW d c.n (refW d c.n δ) →
    BudOKW d c.n (kDel δ) (refW d c.n δ) → EncOKW d c.n δ →
    PgGood d K (poW d c.n δ).R (some c.S) → s < c.n →
    DetHypW (ctxOW K c δ ap) (pwOW K c δ ap π) (s + 1) (refW d c.n δ) →
    (ctxOW K c δ ap).tau (pwOW K c δ ap π) (s + 1) = s →
    EvGW (ctxOW K c δ ap) π (pwOW K c δ ap π) (lgW c.n (refW d c.n δ).δc) (leW (refW d c.n δ).δc) (s + 1) →
    TrackW d c.n δ st ((ctxOW K c δ ap).st (pwOW K c δ ap π) s) s →
    (∀ i, |(ξ' i : ℝ) - π.xi s i| ≤ 4 / 2 ^ (c.par.B / 2)) →
    oNorm (cV (XO c st ξ') - (ctxOW K c δ ap).X (pwOW K c δ ap π) s) ≤ (rW d c.n δ).Xb

end AdversarialBco.UW.Eng
