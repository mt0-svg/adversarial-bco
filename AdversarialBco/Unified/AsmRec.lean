/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.BLOSpec
public import AdversarialBco.Unified.WorldShadowRef
public import AdversarialBco.Bit.BLRun

@[expose] public section

/-!
# BL-O's run record on the extension

The record `recO` (`RunW` of Unified/WorldCore.lean) of BL-O (Unified/BLOSpec.lean) on the coupled world `extO` of an
environment of `TheoremUnified` with BL-O's windows `DO`, `DO'`: the extension `extW` of Unified/WorldExt.lean with
`P0O` prologue blocks of `2 B` coins, `B` the block length of `parO`. It is Bit/BLRun.lean's `blRun` with BL's pure
function replaced by BL-O's and the world `WΩ` by the extension:

* the losses: the environment's (`lossProcE`);
* the position: BL-O's on the environment's coins (`recPos`), the plays: BL-O's on the environment's world (`recPlay`);
* the shift `shO` (the paper's coupling with the reference): `r = pt'/pt°` and
  `m = (r - 1) ε_t + (pt' f(x') - pt° f°(x°) + 4 (pt' - 1)/ε' - 4 (pt° - 1)/ε)/pt°`, with BL-O's gauge play `ptO` in
  place of BL's and the noise `ε_t` of the world; `(0, 1)` unless both learners are in mode `run` and `t < n`;
* the advice `advO` (Lemmas SEL and VAL): `advQ` of Bit/BLRun.lean with BL-O's test (`testO`, the lines R5 to R12
  of `stepO`, the calls by `apO`) and BL-O's step;
* the soundness event `bits = E_bits ∩ NoClip`: BL-O's draws of the rounds `t < n` within `e_ξ`, `e_ζ` of the world's
  draw and half its dither coordinate (`EbitsO`, BL's E1 at the block length of `parO`), and the noises of the rounds
  `t < n` within `3 + 4 (ln(14 n N_e))^{1/2}` (`NoClipO`), on which the clipped reading of UNI-OBS (`ObsClipO`) does not
  act, since the losses lie in `[0, 1]` at the plays;
* the coupling `coupMax`.

`RunCaseO d n δ`: `ε ≤ 1/4` at `poO d n δ = df2oPar d n δ_BL`, `δ_BL = dBL d n δ = 2^{-19-k_δ}/(d n)³`; the assembly
uses SHADOW there and the trivial bound `Reg ≤ n` off it.
-/

open MeasureTheory ProbabilityTheory

namespace AdversarialBco.Unified.Asm

open AdversarialBco AdversarialBco.Poly AdversarialBco.Poly.Layer2 AdversarialBco.Bit.Cpl
open AdversarialBco.Unified.World AdversarialBco.Unified.BLO
open AdversarialBco.Bit.BLP (St Mode refX refPt refTest selT muOf cV rnd sqrtDn rndM rndV frob2 LT rB CallQ)
open AdversarialBco.BitRAM (toE)
open AdversarialBco.Poly.Conj1 (fL)
open Matrix

variable {d : ℕ}

/-! ## The input and BL-O's confidence -/

/-- An input of `TheoremUnified`: `d, n ≥ 1`, `0 < δ < 1`, `0 < r0 ≤ R0`, `K` compact and convex between the balls
`B̄(a, r0)` and `B̄(a, R0)`, and `orc` a weak membership oracle of `K`. -/
structure InpU (n : ℕ) (δ r0 R0 : ℚ) (a : Fin d → ℚ) (K : Set (E d)) (orc : (Fin d → ℚ) → ℕ → Bool) :
    Prop where
  hd : 1 ≤ d
  hn : 1 ≤ n
  hδ0 : 0 < δ
  hδ1 : δ < 1
  hr0 : 0 < r0
  hrR : r0 ≤ R0
  compact : IsCompact K
  convex : Convex ℝ K
  ball_in : Metric.closedBall (toE a) (r0 : ℝ) ⊆ K
  ball_out : K ⊆ Metric.closedBall (toE a) (R0 : ℝ)
  orc : BitRAMO.WeakMemOracle K orc

/-- BL-O's confidence `δ_BL = 2^{-19-k_δ}/(d n)³` at the input `δ`. -/
noncomputable def dBL (d n : ℕ) (δ : ℚ) : ℝ := deltaO d n (kDel δ)

/-- P°'s parameters at BL-O's confidence. -/
noncomputable def poO (d n : ℕ) (δ : ℚ) : Df2OPar := df2oPar d n (dBL d n δ)

/-- The case in which the assembly uses SHADOW: `ε ≤ 1/4` at `poO d n δ`. -/
def RunCaseO (d n : ℕ) (δ : ℚ) : Prop := (poO d n δ).eps ≤ 1 / 4

theorem parO_B_pos (d n : ℕ) (δ : ℚ) : 0 < (parO d n δ).B := by
  unfold parO parN
  simp only
  omega

/-! ## The coupled world and the losses -/

section Rec

variable {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} {K : Set (E d)} {coin : Ω → ℕ → Bool}
  {loss : ℕ → Ω → E d → ℝ} {noise : ℕ → Ω → ℝ}

/-- An environment with BL-O's windows has the windows of the extension with `P0O` prologue blocks of `2 B` coins. -/
theorem winO {n : ℕ} {δ r0 R0 : ℚ} {a : Fin d → ℚ}
    (h : NoisyAdv K n (DO d n δ r0 R0 a) (DO' d n δ r0 R0 a) μ coin loss noise) :
    NoisyAdv K n (winL d (2 * (parO d n δ).B * P0O d n δ r0 R0) (parO d n δ).B)
      (winN d (2 * (parO d n δ).B * P0O d n δ r0 R0) (parO d n δ).B) μ coin loss noise := h

/-- The coupled world of an environment with BL-O's windows: the extension with `P0O` prologue blocks of `2 B` coins,
`B = (parO d n δ).B`. -/
noncomputable def extO (n : ℕ) (δ r0 R0 : ℚ) (a : Fin d → ℚ)
    (h : NoisyAdv K n (DO d n δ r0 R0 a) (DO' d n δ r0 R0 a) μ coin loss noise) : CWorld d (Ω × (ℕ → ℝ)) :=
  extW (P0O d n δ r0 R0) (parO d n δ).B (winO h)

/-- The extension meets `ExtOK`. -/
theorem extO_ok (n : ℕ) (δ r0 R0 : ℚ) (a : Fin d → ℚ)
    (h : NoisyAdv K n (DO d n δ r0 R0 a) (DO' d n δ r0 R0 a) μ coin loss noise) :
    ExtOK μ K n (P0O d n δ r0 R0) (parO d n δ).B coin loss noise (extO n δ r0 R0 a h) :=
  extOK (P0O d n δ r0 R0) (parO d n δ).B (parO_B_pos d n δ) (winO h)

/-- The losses of the environment as a loss process of the extension. -/
noncomputable def lossO (n : ℕ) (δ r0 R0 : ℚ) (a : Fin d → ℚ)
    (h : NoisyAdv K n (DO d n δ r0 R0 a) (DO' d n δ r0 R0 a) μ coin loss noise) (hK : Convex ℝ K) :
    LossProcW d n K (extO n δ r0 R0 a h).𝓕 :=
  lossProcE (winO h) (extO_ok n δ r0 R0 a h) hK

/-! ## The shift and the advice -/

/-- The shift `(m_t, r_t)` of round `t` at P°'s mode `mo` before round `t` (the coupling; Bit/BLRun.lean `shW`
with BL-O's gauge play): `r = pt'/pt°`, `m = (r - 1) ε_t + (pt' f(x') - pt° f°(x°) + 4 (pt' - 1)/ε' -
4 (pt° - 1)/ε)/pt°`; `(0, 1)` unless both learners are in mode `run` and `t < n` (past the horizon the record reads
nothing of the environment, whose losses are measurable below it only). -/
noncomputable def shO (n : ℕ) (δ r0 R0 : ℚ) (a : Fin d → ℚ) (orc : (Fin d → ℚ) → ℕ → Bool)
    (h : NoisyAdv K n (DO d n δ r0 R0 a) (DO' d n δ r0 R0 a) μ coin loss noise) (hK : Convex ℝ K) (t : ℕ)
    (p : Ω × (ℕ → ℝ)) (mo : Df2Mode d) : ℝ × ℝ :=
  if t < n then
  match mo, modeO d n δ r0 R0 a (envWorld orc coin loss noise p.1) t with
  | .run so, .run st =>
    let c := cfgW d n δ r0 R0 a (envWorld orc coin loss noise p.1)
    let q := recPos d n orc coin δ r0 R0 a p
    let Xo := refX (poO d n δ) so ((extO n δ r0 R0 a h).xi t p)
    let pto := refPt (poO d n δ) (kTh n (dBL d n δ) K q) Xo
    let xo : E d := pgMu q + pgOp q (WithLp.toLp 2 (pto⁻¹ • Xo))
    let pt' : ℝ := ptO orc c (XO c st (drawO d n δ r0 R0 (coin p.1) t).1)
    let x' : E d := toE (playO d n δ r0 R0 a (envWorld orc coin loss noise p.1) t)
    let r := pt' / pto
    ((r - 1) * (extO n δ r0 R0 a h).nz t p +
        (pt' * (lossO n δ r0 R0 a h hK).L t ((lossO n δ r0 R0 a h hK).lam t p) x' -
          pto * (if t < n then fL K (lossO n δ r0 R0 a h hK).L t ((lossO n δ r0 R0 a h hK).lam t p) else 0) xo +
          4 * (pt' - 1) / (c.par.eps : ℝ) - 4 * (pto - 1) / (poO d n δ).eps) / pto, r)
  | _, _ => (0, 1)
  else (0, 1)

/-- BL-O's test call of a round in mode `run` and its decision: the point `p'` and whether BL-O fires; `none` when
BL-O acts its guard before the test or the call fails. The lines R5 to R12 of `stepO`, verbatim. -/
def testO (orc : (Fin d → ℚ) → ℕ → Bool) (c : CfgO d) (st : St d) (ξ : Fin d → ℚ) (ζ : ℚ) (obs : ℤ) :
    Option ((Fin d → ℚ) × Bool) :=
  let P := c.par
  let w := st.A *ᵥ ξ
  let X := XO c st ξ
  let pt := ptO orc c X
  let Y := rnd P.p (pt * ((obs : ℚ) / 2 ^ P.p + ζ) / 2 + 2 * (pt - 1) / P.eps)
  let cc := P.kapc * Y
  let a := 1 - cc
  let q := a + cc * (ξ ⬝ᵥ ξ)
  if a < 1 / 2 ∨ q < 1 / 2 then none else
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
  if 2 * (P.Lam : ℚ) < frob2 B' ∨ 2 * (P.Lam : ℚ) < frob2 A' then none else
  let Pp := B' * B'ᵀ
  let wp := b' - (P.eta / 2) • G'
  let callT : CallQ d :=
    if st.first then callO c 0 0 0 (1 - P.eps) Pp wp ((1 - P.eps) ^ 2 / (P.Ne * d * 8))
    else callO c (st.B * st.Bᵀ) st.b (LT P - st.k) (rB P / 2) Pp wp (rB P ^ 2 / (P.Ne * d * 8))
  match apO orc c callT with
  | none => none
  | some p' =>
    some (p', decide (P.eta * (l' - G' ⬝ᵥ p') - 2 * (p' ⬝ᵥ (Pp *ᵥ p') / 2 - b' ⬝ᵥ p' + k') ≤ -P.rho + P.eHat))

/-- The advice of a round (Lemmas SEL and VAL; `advQ` of Bit/BLRun.lean with BL-O's test and step): for the
test call, the selection `selT` of BL-O's test point for P°'s test function at P°'s state `so`, draw `ξ` and
observation `Y`; for line μ, BL-O's answer. -/
noncomputable def advQO (orc : (Fin d → ℚ) → ℕ → Bool) (c : CfgO d) (n : ℕ) (st : St d) (ξ' : Fin d → ℚ) (ζ' : ℚ)
    (obs : ℤ) (p : Df2OPar) (so : Df2St d) (ξ : Fin d → ℝ) (Y : ℝ) : Adv d :=
  (match testO orc c st ξ' ζ' obs with
    | none => 0
    | some (pq, fire) =>
      selT (refTest p so ξ Y).1 (refTest p so ξ Y).2.1 (refTest p so ξ Y).2.2 (-(p.theta * p.rho)) so.ctr so.r
        (cV pq) fire,
   cV (muOf (stepO orc c n (.run st) ξ' ζ' obs)))

/-- P°'s observation of round `t` at its mode `.run so` on the extension (the `Y` of `df2RoundGa`), with the coupled
dither `coupMax` of the record's shift. -/
noncomputable def refYO (n : ℕ) (δ r0 R0 : ℚ) (a : Fin d → ℚ) (orc : (Fin d → ℚ) → ℕ → Bool)
    (h : NoisyAdv K n (DO d n δ r0 R0 a) (DO' d n δ r0 R0 a) μ coin loss noise) (hK : Convex ℝ K) (t : ℕ)
    (p : Ω × (ℕ → ℝ)) (so : Df2St d) : ℝ :=
  let q := recPos d n orc coin δ r0 R0 a p
  let Xo := refX (poO d n δ) so ((extO n δ r0 R0 a h).xi t p)
  let pto := refPt (poO d n δ) (kTh n (dBL d n δ) K q) Xo
  let xo : E d := pgMu q + pgOp q (WithLp.toLp 2 (pto⁻¹ • Xo))
  let sh := shO n δ r0 R0 a orc h hK t p (.run so)
  pto * ((if t < n then fL K (lossO n δ r0 R0 a h hK).L t ((lossO n δ r0 R0 a h hK).lam t p) else 0) xo +
      (extO n δ r0 R0 a h).nz t p + coupMax sh.1 sh.2 ((extO n δ r0 R0 a h).zz t p)) / 2 +
    2 * (pto - 1) / (poO d n δ).eps

/-- The advice of round `t` at P°'s mode `mo` before round `t`; `(0, 0)` unless both learners are in mode `run` and
`t < n`. -/
noncomputable def advO (n : ℕ) (δ r0 R0 : ℚ) (a : Fin d → ℚ) (orc : (Fin d → ℚ) → ℕ → Bool)
    (h : NoisyAdv K n (DO d n δ r0 R0 a) (DO' d n δ r0 R0 a) μ coin loss noise) (hK : Convex ℝ K) (t : ℕ)
    (p : Ω × (ℕ → ℝ)) (mo : Df2Mode d) : Adv d :=
  if t < n then
  match mo, modeO d n δ r0 R0 a (envWorld orc coin loss noise p.1) t with
  | .run so, .run st =>
    advQO orc (cfgW d n δ r0 R0 a (envWorld orc coin loss noise p.1)) n st (drawO d n δ r0 R0 (coin p.1) t).1
      (drawO d n δ r0 R0 (coin p.1) t).2 (readO d n δ r0 R0 a (envWorld orc coin loss noise p.1) t) (poO d n δ) so
      ((extO n δ r0 R0 a h).xi t p) (refYO n δ r0 R0 a orc h hK t p so)
  | _, _ => (0, 0)
  else (0, 0)

/-! ## The soundness event -/

/-- The bound `e_ξ` on each coordinate of `ξ'_t - ξ_t` on `E_bits`, `2^{2 - B/2}` (BL's E1 at `parO`). -/
noncomputable def eXiO (d n : ℕ) (δ : ℚ) : ℝ := 4 / 2 ^ ((parO d n δ).B / 2)

/-- The bound `e_ζ` on `ζ'_t - Z̃_t/2` on `E_bits`, `2^{1 - B/2}`. -/
noncomputable def eZtO (d n : ℕ) (δ : ℚ) : ℝ := 2 / 2 ^ ((parO d n δ).B / 2)

/-- The bound of the noise on the no-clip event: `3 + 4 (ln(14 n N_e))^{1/2}`, so that a feedback `f + ε` with
`f ∈ [0, 1]` is within the range of `ObsClipO`. -/
noncomputable def nzBndO (d n : ℕ) (δ : ℚ) : ℝ := 3 + 4 * Real.sqrt (Real.log (14 * n * (parO d n δ).Ne))

/-- `E_bits`: BL-O's draws of the rounds `t < n` are within `e_ξ`, `e_ζ` of the world's draw and half its dither
coordinate. -/
def EbitsO (n : ℕ) (δ r0 R0 : ℚ) (a : Fin d → ℚ)
    (h : NoisyAdv K n (DO d n δ r0 R0 a) (DO' d n δ r0 R0 a) μ coin loss noise) : Set (Ω × (ℕ → ℝ)) :=
  {p | ∀ t < n, (∀ i, |((drawO d n δ r0 R0 (coin p.1) t).1 i : ℝ) - (extO n δ r0 R0 a h).xi t p i| ≤ eXiO d n δ) ∧
    |((drawO d n δ r0 R0 (coin p.1) t).2 : ℝ) - (extO n δ r0 R0 a h).zz t p 0 / 2| ≤ eZtO d n δ}

/-- The no-clip event (UNI-OBS): the noises of the rounds `t < n` are within `nzBndO`. -/
def NoClipO (n : ℕ) (δ r0 R0 : ℚ) (a : Fin d → ℚ)
    (h : NoisyAdv K n (DO d n δ r0 R0 a) (DO' d n δ r0 R0 a) μ coin loss noise) : Set (Ω × (ℕ → ℝ)) :=
  {p | ∀ t < n, |(extO n δ r0 R0 a h).nz t p| ≤ nzBndO d n δ}

/-! ## The record -/

/-- **BL-O's run record** on the extension of an environment with BL-O's windows. -/
noncomputable def recO (n : ℕ) (δ r0 R0 : ℚ) (a : Fin d → ℚ) (orc : (Fin d → ℚ) → ℕ → Bool)
    (h : NoisyAdv K n (DO d n δ r0 R0 a) (DO' d n δ r0 R0 a) μ coin loss noise) (hK : Convex ℝ K) :
    RunW d n K (extO n δ r0 R0 a h) where
  F := lossO n δ r0 R0 a h hK
  pos := recPos d n orc coin δ r0 R0 a
  sh := shO n δ r0 R0 a orc h hK
  adv := advO n δ r0 R0 a orc h hK
  play := recPlay d n orc coin loss noise δ r0 R0 a
  bits := EbitsO n δ r0 R0 a h ∩ NoClipO n δ r0 R0 a h
  Coup := coupMax

/-- The record's losses of the rounds `t < n` are the environment's. -/
theorem recO_loss (n : ℕ) (δ r0 R0 : ℚ) (a : Fin d → ℚ) (orc : (Fin d → ℚ) → ℕ → Bool)
    (h : NoisyAdv K n (DO d n δ r0 R0 a) (DO' d n δ r0 R0 a) μ coin loss noise) (hK : Convex ℝ K)
    (p : Ω × (ℕ → ℝ)) (t : ℕ) (ht : t < n) : (recO n δ r0 R0 a orc h hK).loss p t = loss t p.1 := by
  show (lossProcE (winO h) (extO_ok n δ r0 R0 a h) hK).L t ((lossProcE (winO h) (extO_ok n δ r0 R0 a h) hK).lam t p) = _
  simp only [lossProcE, ht, ↓reduceDIte]

/-- The record's plays are BL-O's on the environment's world. -/
theorem recO_play (n : ℕ) (δ r0 R0 : ℚ) (a : Fin d → ℚ) (orc : (Fin d → ℚ) → ℕ → Bool)
    (h : NoisyAdv K n (DO d n δ r0 R0 a) (DO' d n δ r0 R0 a) μ coin loss noise) (hK : Convex ℝ K)
    (p : Ω × (ℕ → ℝ)) (t : ℕ) :
    (recO n δ r0 R0 a orc h hK).play t p = toE (playO d n δ r0 R0 a (envWorld orc coin loss noise p.1) t) := rfl

end Rec

end AdversarialBco.Unified.Asm
