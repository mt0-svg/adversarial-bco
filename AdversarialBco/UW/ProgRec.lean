/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.UW.ProgPure
public import AdversarialBco.UW.Interfaces

@[expose] public section

/-!
# BL-OW's shift and advice on the extension

The two fields of `ImplW` that the run record `recUW` takes from BL-OW: the shift `shOW` and the advice `advOW`. They
are Theorem U's `shO` and `advO` (Unified/AsmRec.lean) with BL-O's run replaced by BL-OW's (`modeOW`, `playOW`,
`readOW`, `cfgWW`) and P° of Theorem U by P° of Theorem UW at PARAM-W's reference `refW d n δ = (u', b0, y0, δ_c)`
(`parW d n u'`, the level `δ_c = deltaC d n k_δ` of `kTh`):

* the shift compares the unweighted observations, as in Theorem U: `r = pt'/pt°`,
  `m = (r - 1) ε_t + (pt' f(x') - pt° f°(x°) + 4 (pt' - 1)/ε' - 4 (pt° - 1)/ε)/pt°`;
* the advice selects BL-OW's test point for P°'s test function after P°'s update, which reads P°'s weighted
  observation `obsW b0 y0 ξ Y°` (`df2RoundGaW`), and passes BL-OW's line μ answer (`testOW`: the lines R5 to R12 of
  `stepOW`).
-/

open MeasureTheory ProbabilityTheory

namespace AdversarialBco.UW.BLOW

open AdversarialBco AdversarialBco.Poly AdversarialBco.Poly.Layer2 AdversarialBco.Bit.Cpl
open AdversarialBco.Unified.World AdversarialBco.Unified.BLO AdversarialBco.Unified.Asm
open AdversarialBco.Unified (NoisyAdv envWorld)
open AdversarialBco.Bit.BLP (St Mode refX refPt refTest selT muOf cV rnd sqrtDn rndM rndV frob2 LT rB CallQ)
open AdversarialBco.BitRAM (toE)
open AdversarialBco.Poly.Conj1 (fL)
open Matrix

variable {d : ℕ}

/-- The reference of Theorem UW at the input: PARAM-W's `u'`, `b0`, `y0` and the level `δ_c = 1/(2^{k_δ} N_0)`. -/
noncomputable def refW (d n : ℕ) (δ : ℚ) : RefW :=
  ⟨(uOW d n δ : ℝ), (b0OW d n δ : ℝ), (y0OW d n δ : ℝ), deltaC d n (kDel δ)⟩

/-- P°'s parameters at the input: T4U at PARAM-W's scaling. -/
noncomputable def poW (d n : ℕ) (δ : ℚ) : Df2OPar := parW d n (uOW d n δ : ℝ)

/-- BL-OW's test call of a round in mode `run` and its decision (the lines R5 to R12 of `stepOW`, verbatim). -/
def testOW (b0 y0 : ℚ) (orc : (Fin d → ℚ) → ℕ → Bool) (c : CfgO d) (st : St d) (ξ : Fin d → ℚ) (ζ : ℚ) (obs : ℤ) :
    Option ((Fin d → ℚ) × Bool) :=
  let P := c.par
  let w := st.A *ᵥ ξ
  let X := XO c st ξ
  let pt := ptO orc c X
  let Y := rnd P.p (pt * ((obs : ℚ) / 2 ^ P.p + ζ) / 2 + 2 * (pt - 1) / P.eps)
  let Yw := ywQ P.p b0 y0 ξ Y
  let cc := P.kapc * Yw
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
  let g := rndV P.p ((Yw * P.nu) • u)
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

/-- The advice of a round: the selection `selT` of BL-OW's test point for P°'s test function at P°'s state `so`,
draw `ξ` and weighted observation `obsW b0 y0 ξ Y` (`Y` P°'s observation before the weight and the clip); for line μ,
BL-OW's answer. -/
noncomputable def advQOW (b0 y0 : ℚ) (orc : (Fin d → ℚ) → ℕ → Bool) (c : CfgO d) (n : ℕ) (st : St d)
    (ξ' : Fin d → ℚ) (ζ' : ℚ) (obs : ℤ) (p : Df2OPar) (so : Df2St d) (ξ : Fin d → ℝ) (Y : ℝ) : Adv d :=
  (match testOW b0 y0 orc c st ξ' ζ' obs with
    | none => 0
    | some (pq, fire) =>
      selT (refTest p so ξ (obsW (b0 : ℝ) (y0 : ℝ) ξ Y)).1 (refTest p so ξ (obsW (b0 : ℝ) (y0 : ℝ) ξ Y)).2.1
        (refTest p so ξ (obsW (b0 : ℝ) (y0 : ℝ) ξ Y)).2.2 (-(p.theta * p.rho)) so.ctr so.r (cV pq) fire,
   cV (muOf (stepOW b0 y0 orc c n (.run st) ξ' ζ' obs)))

section Rec

variable {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} {K : Set (E d)} {coin : Ω → ℕ → Bool}
  {loss : ℕ → Ω → E d → ℝ} {noise : ℕ → Ω → ℝ}

/-- The shift `(m_t, r_t)` of round `t` at P°'s mode `mo` before round `t`: `shO` with BL-OW's run and P° of
Theorem UW; `(0, 1)` unless both learners are in mode `run` and `t < n`. -/
noncomputable def shOW (n : ℕ) (δ r0 R0 : ℚ) (a : Fin d → ℚ) (orc : (Fin d → ℚ) → ℕ → Bool)
    (h : NoisyAdv K n (DO d n δ r0 R0 a) (DO' d n δ r0 R0 a) μ coin loss noise) (hK : Convex ℝ K) (t : ℕ)
    (p : Ω × (ℕ → ℝ)) (mo : Df2Mode d) : ℝ × ℝ :=
  if t < n then
  match mo, modeOW d n δ r0 R0 a (envWorld orc coin loss noise p.1) t with
  | .run so, .run st =>
    let c := cfgWW d n δ r0 R0 a (envWorld orc coin loss noise p.1)
    let q := recPos d n orc coin δ r0 R0 a p
    let Xo := refX (poW d n δ) so ((extO n δ r0 R0 a h).xi t p)
    let pto := refPt (poW d n δ) (kTh n (deltaC d n (kDel δ)) K q) Xo
    let xo : E d := pgMu q + pgOp q (WithLp.toLp 2 (pto⁻¹ • Xo))
    let pt' : ℝ := ptO orc c (XO c st (drawO d n δ r0 R0 (coin p.1) t).1)
    let x' : E d := toE (playOW d n δ r0 R0 a (envWorld orc coin loss noise p.1) t)
    let r := pt' / pto
    ((r - 1) * (extO n δ r0 R0 a h).nz t p +
        (pt' * (lossO n δ r0 R0 a h hK).L t ((lossO n δ r0 R0 a h hK).lam t p) x' -
          pto * (if t < n then fL K (lossO n δ r0 R0 a h hK).L t ((lossO n δ r0 R0 a h hK).lam t p) else 0) xo +
          4 * (pt' - 1) / (c.par.eps : ℝ) - 4 * (pto - 1) / (poW d n δ).eps) / pto, r)
  | _, _ => (0, 1)
  else (0, 1)

/-- P°'s unweighted observation of round `t` at its mode `.run so` on the extension (the `Y` of `df2RoundGaW` before
the weight and the clip), with the coupled dither `coupMax` of the record's shift. -/
noncomputable def refYOW (n : ℕ) (δ r0 R0 : ℚ) (a : Fin d → ℚ) (orc : (Fin d → ℚ) → ℕ → Bool)
    (h : NoisyAdv K n (DO d n δ r0 R0 a) (DO' d n δ r0 R0 a) μ coin loss noise) (hK : Convex ℝ K) (t : ℕ)
    (p : Ω × (ℕ → ℝ)) (so : Df2St d) : ℝ :=
  let q := recPos d n orc coin δ r0 R0 a p
  let Xo := refX (poW d n δ) so ((extO n δ r0 R0 a h).xi t p)
  let pto := refPt (poW d n δ) (kTh n (deltaC d n (kDel δ)) K q) Xo
  let xo : E d := pgMu q + pgOp q (WithLp.toLp 2 (pto⁻¹ • Xo))
  let sh := shOW n δ r0 R0 a orc h hK t p (.run so)
  pto * ((if t < n then fL K (lossO n δ r0 R0 a h hK).L t ((lossO n δ r0 R0 a h hK).lam t p) else 0) xo +
      (extO n δ r0 R0 a h).nz t p + coupMax sh.1 sh.2 ((extO n δ r0 R0 a h).zz t p)) / 2 +
    2 * (pto - 1) / (poW d n δ).eps

/-- The advice of round `t` at P°'s mode `mo` before round `t`; `(0, 0)` unless both learners are in mode `run` and
`t < n`. -/
noncomputable def advOW (n : ℕ) (δ r0 R0 : ℚ) (a : Fin d → ℚ) (orc : (Fin d → ℚ) → ℕ → Bool)
    (h : NoisyAdv K n (DO d n δ r0 R0 a) (DO' d n δ r0 R0 a) μ coin loss noise) (hK : Convex ℝ K) (t : ℕ)
    (p : Ω × (ℕ → ℝ)) (mo : Df2Mode d) : Adv d :=
  if t < n then
  match mo, modeOW d n δ r0 R0 a (envWorld orc coin loss noise p.1) t with
  | .run so, .run st =>
    advQOW (b0OW d n δ) (y0OW d n δ) orc (cfgWW d n δ r0 R0 a (envWorld orc coin loss noise p.1)) n st
      (drawO d n δ r0 R0 (coin p.1) t).1 (drawO d n δ r0 R0 (coin p.1) t).2
      (readOW d n δ r0 R0 a (envWorld orc coin loss noise p.1) t) (poW d n δ) so ((extO n δ r0 R0 a h).xi t p)
      (refYOW n δ r0 R0 a orc h hK t p so)
  | _, _ => (0, 0)
  else (0, 0)

end Rec

/-- **BL-OW as data** for a program text `P` with the cost constants `C'`, `k`: PARAM-W's schedule, BL-OW's plays,
shift and advice. -/
noncomputable def implW (P : List BitRAMO.InstrO) (C' : ℝ) (k : ℕ) : ImplW where
  P := P
  C' := C'
  k := k
  u := fun d n δ => (uOW d n δ : ℝ)
  b0 := fun d n δ => (b0OW d n δ : ℝ)
  y0 := fun d n δ => (y0OW d n δ : ℝ)
  play := fun d n δ r0 R0 a w t => playOW d n δ r0 R0 a w t
  sh := fun n δ r0 R0 a orc h hK => shOW n δ r0 R0 a orc h hK
  adv := fun n δ r0 R0 a orc h hK => advOW n δ r0 R0 a orc h hK

/-- **The plays are interior** (`PlayIntUW` for BL-OW). -/
theorem playIntUW (P : List BitRAMO.InstrO) (C' : ℝ) (k : ℕ) : PlayIntUW (implW P C' k) :=
  fun d n δ r0 R0 a K w hd hr0 hK hball horc t => playIntOW d n δ r0 R0 a K w hd hr0 hK hball horc t

end AdversarialBco.UW.BLOW
