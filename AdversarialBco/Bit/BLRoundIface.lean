/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.BLRun

@[expose] public section

/-!
# Piece C of `RunOK`: the cut C1 / C2

`RoundC` of Bit/BLRun.lean is cut in two:

* C1 (`C1Stmt`): BL's round arithmetic R5 to R10 against P°'s update of round `s` (Lemmas TRACK, TRACK-2 and DOM
  with E1 to E11): BL's two guards before the test do not act, and
  its new pair and fields are tracked against P°'s `An`, `Pn An`, `bn`, `kn`, `Gn`, `ln` with the bounds of `Track` at
  `s + 1`; with the observation, `q` and `w` errors that line μ reads.
* C2 (`C2Stmt`): the test call, the fire decision and line μ (Lemmas SEL, VAL and GUARD
  with E12 to E16 and E18): from C1's conclusions, the checked advice `advQ` is accepted by P°'s routine at both calls,
  so either both learners fire or both continue, and `Track` holds at `s + 1`.

`roundC_of : C1Stmt → C2Stmt → RoundC`. The hypotheses of `RoundC` other than `O3SpecQ` and the advice are bundled in
`RCHyp`; BL's values of R5 to R9 in `rv`, verbatim from `step`.
-/

namespace AdversarialBco.Bit.BLP

open MeasureTheory
open AdversarialBco.BitRAM
open AdversarialBco.RealRAM (Strategy lossAd polytope)
open AdversarialBco.Poly
open AdversarialBco.Poly.Layer2 (kTh WΩ)
open AdversarialBco.Bit.Cpl
open AdversarialBco.Bit.Asm
open Matrix

variable {d : ℕ}

namespace RC

/-- P°'s epoch context of piece C: the parameters at BL's confidence, the body `kTh` at BL's position, the routines
`ap`. -/
noncomputable abbrev ctx (R : Routines) (d n m : ℕ) (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) (cs : ℕ → Bool)
    (ap : ℕ → ApFun d) : Df2Ctx d :=
  df2CtxAtF d n (deltaBL d n) (kTh n (deltaBL d n) (polytope A b) (posR R d n m A b cs)) ap

/-- BL's reading `⌊2^p f(x')⌋` of a round in mode `run st` with the loss `f`. -/
noncomputable def obsQ (cfg : Cfg d) (st : St d) (ξ' : Fin d → ℚ) (f : E d → ℝ) : ℤ :=
  ⌊(2 : ℝ) ^ cfg.par.p * f (toE (playPt cfg (.run st) ξ'))⌋

/-- BL's values of R5 YOBS to R9 INCR in mode `run`. -/
structure RV (d : ℕ) where
  Y : ℚ
  c : ℚ
  a : ℚ
  q : ℚ
  s1 : ℚ
  s3 : ℚ
  rq : ℚ
  s2 : ℚ
  s4 : ℚ
  A : Matrix (Fin d) (Fin d) ℚ
  B : Matrix (Fin d) (Fin d) ℚ
  b : Fin d → ℚ
  k : ℚ
  g : Fin d → ℚ
  G : Fin d → ℚ
  l : ℚ

/-- BL's values of R5 to R9 from the state `st`, the draws `ξ`, `ζ` and the reading `obs` (the `let`s of `step`). -/
def rv (cfg : Cfg d) (st : St d) (ξ : Fin d → ℚ) (ζ : ℚ) (obs : ℤ) : RV d :=
  let P := cfg.par
  let w := st.A *ᵥ ξ
  let X := XQ cfg st ξ
  let pt := ptQ cfg X
  let Y := rnd P.p (pt * ((obs : ℚ) / 2 ^ P.p + ζ) / 2 + 2 * (pt - 1) / P.eps)
  let c := P.kapc * Y
  let a := 1 - c
  let q := a + c * (ξ ⬝ᵥ ξ)
  let s1 := sqrtDn P.p (1 / a)
  let s3 := sqrtDn P.p a
  let rq := sqrtDn P.p q
  let s2 := rnd P.p (c / (s3 * rq * (s3 + rq)))
  let s4 := rnd P.p (c / (s3 + rq))
  let A' := rndM P.p (s1 • st.A - s2 • vecMulVec w ξ)
  let B' := rndM P.p (s3 • st.B + s4 • vecMulVec (st.B *ᵥ ξ) ξ)
  let u := st.B *ᵥ ξ
  let v := st.Bᵀ *ᵥ st.mu
  let b' := st.b + rndV P.p (c • ((u ⬝ᵥ st.mu) • u - st.B *ᵥ v))
  let k' := st.k + rnd P.p (c / 2 * ((u ⬝ᵥ st.mu) ^ 2 - v ⬝ᵥ v))
  let g := rndV P.p ((Y * P.nu) • u)
  let G' := st.G + g
  let l' := st.l + rnd P.p (g ⬝ᵥ st.mu)
  ⟨Y, c, a, q, s1, s3, rq, s2, s4, A', B', b', k', g, G', l'⟩

/-- The hypotheses of `RoundC` other than `O3SpecQ R.ap` and the advice. -/
structure RCHyp (R : Routines) (d n m : ℕ) (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) (cs : ℕ → Bool)
    (ap : ℕ → ApFun d) (π : Df2Path d) (s : ℕ) (st : St d) (ξ' : Fin d → ℚ) (ζ' : ℚ) (Z : ℝ) (f : E d → ℝ) :
    Prop where
  hd : 1 ≤ d
  hn : 1 ≤ n
  hc : RunCase d n
  bud : Bud.BudOK d n
  pg : PgGood d (polytope A b) (po d n).R (some (posR R d n m A b cs))
  rows : ∀ y : Fin d → ℝ, (∀ i, cV ((cfgOf R d n m A b cs).α i) ⬝ᵥ y ≤ (cfgOf R d n m A b cs).β i) ↔
    pgMu (posR R d n m A b cs) + pgOp (posR R d n m A b cs) (WithLp.toLp 2 y) ∈ polytope A b
  bpos : ∀ i, 0 < (cfgOf R d n m A b cs).β i
  gauge : ∀ X : Fin d → ℚ, (gaugeQ (cfgOf R d n m A b cs) X : ℝ) =
    gauge (kTh n (deltaBL d n) (polytope A b) (posR R d n m A b cs)) (WithLp.toLp 2 (cV X))
  hs : s < n
  det : DetHyp (ctx R d n m A b cs ap) (deltaBL d n) π (s + 1)
  tau : (ctx R d n m A b cs ap).tau π (s + 1) = s
  track : Track d n st ((ctx R d n m A b cs ap).st π s) s
  adm : AdmLoss (polytope A b) f
  g : ∀ y, π.g s y = f (pgMu (posR R d n m A b cs) + pgOp (posR R d n m A b cs) y) / 2
  xi : ∀ i, |(ξ' i : ℝ) - π.xi s i| ≤ eXi0 d n
  zt : |(ζ' : ℝ) - Z / 2| ≤ eZt0 d n
  Y : (ctx R d n m A b cs ap).Y π s =
    ptQ (cfgOf R d n m A b cs) (XQ (cfgOf R d n m A b cs) st ξ') *
        (f (toE (playPt (cfgOf R d n m A b cs) (.run st) ξ')) + Z / 2) / 2 +
      2 * (ptQ (cfgOf R d n m A b cs) (XQ (cfgOf R d n m A b cs) st ξ') - 1) / ((cfgOf R d n m A b cs).par.eps : ℝ)

/-- C1's conclusions on BL's values `r` of R5 to R9 (E2, E3, E7, E9, E11, E16, E18 and the tracking lemma
at `s + 1`): the guards of R7 and R10 do not act; the new pair is `(I + H) A°_{s+1}`, `(I + H^B) P°_{s+1} A°_{s+1}`
with `H`, `H^B` within `hTr (s + 1)`; the fields `b, k, G, l` within `s + 1` times their error per round; the
observation, `q` and `w = A ξ` within `e_Y`, `Δ_q`, `Δ_u`. -/
structure C1Out (d n : ℕ) (cfg : Cfg d) (st : St d) (ξ' : Fin d → ℚ) (r : RV d) (c : Df2Ctx d) (π : Df2Path d)
    (s : ℕ) : Prop where
  ga : ¬ (r.a < 1 / 2 ∨ r.q < 1 / 2)
  gt : ¬ (2 * (cfg.par.Lam : ℚ) < frob2 r.B ∨ 2 * (cfg.par.Lam : ℚ) < frob2 r.A)
  hA : ∃ H : Matrix (Fin d) (Fin d) ℝ, cM r.A = (1 + H) * c.An π s ∧ opN H ≤ Bud.hTr d n (s + 1)
  hB : ∃ H : Matrix (Fin d) (Fin d) ℝ, cM r.B = (1 + H) * (c.Pn π s * c.An π s) ∧ opN H ≤ Bud.hTr d n (s + 1)
  errb : oNorm (cV r.b - c.bn π s) ≤ (s + 1) * Bud.eb d n
  errk : |(r.k : ℝ) - c.kn π s| ≤ (s + 1) * Bud.ek d n
  errG : oNorm (cV r.G - c.Gn π s) ≤ (s + 1) * Bud.eg d n
  errl : |(r.l : ℝ) - c.ln π s| ≤ (s + 1) * Bud.el d n
  eY : |(r.Y : ℝ) - c.Y π s| ≤ Bud.eY d n
  eq : |(r.q : ℝ) - c.qq π s| ≤ Bud.Dq d n
  ew : oNorm (cV (st.A *ᵥ ξ') - c.w π s) ≤ Bud.Du d n

/-- C1: under `RCHyp`, BL's round values satisfy `C1Out`. -/
def C1Stmt : Prop :=
  ∀ (R : Routines) (d n m : ℕ) (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) (cs : ℕ → Bool)
    (ap : ℕ → ApFun d) (π : Df2Path d) (s : ℕ) (st : St d) (ξ' : Fin d → ℚ) (ζ' : ℚ) (Z : ℝ) (f : E d → ℝ),
    RCHyp R d n m A b cs ap π s st ξ' ζ' Z f →
    C1Out d n (cfgOf R d n m A b cs) st ξ'
      (rv (cfgOf R d n m A b cs) st ξ' ζ' (obsQ (cfgOf R d n m A b cs) st ξ' f)) (ctx R d n m A b cs ap) π s

/-- C2: under `O3SpecQ`, `RCHyp`, the advice and C1's conclusions, the conclusion of `RoundC`. -/
def C2Stmt : Prop :=
  ∀ (R : Routines) (d n m : ℕ) (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) (cs : ℕ → Bool)
    (ap : ℕ → ApFun d) (π : Df2Path d) (s : ℕ) (st : St d) (ξ' : Fin d → ℚ) (ζ' : ℚ) (Z : ℝ) (f : E d → ℝ),
    O3SpecQ R.ap → RCHyp R d n m A b cs ap π s st ξ' ζ' Z f →
    ap s = apAdv (advQ R.ap (cfgOf R d n m A b cs) n st ξ' ζ' (obsQ (cfgOf R d n m A b cs) st ξ' f)
      (ctx R d n m A b cs ap).p ((ctx R d n m A b cs ap).st π s) (π.xi s) ((ctx R d n m A b cs ap).Y π s)) →
    C1Out d n (cfgOf R d n m A b cs) st ξ'
      (rv (cfgOf R d n m A b cs) st ξ' ζ' (obsQ (cfgOf R d n m A b cs) st ξ' f)) (ctx R d n m A b cs ap) π s →
    (step R.ap (cfgOf R d n m A b cs) n (.run st) ξ' ζ' (obsQ (cfgOf R d n m A b cs) st ξ' f) =
        .run (init (cfgOf R d n m A b cs).par d) ∧ (ctx R d n m A b cs ap).fire π s) ∨
      ∃ st' : St d, step R.ap (cfgOf R d n m A b cs) n (.run st) ξ' ζ' (obsQ (cfgOf R d n m A b cs) st ξ' f) =
          .run st' ∧ (ctx R d n m A b cs ap).cont π s ∧
        Track d n st' ((ctx R d n m A b cs ap).st π (s + 1)) (s + 1)

end RC

open RC in
/-- Piece C, the round, from the cut. -/
theorem roundC_of (h1 : C1Stmt) (h2 : C2Stmt) : RoundC := by
  intro R d n m A b cs ap π s st ξ' ζ' Z f hd hn hc hbud hO3 hpg hrows hpos hgauge hs hdet htau htr hadm hg hxi hzt
    c cfg pt' fx obs
    hY hap
  have H : RCHyp R d n m A b cs ap π s st ξ' ζ' Z f :=
    ⟨hd, hn, hc, hbud, hpg, hrows, hpos, hgauge, hs, hdet, htau, htr, hadm, hg, hxi, hzt, hY⟩
  exact h2 R d n m A b cs ap π s st ξ' ζ' Z f hO3 H hap (h1 R d n m A b cs ap π s st ξ' ζ' Z f H)

end AdversarialBco.Bit.BLP
