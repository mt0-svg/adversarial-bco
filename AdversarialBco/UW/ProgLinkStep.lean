/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.UW.ProgPure
public import AdversarialBco.Bit.Transfer.XBLR5
public import AdversarialBco.Bit.Transfer.XBLSetupFacts

@[expose] public section

/-!
# The R5w box as a change of the dither

BL-OW's round (`stepOW`, UW/ProgPure.lean) is BL-O's round (`stepO`, Unified/BLOSpec.lean) with R5's observation `Y'`
replaced by the weighted, clipped observation `Y'^w = rnd_p(φ' clip(Y', y0))` (`ywQ`) in R7, R9 and R13. In `stepO`
the dither `ζ'` enters only through `Y' = rnd_p(pt' (obs/2^p + ζ')/2 + 2 (pt' - 1)/ε')`, and `pt' ≥ 1`. So for the dither

  `ζ_W = 2 (Y'^w - 2 (pt' - 1)/ε')/pt' - obs/2^p`

R5 of `stepO` returns `rnd_p(Y'^w) = Y'^w` (`Y'^w` lies on the grid `2^{-p}`), and BL-OW's round is BL-O's round at
the dither `ζ_W` (`stepOW_dither`). Everything BL-O's program does after R5 (R7 to R15, its machine proof) is then
BL-O's at `ζ_W`; the R5w box of the paper is exactly the computation of `Y'^w` from `Y'`.

* `tailY`: `stepO` in mode `run` after R5, as a function of `Y'` (R7 to R15, the text of `stepO` verbatim);
* `stepO_tailY`, `stepOW_tailY`: both rounds are `tailY` at their observation;
* `yObs_zetaW`: R5 at the dither `ζ_W` gives back any point of the grid;
* `stepOW_dither`: the reduction.
-/

namespace AdversarialBco.UW.ProgW

open AdversarialBco AdversarialBco.Unified.BLO
open AdversarialBco.UW.BLOW (stepOW ywQ)
open AdversarialBco.Bit.BLP (Par St Mode init rnd sqrtDn rndV rndM frob2 LT Lmu rB eBL CallQ)
open AdversarialBco.Bit.Transfer.BLM (OnG qn onG_rnd_s eq_qn_div)
open Matrix

variable {d : ℕ}

/-- R5 YOBS of `stepO` at the scale `pt'`, the dither `ζ` and the reading `obs`. -/
def yObs (P : Par) (pt ζ : ℚ) (obs : ℤ) : ℚ :=
  rnd P.p (pt * ((obs : ℚ) / 2 ^ P.p + ζ) / 2 + 2 * (pt - 1) / P.eps)

/-- The dither at which R5 returns `y`: `ζ_W = 2 (y - 2 (pt' - 1)/ε')/pt' - obs/2^p`. -/
def zetaW (P : Par) (pt y : ℚ) (obs : ℤ) : ℚ := 2 * (y - 2 * (pt - 1) / P.eps) / pt - (obs : ℚ) / 2 ^ P.p

/-- `rnd_k` is the identity on the grid `2^{-k}`. -/
theorem rnd_of_onG {k : ℕ} {x : ℚ} (h : OnG k x) : rnd k x = x := by
  have hx := eq_qn_div k h
  unfold rnd
  rw [hx, div_mul_cancel₀ _ (by positivity)]
  congr 1
  have : ⌊((qn k x : ℤ) : ℚ) + 1 / 2⌋ = qn k x := by
    rw [Int.floor_eq_iff]
    constructor <;> linarith
  rw [this]

/-- **R5 at the dither `ζ_W`** returns `y`, for `pt' ≠ 0` and `y` on the grid `2^{-p}`. -/
theorem yObs_zetaW (P : Par) {pt y : ℚ} (obs : ℤ) (hpt : pt ≠ 0) (hy : OnG P.p y) :
    yObs P pt (zetaW P pt y obs) obs = y := by
  unfold yObs zetaW
  have e : pt * ((obs : ℚ) / 2 ^ P.p + (2 * (y - 2 * (pt - 1) / P.eps) / pt - (obs : ℚ) / 2 ^ P.p)) / 2 +
      2 * (pt - 1) / P.eps = y := by
    field_simp
    ring
  rw [e, rnd_of_onG hy]

/-- **R7 FACTOR to R15 COMMIT of `stepO`** in mode `run`, as a function of R5's observation `Y`: the text of `stepO`
after R5, verbatim. -/
def tailY (orc : (Fin d → ℚ) → ℕ → Bool) (c : CfgO d) (n : ℕ) (st : St d) (ξ : Fin d → ℚ) (Y : ℚ) : Mode d :=
  let P := c.par
  let w := st.A *ᵥ ξ
  -- R7 FACTOR
  let cc := P.kapc * Y
  let a := 1 - cc
  let q := a + cc * (ξ ⬝ᵥ ξ)
  if a < 1 / 2 ∨ q < 1 / 2 then .guard else
  let s1 := sqrtDn P.p (1 / a)
  let s3 := sqrtDn P.p a
  let rq := sqrtDn P.p q
  let s2 := rnd P.p (cc / (s3 * rq * (s3 + rq)))
  let s4 := rnd P.p (cc / (s3 + rq))
  -- R8 PAIR
  let A' := rndM P.p (s1 • st.A - s2 • vecMulVec w ξ)
  let B' := rndM P.p (s3 • st.B + s4 • vecMulVec (st.B *ᵥ ξ) ξ)
  -- R9 INCR
  let u := st.B *ᵥ ξ
  let v := st.Bᵀ *ᵥ st.mu
  let b' := st.b + rndV P.p (cc • ((u ⬝ᵥ st.mu) • u - st.B *ᵥ v))
  let k' := st.k + rnd P.p (cc / 2 * ((u ⬝ᵥ st.mu) ^ 2 - v ⬝ᵥ v))
  let g := rndV P.p ((Y * P.nu) • u)
  let G' := st.G + g
  let l' := st.l + rnd P.p (g ⬝ᵥ st.mu)
  -- R10 TRACE
  if 2 * (P.Lam : ℚ) < frob2 B' ∨ 2 * (P.Lam : ℚ) < frob2 A' then .guard else
  let Pp := B' * B'ᵀ
  let wp := b' - (P.eta / 2) • G'
  -- R11 TEST
  let callT : CallQ d :=
    if st.first then callO c 0 0 0 (1 - P.eps) Pp wp ((1 - P.eps) ^ 2 / (P.Ne * d * 8))
    else callO c (st.B * st.Bᵀ) st.b (LT P - st.k) (rB P / 2) Pp wp (rB P ^ 2 / (P.Ne * d * 8))
  match apO orc c callT with
  | none => .guard
  | some p' =>
    -- R12 FIRE
    if P.eta * (l' - G' ⬝ᵥ p') - 2 * (p' ⬝ᵥ (Pp *ᵥ p') / 2 - b' ⬝ᵥ p' + k') ≤ -P.rho + P.eHat then
      .run (init P d)
    else
    -- R13 WMU
    let s5 := rnd P.p (P.eta * Y * P.nu / q)
    let wmu := st.mu - s5 • w
    if (2 * P.W) ^ 2 < wmu ⬝ᵥ wmu then .guard else
    -- R14 LINE
    match apO orc c (callO c Pp b' (Lmu P - k') (rB P / 2) Pp (Pp *ᵥ wmu) (eBL P d n)) with
    | none => .guard
    -- R15 COMMIT
    | some mu' => .run ⟨false, mu', A', B', b', k', G', l'⟩

/-- `stepO` in mode `run` is `tailY` at R5's observation. -/
theorem stepO_tailY (orc : (Fin d → ℚ) → ℕ → Bool) (c : CfgO d) (n : ℕ) (st : St d) (ξ : Fin d → ℚ) (ζ : ℚ)
    (obs : ℤ) :
    stepO orc c n (.run st) ξ ζ obs = tailY orc c n st ξ (yObs c.par (ptO orc c (XO c st ξ)) ζ obs) := rfl

/-- `stepOW` in mode `run` is `tailY` at the weighted observation `Y'^w = ywQ p b0 y0 ξ Y'`. -/
theorem stepOW_tailY (b0 y0 : ℚ) (orc : (Fin d → ℚ) → ℕ → Bool) (c : CfgO d) (n : ℕ) (st : St d)
    (ξ : Fin d → ℚ) (ζ : ℚ) (obs : ℤ) :
    stepOW b0 y0 orc c n (.run st) ξ ζ obs =
      tailY orc c n st ξ (ywQ c.par.p b0 y0 ξ (yObs c.par (ptO orc c (XO c st ξ)) ζ obs)) := rfl

/-- `pt' ≥ 1`. -/
theorem ptO_ge_one (orc : (Fin d → ℚ) → ℕ → Bool) (c : CfgO d) (X : Fin d → ℚ) : 1 ≤ ptO orc c X :=
  le_max_left _ _

/-- The weighted observation lies on the grid `2^{-p}`. -/
theorem ywQ_onG (p : ℕ) (b0 y0 : ℚ) (ξ : Fin d → ℚ) (Y : ℚ) : OnG p (ywQ p b0 y0 ξ Y) := onG_rnd_s _ _

/-- **The R5w box is a change of the dither.** BL-OW's round in mode `run` (`stepOW`) is BL-O's round (`stepO`) on
the same configuration, state, draw and reading, at the dither `ζ_W = 2 (Y'^w - 2 (pt' - 1)/ε')/pt' - obs/2^p`, where
`pt' = ptO orc c X'` is the gauge play's scale and `Y'^w = rnd_p(φ' clip(Y', y0))` the weighted, clipped observation
of BL-OW's R5w computed from BL-O's R5 observation `Y'` at the true dither `ζ`. Against the R5w box of the paper
(Sec. 5): BL-OW reads `Y'`, forms `Y'^w`, and runs R7 to R15 on `Y'^w`; since `ζ'` enters BL-O's round only in R5
and `pt' ≥ 1`, BL-O's R5 at `ζ_W` yields `Y'^w` exactly (`Y'^w` is on the grid, where `rnd_p` is the identity). -/
theorem stepOW_dither (b0 y0 : ℚ) (orc : (Fin d → ℚ) → ℕ → Bool) (c : CfgO d) (n : ℕ) (st : St d)
    (ξ : Fin d → ℚ) (ζ : ℚ) (obs : ℤ) :
    stepOW b0 y0 orc c n (.run st) ξ ζ obs =
      stepO orc c n (.run st) ξ
        (zetaW c.par (ptO orc c (XO c st ξ))
          (ywQ c.par.p b0 y0 ξ (yObs c.par (ptO orc c (XO c st ξ)) ζ obs)) obs) obs := by
  rw [stepOW_tailY, stepO_tailY, yObs_zetaW c.par obs
    (ne_of_gt (lt_of_lt_of_le one_pos (ptO_ge_one orc c _))) (ywQ_onG _ _ _ _ _)]

/-- The modes `off` and `guard` stay under `stepOW`. -/
theorem stepOW_og (b0 y0 : ℚ) (orc : (Fin d → ℚ) → ℕ → Bool) (c : CfgO d) (n : ℕ) {mo : Mode d}
    (h : mo = .off ∨ mo = .guard) (ξ : Fin d → ℚ) (ζ : ℚ) (obs : ℤ) : stepOW b0 y0 orc c n mo ξ ζ obs = mo := by
  rcases h with rfl | rfl <;> rfl

end AdversarialBco.UW.ProgW
