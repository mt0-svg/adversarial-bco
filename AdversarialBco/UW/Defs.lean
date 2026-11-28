/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.AsmRec
public import AdversarialBco.StatementUW

@[expose] public section

/-!
# Theorem UW: the objects its interfaces read

The definitions that the interface Props of UW/Interfaces.lean state their bricks with. Each one follows the object of
Theorem U's proof it generalises (Poly/Df2Run.lean, Poly/Df2Layer2.lean, Bit/ShadowIface.lean, Unified/WorldCore.lean).

* **The table T4U**: `parW d n u`, Table par of the paper with the floors at
  `δ_0 = 1/N_0`, `N_0 = 15 · 2^17 d³ n⁴` (`n0W`, `NeO d n 0`), `L_f = 36 log N_0`, and the scale `u` in `η` and `ε`:
  `η = d^{1/2}/(L_f (n u)^{1/2})`, `ε = 14500 d^{3/2} L_f^5 (u/n)^{1/2}`. The record is Theorem U's `Df2OPar`, so the
  learner `df2NextAP` reads it as it reads `df2oPar d n δ`; its field `δe` holds the floor `δ_0` (every floor role:
  the caps, the guards, `s_b`), and the level `δ_c` of the events is a separate number.
* **The scale and the level**: `uF d n k = 1 + k log 2/(7 d Λ_0)` (`Λ_0 = lam0 d n = log N_0`), the level
  `lvl d n u = Λ_0 + 7 d Λ_0 (u - 1)` that the rows read, and the level of the events at the input,
  `deltaC d n k = 1/(2^k N_0) = 1/NeO d n k` (Theorem U's `δ_e` at `k`). `RunCaseUW d n δ`: `ε ≤ 1/8` at `uF d n k_δ`,
  the case in which the assembly uses the analysis (off it, the bound of `TheoremUW` exceeds `n`).
* **The reference's parameters** `RefW`: the scale `u`, the sure ranges `b0`, `y0` and the level `δc`, with the regime
  `RegimeW` (`1 ≤ u`, `ε(u) ≤ 1/4`, the brackets of `b0` and `y0`, `δc ≤ δ_0`,
  `log(1/δc) ≤ ℓ_c(u)`).
* **The sure ranges**: the weight `wgt b0 s = min(1, max(0, b0 + 1 - s))`, the clip
  `clipW y0 y = max(-y0, min(y0, y))` and the observation `obsW b0 y0 ξ Y = φ(|ξ|²) clip(Y, y0)`.
* **The weighted rounds**: `df2RoundGaW` (`df2RoundGa` with `Y` replaced by `obsW`), the reference's round
  `cRoundW` (`cRoundA` at `parW` with the weight), and the epoch round `df2RoundEW` (`df2RoundE` with the weight).
* **The weighted epoch as an epoch of Theorem U's learner** (`pathW`): the epoch learner of Df2Layer2.lean with
  the noise `eW` in place of the noise of the path, chosen so that the observation it computes is the weighted one
  (`mode_pathW`, `Y_pathW`, proved below). Every quantity of `Df2Ctx` (the state, `Y`, `ĝ`, `ŝ''`, the stopping time,
  the events) is then read on `pathW` without a new definition, and DET reads the same objects.
* **The levels of the events with sure ranges**: `bnW` (`B_n` with `u`), `b1W` (`b₁`
  with `u`), `sYW` (event (b) under the clip, `21 n + y0² log(7/δc)`), `lgW` and `leW` (event (a) at the level, for
  the bit chain only); the events `EvGW`, `EvYW`, `EvLQW`, `EvSDFW`, `EvDQW` (Theorem U's `EvG` to `EvDQ` with these
  levels; `EvGW` reads the noise of the unweighted path and the state of the weighted one).
* **The reference P° of Theorem UW on a coupled world** (Unified/WorldCore.lean with `cRoundW`): `modeU`,
  `refPlayU`, `ctxU`, `pathU`, `epU` (the weighted path of the epoch started before round `a`), `meanU`, `AzU`, `GoodU`
  (`Ω_ref`), `shRU`, `DU`, and the engine hypothesis `EngineHypUW` (`EngineHypW` on `GoodU`).
* **The bound**: `thrUW C d n δ`, the threshold of `TheoremUW`; `bRegW` (P°'s regret bound, `2ρ/η + n ε +
  (2 n log(7/δc))^{1/2}`), `deltaRefW` (its failure budget, `n (149/168) δc + δc/7`).

`kTh` and `gTh` read their `δ` only through the radius `R = 134 d (log(2d + 2))^{1/2}`, which no `δ` and no `u` change
(`parW_R`); the UW objects pass the level `δc` there.

## Junk values

`parW d n u` at `u < 0` takes `Real.sqrt u = 0`; the regime asks `1 ≤ u`. `deltaC d n k` is positive for
`d, n ≥ 1`. `eW` divides by the gauge play `pt ≥ 1`.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped Matrix

namespace AdversarialBco.UW

open AdversarialBco.RealRAM AdversarialBco.Poly AdversarialBco.Poly.Layer2 AdversarialBco.Bit.Cpl
open AdversarialBco.Unified.World
open AdversarialBco.Unified.BLO (NeO kDel)

variable {d : ℕ}

/-! ## The table T4U -/

/-- `N_0 = 15 · 2^17 d³ n⁴`; the floor is `δ_0 = 1/N_0`. -/
def n0W (d n : ℕ) : ℕ := NeO d n 0

/-- `Λ_0 = log N_0`. -/
noncomputable def lam0 (d n : ℕ) : ℝ := Real.log (n0W d n)

/-- The scale at `k_δ`, `u(k) = 1 + k log 2/(7 d Λ_0)`. -/
noncomputable def uF (d n k : ℕ) : ℝ := 1 + k * Real.log 2 / (7 * d * lam0 d n)

/-- The level the rows read at the scale `u`, `ℓ_c(u) = Λ_0 + 7 d Λ_0 (u - 1)`. -/
noncomputable def lvl (d n : ℕ) (u : ℝ) : ℝ := lam0 d n + 7 * d * lam0 d n * (u - 1)

/-- The level of the events at `k`: `δ_c = 1/(2^k N_0)`, Theorem U's `δ_e` at `k`. -/
noncomputable def deltaC (d n k : ℕ) : ℝ := 1 / (NeO d n k : ℝ)

/-- **T4U**: Table par with the floors at `δ_0 = 1/N_0`, `L = L_f = 36 log N_0`, and the scale `u`:
`λ = 1/(725 d L²)`, `σ² = 1/(8 L)`, `ρ = 1450 d² L³`, `η = d^{1/2}/(L (n u)^{1/2})`, `ε = 14500 d^{3/2} L⁵ u^{1/2}/n^{1/2}`,
`κ = 1/4`, `θ = 1`, `α = 1/4`, `c₁ = 8`, `γ = 1/100`, `κ₀ = (1 - λ)^{-2}`, `R = 134 d (log(2d + 2))^{1/2}`,
`s_b = δ_0²/(R (R + 1))`. The field `δe` is the floor `δ_0`; `δ1 = 5 n δ_0/4` keeps `δe = 4 δ1/(5 n)` of `df2oPar`. -/
noncomputable def parW (d n : ℕ) (u : ℝ) : Df2OPar :=
  let δ0 : ℝ := 1 / (n0W d n : ℝ)
  let Le := df2C0 * Real.log (1 / δ0)
  let lam := 1 / (df2oClam * d * Le ^ 2)
  let eps := 20 * df2oClam * (d * Real.sqrt d) * Le ^ 5 * Real.sqrt u / Real.sqrt n
  let R := 134 * d * Real.sqrt (Real.log (2 * d + 2))
  let δ1 := 5 * n * δ0 / 4
  { δ1 := δ1, δe := δ0, Le := Le, lam := lam, eta := Real.sqrt d / (Le * Real.sqrt (n * u)), sig2 := 1 / (8 * Le),
    rho := 2 * df2oClam * d ^ 2 * Le ^ 3, eps := eps, kap := 1 / 4, theta := 1, alpha := 1 / 4, c1 := 8,
    gam := 1 / 100, k0 := ((1 - lam) ^ 2)⁻¹, R := R, sb := δ0 ^ 2 / (R * (R + 1)),
    j := ⌈Real.logb 2 (n * R * (R + 7) / (δ1 * eps))⌉₊ }

/-- The radius of T4U is that of every `df2oPar`. -/
theorem parW_R (d n : ℕ) (u δ : ℝ) : (parW d n u).R = (df2oPar d n δ).R := rfl

/-- The case of the assembly: `ε(u_δ) ≤ 1/8` at the scale `u_δ = uF d n k_δ`. The program has no cap on its scale
(UW/ProgPure.lean): it runs at `u' = u_up` on every input. In the case, the reference at the program's values is in
its regime `RegimeW`, with `u_δ ≤ u' ≤ uF d n (k_δ + 1)` (UW/ParamW.lean). Off the case, `ε(u_δ) > 1/8` makes the
bound of `TheoremUW` exceed `n` once `C_Λ ≥ 8 · 14500` (`C` is existential in the statement), whatever the program
does. -/
def RunCaseUW (d n : ℕ) (δ : ℚ) : Prop := (parW d n (uF d n (kDel δ))).eps ≤ 1 / 8

/-! ## The reference's parameters -/

/-- The parameters of the reference of Theorem UW: the scale `u`, the sure ranges `b0`, `y0`, the level `δc`. -/
structure RefW where
  u : ℝ
  b0 : ℝ
  y0 : ℝ
  δc : ℝ

/-- The regime of the reference: `d, n ≥ 1`, `1 ≤ u`, `ε(u) ≤ 1/4`,
`b0 ∈ [2d + 36Λ_0 + 2, 2d + 36Λ_0 + 3]`, `y0 ∈ [10 + 18/ε + 10 (12Λ_0)^{1/2}, 11 + 18/ε + 10 (36Λ_0)^{1/2}]`,
`0 < δc ≤ δ_0`, `log(1/δc) ≤ ℓ_c(u)`. -/
structure RegimeW (d n : ℕ) (ρ : RefW) : Prop where
  hd : 1 ≤ d
  hn : 1 ≤ n
  hu : 1 ≤ ρ.u
  heps : (parW d n ρ.u).eps ≤ 1 / 4
  b0_lo : 2 * d + 36 * lam0 d n + 2 ≤ ρ.b0
  b0_hi : ρ.b0 ≤ 2 * d + 36 * lam0 d n + 3
  y0_lo : 10 + 18 / (parW d n ρ.u).eps + 10 * Real.sqrt (12 * lam0 d n) ≤ ρ.y0
  y0_hi : ρ.y0 ≤ 11 + 18 / (parW d n ρ.u).eps + 10 * Real.sqrt (36 * lam0 d n)
  dc_pos : 0 < ρ.δc
  dc_le : ρ.δc ≤ 1 / (n0W d n : ℝ)
  dc_lvl : Real.log (1 / ρ.δc) ≤ lvl d n ρ.u

/-! ## The bound -/

/-- The threshold of `TheoremUW`: `C (d^{3/2} √n log^5(2dn) + d √(n log(2/δ)) log^{9/2}(2dn))`. -/
noncomputable def thrUW (C : ℝ) (d n : ℕ) (δ : ℚ) : ℝ :=
  C * ((d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n * Real.log (2 * d * n) ^ 5 +
    d * Real.sqrt (n * Real.log (2 / (δ : ℝ))) * Real.log (2 * d * n) ^ (9 / 2 : ℝ))

/-- P°'s regret bound at T4U: `2ρ/η + n ε + (2 n log(7/δc))^{1/2}` (`bReg` with the Azuma term at the level). -/
noncomputable def bRegW (d n : ℕ) (u δc : ℝ) : ℝ :=
  2 * ((parW d n u).rho / (parW d n u).eta) + n * (parW d n u).eps + Real.sqrt (2 * n * Real.log (7 / δc))

/-- The failure budget of P°'s analysis at the level `δc`: `n (149/168) δc + δc/7` (`deltaRef` at `δc`). -/
noncomputable def deltaRefW (n : ℕ) (δc : ℝ) : ℝ := n * (149 / 168 * δc) + δc / 7

/-! ## The levels of the events with sure ranges -/

/-- `B_n = λ L² (1 + (10 d n u)^{1/2} + d² L u/ε)`. -/
noncomputable def bnW (p : Df2OPar) (d n : ℕ) (u : ℝ) : ℝ :=
  p.lam * p.Le ^ 2 * (1 + Real.sqrt (10 * d * n * u) + (d : ℝ) ^ 2 * p.Le * u / p.eps)

/-- `b₁ = 1 + (1/λ) ((11/20) (10 d n L u)^{1/2} + (13/100) d^{3/2} L² u/ε)`. -/
noncomputable def b1W (p : Df2OPar) (d n : ℕ) (u : ℝ) : ℝ :=
  1 + 1 / p.lam * (11 / 20 * Real.sqrt (10 * d * n * p.Le * u) + 13 / 100 * (d * Real.sqrt d) * p.Le ^ 2 * u / p.eps)

/-- Event (b) under the clip: `s_Y = 21 n + y0² log(7/δc)`. -/
noncomputable def sYW (n : ℕ) (y0 δc : ℝ) : ℝ := 21 * n + y0 ^ 2 * Real.log (7 / δc)

/-- The level of event (a), `x = log(14 n/δc)`. -/
noncomputable def lgW (n : ℕ) (δc : ℝ) : ℝ := Real.log (14 * n / δc)

/-- `L_e = 36 log(1/δc)`, the gauge level of event (a) (`π_x ≤ L_e^{1/2}`). -/
noncomputable def leW (δc : ℝ) : ℝ := df2C0 * Real.log (1 / δc)

/-! ## The sure ranges -/

/-- The weight `φ(s) = min(1, max(0, b0 + 1 - s))`: `1` on `[0, b0]`, `0` on `[b0 + 1, ∞)`. -/
noncomputable def wgt (b0 s : ℝ) : ℝ := min 1 (max 0 (b0 + 1 - s))

/-- The clip `clip(y, y0) = max(-y0, min(y0, y))`. -/
noncomputable def clipW (y0 y : ℝ) : ℝ := max (-y0) (min y0 y)

/-- The observation with sure ranges, `Y^w = φ(|ξ|²) clip(Y, y0)`. -/
noncomputable def obsW (b0 y0 : ℝ) (ξ : Fin d → ℝ) (Y : ℝ) : ℝ := wgt b0 (ξ ⬝ᵥ ξ) * clipW y0 Y

/-! ## The weighted rounds -/

open Classical in
/-- `df2RoundGa` with the observation weighted and clipped. -/
noncomputable def df2RoundGaW (p : Df2OPar) (b0 y0 : ℝ) (n : ℕ) (K : Set (E d)) (Ps : PgSp d) (ga : E d → ℝ)
    (ap : ApFun d) (ft : E d → ℝ) (nt : ℝ) (ξ : Fin d → ℝ) (ζ : ℝ) : Df2Mode d → E d × Df2Mode d
  | .off => (0, .off)
  | .guard => if pgMu Ps + pgOp Ps 0 ∈ K then (pgMu Ps + pgOp Ps 0, .guard) else (0, .off)
  | .run st =>
    let w := st.A *ᵥ ξ
    let X := st.mu + (1 - p.lam) • w
    let pt := max 1 (ga (WithLp.toLp 2 X) / (1 - p.eps))
    let x := pgMu Ps + pgOp Ps (WithLp.toLp 2 (pt⁻¹ • X))
    if x ∈ K then
      (x, df2NextAP ap p n (df2Keps K Ps p.R p.eps) st ξ w
        (obsW b0 y0 ξ (pt * (ft x + nt + ζ) / 2 + 2 * (pt - 1) / p.eps)))
    else (0, .off)

/-- The round of the reference P° of Theorem UW at the position `q` with the routine `ap`: `cRoundA` at T4U with
the observation weighted and clipped, at the exact gauge of `kTh`. -/
noncomputable def cRoundW (n : ℕ) (ρ : RefW) (K : Set (E d)) (q : PgSp d) (ap : ApFun d) (ft : E d → ℝ) (nt : ℝ)
    (ξ : Fin d → ℝ) (ζ : ℝ) (m : Df2Mode d) : E d × Df2Mode d :=
  df2RoundGaW (parW d n ρ.u) ρ.b0 ρ.y0 n K q (gauge (kTh n ρ.δc K q)) ap ft nt ξ ζ m

/-- `df2RoundE` with the observation weighted and clipped: the epoch round of the reference of Theorem UW. -/
noncomputable def df2RoundEW (c : Df2Ctx d) (b0 y0 : ℝ) (ap : ApFun d) (g : E d → ℝ) (e : ℝ) (ξ : Fin d → ℝ) :
    Df2Mode d → (Fin d → ℝ) × Df2Mode d
  | .off => (0, .off)
  | .guard => (0, .guard)
  | .run st =>
    let w := st.A *ᵥ ξ
    let X := st.mu + (1 - c.p.lam) • w
    let pt := df2Pip c.p c.Kt (WithLp.toLp 2 X)
    (pt⁻¹ • X, df2NextAP ap c.p c.n (df2KepsOf c.Kt c.p.eps) st ξ w
      (obsW b0 y0 ξ (pt * (g (WithLp.toLp 2 (pt⁻¹ • X)) + e) + 2 * (pt - 1) / c.p.eps)))

/-- The modes of the weighted epoch on the path `π`. -/
noncomputable def modeEW (c : Df2Ctx d) (b0 y0 : ℝ) (π : Df2Path d) : ℕ → Df2Mode d
  | 0 => .run (df2Init c.p d)
  | s + 1 => (df2RoundEW c b0 y0 (c.ap s) (π.g s) (π.e s) (π.xi s) (modeEW c b0 y0 π s)).2

/-- The noise that makes Theorem U's epoch learner observe the weighted observation in round `s`:
`e^w = (Y^w - 2 (pt - 1)/ε)/pt - g(X/pt)`, with `Y^w = obsW b0 y0 ξ Y`; the noise of the path off the mode `run`. -/
noncomputable def eW (c : Df2Ctx d) (b0 y0 : ℝ) (π : Df2Path d) (s : ℕ) : ℝ :=
  match modeEW c b0 y0 π s with
  | .run st =>
    let X := st.mu + (1 - c.p.lam) • (st.A *ᵥ π.xi s)
    let pt := df2Pip c.p c.Kt (WithLp.toLp 2 X)
    let gx := π.g s (WithLp.toLp 2 (pt⁻¹ • X))
    (obsW b0 y0 (π.xi s) (pt * (gx + π.e s) + 2 * (pt - 1) / c.p.eps) - 2 * (pt - 1) / c.p.eps) / pt - gx
  | _ => π.e s

/-- **The weighted epoch as an epoch of Theorem U's learner**: the path with the noise `eW`. -/
noncomputable def pathW (c : Df2Ctx d) (b0 y0 : ℝ) (π : Df2Path d) : Df2Path d := ⟨π.g, eW c b0 y0 π, π.xi⟩

theorem df2Pip_pos (p : Df2OPar) (Kt : Set (E d)) (x : E d) : 0 < df2Pip p Kt x :=
  lt_of_lt_of_le one_pos (le_max_left _ _)

/-- On the reweighted path, Theorem U's epoch round is the weighted round. -/
theorem roundE_pathW (c : Df2Ctx d) (b0 y0 : ℝ) (π : Df2Path d) (s : ℕ) :
    df2RoundE c (c.ap s) (π.g s) (eW c b0 y0 π s) (π.xi s) (modeEW c b0 y0 π s) =
      df2RoundEW c b0 y0 (c.ap s) (π.g s) (π.e s) (π.xi s) (modeEW c b0 y0 π s) := by
  unfold eW
  cases h : modeEW c b0 y0 π s with
  | off => rfl
  | guard => rfl
  | run st =>
    simp only [df2RoundE, df2RoundEW]
    have hpt := df2Pip_pos c.p c.Kt (WithLp.toLp 2 (st.mu + (1 - c.p.lam) • (st.A *ᵥ π.xi s)))
    congr 2
    field_simp
    ring

/-- **The path trick**: the modes of Theorem U's epoch learner on `pathW` are those of the weighted epoch. -/
theorem mode_pathW (c : Df2Ctx d) (b0 y0 : ℝ) (π : Df2Path d) (s : ℕ) :
    c.mode (pathW c b0 y0 π) s = modeEW c b0 y0 π s := by
  induction s with
  | zero => rfl
  | succ s ih =>
    show (df2RoundE c (c.ap s) (π.g s) (eW c b0 y0 π s) (π.xi s) (c.mode (pathW c b0 y0 π) s)).2 = _
    rw [ih, roundE_pathW]
    rfl

/-- On `pathW`, the observation that Theorem U's epoch learner computes in a round in mode `run` is the weighted
one. -/
theorem Y_pathW (c : Df2Ctx d) (b0 y0 : ℝ) (π : Df2Path d) (s : ℕ) (st : Df2St d)
    (h : modeEW c b0 y0 π s = .run st) :
    c.Y (pathW c b0 y0 π) s =
      obsW b0 y0 (π.xi s) (c.pip (pathW c b0 y0 π) s * (π.g s (WithLp.toLp 2 (c.play (pathW c b0 y0 π) s)) + π.e s) +
        2 * (c.pip (pathW c b0 y0 π) s - 1) / c.p.eps) := by
  have hst : c.st (pathW c b0 y0 π) s = st := by
    simp only [Df2Ctx.st, mode_pathW, h, Df2Mode.stOr]
  have hpt : 0 < c.pip (pathW c b0 y0 π) s := df2Pip_pos c.p c.Kt (WithLp.toLp 2 (c.X (pathW c b0 y0 π) s))
  simp only [Df2Ctx.Y, Df2Ctx.play]
  show c.pip (pathW c b0 y0 π) s * (π.g s _ + eW c b0 y0 π s) + _ = _
  have he : eW c b0 y0 π s = (obsW b0 y0 (π.xi s) (c.pip (pathW c b0 y0 π) s *
      (π.g s (WithLp.toLp 2 ((c.pip (pathW c b0 y0 π) s)⁻¹ • c.X (pathW c b0 y0 π) s)) + π.e s) +
        2 * (c.pip (pathW c b0 y0 π) s - 1) / c.p.eps) - 2 * (c.pip (pathW c b0 y0 π) s - 1) / c.p.eps) /
      c.pip (pathW c b0 y0 π) s - π.g s (WithLp.toLp 2 ((c.pip (pathW c b0 y0 π) s)⁻¹ • c.X (pathW c b0 y0 π) s)) := by
    unfold eW
    rw [h]
    simp only [Df2Ctx.pip, Df2Ctx.X, Df2Ctx.w, hst]
    rfl
  rw [he]
  set P := c.pip (pathW c b0 y0 π) s
  set O := obsW b0 y0 (π.xi s) (P * (π.g s (WithLp.toLp 2 (P⁻¹ • c.X (pathW c b0 y0 π) s)) + π.e s) +
    2 * (P - 1) / c.p.eps)
  field_simp
  ring

/-! ## The events with sure ranges, on the weighted epoch -/

/-- Event (a) at the level, for the bit chain only: for `s ≤ τ`, the noise of the unweighted path
`|e_s| ≤ x^{1/2}`, the gauge of the sample of the weighted epoch `π(X_s) ≤ L_e^{1/2}`, `|ξ_s|² ≤ (8d/3) x`. -/
def EvGW (c : Df2Ctx d) (π πw : Df2Path d) (lg le : ℝ) (m : ℕ) : Prop :=
  ∀ s ≤ c.tau πw m, |π.e s| ≤ Real.sqrt lg ∧ gauge c.Kt (WithLp.toLp 2 (c.X πw s)) ≤ Real.sqrt le ∧
    π.xi s ⬝ᵥ π.xi s ≤ 8 * d / 3 * lg

/-- Event (b) under the clip: `∑_{s ≤ τ} (Y^w_s)² ≤ s_Y`. -/
def EvYW (c : Df2Ctx d) (πw : Df2Path d) (sY : ℝ) (m : ℕ) : Prop :=
  ∑ s ∈ Finset.range (c.tau πw m + 1), c.Y πw s ^ 2 ≤ sY

/-- Event (c), LQ, at the level `b1`. -/
def EvLQW (c : Df2Ctx d) (πw : Df2Path d) (b1 : ℝ) (m : ℕ) : Prop :=
  ∀ t ≤ c.tau πw m, ∀ y : Fin d → ℝ, oNorm y ≤ c.p.R → y ∈ c.SS πw t →
    |∑ u ∈ Finset.range (t + 1), (c.ghat πw u - c.sGrad πw u) ⬝ᵥ (y - (c.st πw u).mu)| ≤ b1

/-- Event (d), S-DF, at the level `Bn`. -/
def EvSDFW (c : Df2Ctx d) (πw : Df2Path d) (Bn : ℝ) (m : ℕ) : Prop :=
  ∀ t ≤ c.tau πw m, ∀ v : Fin d → ℝ,
    |df2Sq (c.Pn πw t - c.PBar πw (t + 1)) v| ≤ 4 * c.p.kap * c.p.eta * Bn * df2Sq (c.PBar πw t) v

/-- Event (e), DQ, at the level `Bn`. -/
def EvDQW (c : Df2Ctx d) (πw : Df2Path d) (Bn : ℝ) (m : ℕ) : Prop :=
  ∀ t ≤ c.tau πw m, ∀ y : Fin d → ℝ, oNorm y ≤ c.p.R → y ∈ c.SS πw t →
    |c.GG πw t y| ≤ Bn / (c.p.Le * c.p.lam ^ 2)

/-! ## The reference P° of Theorem UW on a coupled world -/

section Ref

variable {n : ℕ} {K : Set (E d)} {Ω : Type} [MeasurableSpace Ω] {W : CWorld d Ω}

/-- The mode of P° before round `t` (`RunW.mode` with `cRoundW`). -/
noncomputable def modeU (B : RunW d n K W) (ρ : RefW) : ℕ → Ω → Df2Mode d
  | 0, _ => .run (df2Init (parW d n ρ.u) d)
  | t + 1, ω => (cRoundW n ρ K (B.pos ω) (apAdv (B.adv t ω (modeU B ρ t ω))) (B.lossR t ω) (W.nz t ω)
      (W.xi t ω) (B.zeta t ω (modeU B ρ t ω)) (modeU B ρ t ω)).2

/-- The play of P° in round `t`. -/
noncomputable def refPlayU (B : RunW d n K W) (ρ : RefW) (t : ℕ) (ω : Ω) : E d :=
  (cRoundW n ρ K (B.pos ω) (apAdv (B.adv t ω (modeU B ρ t ω))) (B.lossR t ω) (W.nz t ω) (W.xi t ω)
    (B.zeta t ω (modeU B ρ t ω)) (modeU B ρ t ω)).1

/-- The noise of P°'s path in round `t`: `(ε_t + ζ*_t)/2`. -/
noncomputable def eRefU (B : RunW d n K W) (ρ : RefW) (t : ℕ) (ω : Ω) : ℝ :=
  (W.nz t ω + B.zeta t ω (modeU B ρ t ω)) / 2

/-- The context of P°'s virtual epoch started before round `a`. -/
noncomputable def ctxU (B : RunW d n K W) (ρ : RefW) (a : ℕ) (ω : Ω) : Df2Ctx d :=
  ⟨parW d n ρ.u, n, kTh n ρ.δc K (B.pos ω), fun s => apAdv (B.adv (a + s) ω (modeU B ρ (a + s) ω))⟩

/-- The (unweighted) path of P°'s virtual epoch started before round `a`. -/
noncomputable def pathU (B : RunW d n K W) (ρ : RefW) (a : ℕ) (ω : Ω) : Df2Path d :=
  ⟨fun s => gTh n ρ.δc K (fun t => B.F.L t (lamAtW n B.F.lam a s ω)) a s (B.pos ω), fun s => eRefU B ρ (a + s) ω,
    fun s => W.xi (a + s) ω⟩

/-- The weighted path of P°'s virtual epoch started before round `a`. -/
noncomputable def epU (B : RunW d n K W) (ρ : RefW) (a : ℕ) (ω : Ω) : Df2Path d :=
  pathW (ctxU B ρ a ω) ρ.b0 ρ.y0 (pathU B ρ a ω)

/-- The mean loss of round `t` of P° given the past. -/
noncomputable def meanU (B : RunW d n K W) (ρ : RefW) (t : ℕ) (ω : Ω) : ℝ :=
  ∫ z, B.loss ω t ((cRoundW n ρ K (B.pos ω) apCall (B.lossR t ω) 0 z 0 (modeU B ρ t ω)).1) ∂gaussK d

/-- The Azuma event of P° at the level `δc`. -/
def AzU (B : RunW d n K W) (ρ : RefW) (ω : Ω) : Prop :=
  ∑ t ∈ Finset.range n, B.loss ω t (refPlayU B ρ t ω) ≤
    ∑ t ∈ Finset.range n, meanU B ρ t ω + Real.sqrt (2 * n * Real.log (7 / ρ.δc))

/-- `Ω_ref` of Theorem UW: every virtual epoch of P° meets event (a) at the level and the four events with sure
ranges at T4U at its horizon, and the Azuma event holds. -/
def GoodU (B : RunW d n K W) (ρ : RefW) (ω : Ω) : Prop :=
  (∀ a < n,
    EvGW (ctxU B ρ a ω) (pathU B ρ a ω) (epU B ρ a ω) (lgW n ρ.δc) (leW ρ.δc) (n - a) ∧
    EvYW (ctxU B ρ a ω) (epU B ρ a ω) (sYW n ρ.y0 ρ.δc) (n - a) ∧
    EvLQW (ctxU B ρ a ω) (epU B ρ a ω) (b1W (parW d n ρ.u) d n ρ.u) (n - a) ∧
    EvSDFW (ctxU B ρ a ω) (epU B ρ a ω) (bnW (parW d n ρ.u) d n ρ.u) (n - a) ∧
    EvDQW (ctxU B ρ a ω) (epU B ρ a ω) (bnW (parW d n ρ.u) d n ρ.u) (n - a)) ∧
  AzU B ρ ω

/-- The shift of round `t` on P°'s run. -/
noncomputable def shRU (B : RunW d n K W) (ρ : RefW) (t : ℕ) (ω : Ω) : ℝ × ℝ := B.sh t ω (modeU B ρ t ω)

/-- Round `t` decouples. -/
def DU (B : RunW d n K W) (ρ : RefW) (t : ℕ) (ω : Ω) : Prop :=
  B.zeta t ω (modeU B ρ t ω) ≠ (shRU B ρ t ω).1 + (shRU B ρ t ω).2 * W.zz t ω 0 / 2

/-- Step 1 of SHADOW on the good events of Theorem UW (`EngineHypW` with P° of Theorem UW and `GoodU`). -/
structure EngineHypUW (B : RunW d n K W) (ρ : RefW) (κ0 κ1 : ℝ) : Prop where
  shift : ∀ ω, B.Case ρ.δc ω → GoodU B ρ ω → ω ∈ B.bits → ∀ t < n, (∀ s < t, ¬ DU B ρ s ω) →
    0 < (shRU B ρ t ω).2 ∧ tvB (shRU B ρ t ω).1 (shRU B ρ t ω).2 ≤ κ0 + κ1 * |W.nz t ω|
  regret : ∀ ω, B.Case ρ.δc ω → GoodU B ρ ω → ω ∈ B.bits → (∀ s < n, ¬ DU B ρ s ω) →
    ∑ t ∈ Finset.range n, B.loss ω t (B.play t ω) ≤ ∑ t ∈ Finset.range n, B.loss ω t (refPlayU B ρ t ω) + 1

end Ref

end AdversarialBco.UW
