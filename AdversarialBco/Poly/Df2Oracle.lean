/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import Mathlib

@[expose] public section

/-!
# DF2-O: the projection subroutine AP = ELL-cap, definitions and interface statements

The subroutine AP of the learner DF2-O is Procedure ELL-cap for `d ≥ 2` and Procedure ELL-1 for `d = 1`, of
Appendix E of the paper (PO below), with the Lipschitz constant `L_F = tr(P) (R + |w|)` in place of `‖P‖ (R + |w|)`. This file defines the
procedures as functions of their inputs and states what PO proves of them; the machine layer proves that the program
computes these functions, and `Df2OracleProof.lean` proves the statements.

Carriers: points are `Fin d → ℝ`, matrices `Matrix (Fin d) (Fin d) ℝ`, as in `Df2R1.lean`; the norm is the Euclidean
one, `oNorm v = (v ⬝ᵥ v)^{1/2}` (the norm of `Fin d → ℝ` in Mathlib is the sup norm, which no statement here reads).
The body `Q` is a set: a membership call is the question `x ∈ Q`, answered exactly. `R` is the radius of the ball
`B_R` that contains the bodies (`R = 134 d (log (2d + 2))^{1/2}`); it is an argument.

Definitions, in the order.
* `oGauge`: the gauge `γ(x) = inf {t > 0 : a₀ + (x - a₀)/t ∈ Q}` of `Q` about `a₀` (first paragraph).
* `oBisect`, `oGaugeVal`, `oGaugeValCap`: the value of the gauge with error `η` (first paragraph):
  bisection on `t` over `[|x - a₀|/(2R), |x - a₀|/r]` for `⌈log₂ (|x - a₀|/(r η))⌉` steps, the question being
  `a₀ + (x - a₀)/t ∈ Q`, returning the upper end; `0` at `x = a₀`. The capped value fails when that number of steps
  exceeds `B` (stop (c2)).
* `LineWin`, `lineFirst`, `lineHalve`, `lineLoop`, `line`: Procedure LINE on the values `ev1 s η` of a
  function of one variable, asked with error `η`, which may fail; with at most `J` halvings (stop (c1)).
* `sep`: Procedure SEP: LINE along each coordinate, then the vector `g` of Lemma E.1.
* `ccUpdate`: the central cut of Lemma E.4.
* `ellConsts`, `ellStep`, `ellLoop`, `ellCap`: Procedure ELL-cap with its stops (c0) to (c4).
* `ellOne`: Procedure ELL-1, the case `d = 1`, on `ℝ`.
* `apCall`: the subroutine AP of DF2-O: `ellOne` on the coordinate line when `d = 1`, `ellCap` otherwise.

Statements.
* `LemmaGAUGE` (first paragraph): for `Q` closed and convex with `B(a₀, r) ⊆ Q ⊆ B_R`, the gauge is convex
  and `(1/r)`-Lipschitz, `|x - a₀|/(2R) ≤ γ(x) ≤ |x - a₀|/r`, and `γ(x) ≤ 1` exactly when `x ∈ Q`.
* `LemmaGVAL`, `LemmaGCAP` (first paragraph and stop (c2)): the value by bisection is within `η` of `γ`
  at every point and every error `η > 0`; the capped value does not fail at `|x - a₀| ≤ 3R` with `η ≥ η_min`.
* `LemmaCC`, `LemmaBALL`: the central cut and the determinant bound from an inscribed ball.
* `LemmaLINE`: for a convex `L`-Lipschitz function whose values are read with their errors at the
  queries LINE makes (points of `[0, ℓ]`, errors at least `τ ℓ 4^{-J}/1600`), LINE with at most
  `J = ⌈log₂ (8L/τ)⌉` halvings returns `s ∈ [0, ℓ]` and `δ` with `ℓ 4^{-(J+1)} ≤ δ ≤ ℓ/4` and an exact second
  difference at most `τ δ/2 + τ δ/100` (the measured one at most `τ δ/2`, and the three inner values of the window
  have error at most `τ δ/400`).
* `LemmaSEP`: for a convex `L`-Lipschitz `h` whose values are read with their errors at the queries SEP
  makes (points within `2 ℓ₁` of `y₀`, errors at least `η_min = (τ ℓ₁/1600) 2^{-3d(J+1)}`, PO's count part of the
  lemma), `|y - y₀| ≤ (64/63) ℓ₁` and `h(z) ≥ h(y) + ⟨g, z - y⟩ - τ |z - y|₁` for every `z`.
* `PropELL` (Propositions ELL and ELL-cap (b)): for `d ≥ 2`, on a closed convex `Q` with
  `B(a₀, r) ⊆ Q ⊆ B_R`, `P` positive definite and `e > 0`, ELL-cap returns a point of `Q` within `e` of the
  infimum of `F(x) = |x - w|²_P/2` over `Q`.
* `PropELLcap` (Proposition ELL-cap (a)): on every input ELL-cap fails or returns a point of `Q` of norm at most `R`.
* `PropELL1` (Proposition ELL-1): (a) on every input ELL-1 fails or returns a point of `Q ∩ [-R, R]`; (b) on an
  interval `Q` with `[a₀ - r, a₀ + r] ⊆ Q ⊆ [-R, R]`, `p > 0`, `e > 0`, it returns a point of `Q` within `e` of the
  infimum of `p (x - w)²/2`.
* `PropAP` ((SPEC-AP) for `apCall`, at every accuracy `e > 0`): (a) for `d ≥ 1` and the hypotheses of
  `PropELL`, `apCall` returns a point of `Q` within `e` of the infimum of `F` over `Q`; (b) on every input it fails or
  returns a point of `Q` of norm at most `R`.

Not stated here: the counts of membership calls of Propositions ELL and ELL-cap (a) and of Lemmas LINE and SEP. The
machine layer counts the steps of the program, membership calls among them, and bounds them with the caps `N`, `J`,
`B`, `m` read off these definitions; the arguments of the calls are bounded in the analysis of the learner. What
`PropELL` needs of the counts, the region and the least error of the queries of LINE and SEP, is in the accuracy
hypotheses of `LemmaLINE` and `LemmaSEP`, and `LemmaGCAP` turns it into "the stop (c2) does not occur".

Junk values. `x / 0 = 0`, `Real.sqrt` of a negative number is `0`, `Real.logb 2 x = log |x| / log 2`,
`⌈x⌉₊ = 0` for `x ≤ 0`, and `sInf` of an empty set of reals is `0` (`oGauge` of a point `x ≠ a₀` with no `t > 0`
in its set; `oGauge` is read under `B(a₀, r) ⊆ Q`, where the set holds every `t ≥ |x - a₀|/r`). ELL-cap computes its
constants only after the stop (c0); they are positive when `0 < r ≤ R`, `e > 0`, `d ≥ 1` and `tr P > 0`. On other
inputs they may be junk; only `PropELLcap` and `PropAP` (b) speak of these, and there every returned point is still a
recorded one. `ccUpdate` divides by `(cᵀ A c)^{1/2}`, `d + 1` and `d² - 1`: `LemmaCC` assumes `d ≥ 2`, `A` positive
definite and `c ≠ 0`. Under the hypotheses of `PropELL` ELL-cap calls it with `c ≠ 0` (step 1: `|a| > R > 0`; step 2:
stop (c3); step 3: the early return); on other inputs it may call it with `c = 0` (step 1 at `a = 0` when
`r ≤ R < 0`), and the junk update is read only by `PropELLcap` and `PropAP` (b). `ellIn` reads `A⁻¹`, Mathlib's
inverse, junk `0` on a singular `A`; it is read on positive definite `A` only. `LineWin.spread` divides by the
spacing, positive when `ℓ > 0`. `sep` takes the least of the scales `δ_i`, `0` when `d = 0`. Every error asked by
LINE and SEP is positive when `τ > 0` and `ℓ > 0` (`ℓ₁ > 0`, `d ≥ 1`). `ellOne` divides by `p (R + |w|)`, positive
when `p > 0` and `R > 0`; it is `0` at `R = 0`, `w = 0`, a case read only by `PropELL1` (a) and `PropAP` (b), which
hold on every input (`PropELL1` (b) has `R ≥ r > 0`).
-/

open Matrix
open scoped Matrix

namespace AdversarialBco.Poly

variable {d : ℕ}

/-! ## Norms, balls, the objective, ellipsoids -/

/-- The Euclidean norm `(v ⬝ᵥ v)^{1/2}`. -/
noncomputable def oNorm (v : Fin d → ℝ) : ℝ := Real.sqrt (v ⬝ᵥ v)

/-- The closed Euclidean ball `B(c, ρ)`. -/
def oBall (c : Fin d → ℝ) (ρ : ℝ) : Set (Fin d → ℝ) := {x | oNorm (x - c) ≤ ρ}

/-- The objective `F(x) = |x - w|²_P / 2`. -/
noncomputable def ellF (P : Matrix (Fin d) (Fin d) ℝ) (w x : Fin d → ℝ) : ℝ :=
  (1 / 2) * ((x - w) ⬝ᵥ (P *ᵥ (x - w)))

/-- `x ∈ E(A, a) = {x : (x - a)ᵀ A⁻¹ (x - a) ≤ 1}`. -/
def ellIn (A : Matrix (Fin d) (Fin d) ℝ) (a x : Fin d → ℝ) : Prop := (x - a) ⬝ᵥ (A⁻¹ *ᵥ (x - a)) ≤ 1

/-- The coordinate vector `e_i`. -/
def oUnit (i : Fin d) : Fin d → ℝ := Pi.single i 1

/-! ## The gauge and its value with an error -/

/-- The gauge of `Q` about `a₀`: `γ(x) = inf {t > 0 : a₀ + (x - a₀)/t ∈ Q}`. -/
noncomputable def oGauge (Q : Set (Fin d → ℝ)) (a0 x : Fin d → ℝ) : ℝ :=
  sInf {t : ℝ | 0 < t ∧ a0 + t⁻¹ • (x - a0) ∈ Q}

open Classical in
/-- Bisection on `[lo, hi]`: the upper end moves to the midpoint when the question holds there, else the lower end. -/
noncomputable def oBisect (Pr : ℝ → Prop) (lo hi : ℝ) : ℕ → ℝ × ℝ
  | 0 => (lo, hi)
  | j + 1 =>
    let I := oBisect Pr lo hi j
    if Pr ((I.1 + I.2) / 2) then (I.1, (I.1 + I.2) / 2) else ((I.1 + I.2) / 2, I.2)

/-- The number of bisection steps of a value at `x` with error `η`: `⌈log₂ (|x - a₀|/(r η))⌉`. -/
noncomputable def oValSteps (a0 : Fin d → ℝ) (r : ℝ) (x : Fin d → ℝ) (η : ℝ) : ℕ :=
  ⌈Real.logb 2 (oNorm (x - a0) / (r * η))⌉₊

open Classical in
/-- The value of the gauge of `Q` about `a₀` at `x` with error `η`: the upper end of the bisection on
`[|x - a₀|/(2R), |x - a₀|/r]` with the question `a₀ + (x - a₀)/t ∈ Q`; `0` at `x = a₀`. -/
noncomputable def oGaugeVal (Q : Set (Fin d → ℝ)) (a0 : Fin d → ℝ) (r R : ℝ) (x : Fin d → ℝ) (η : ℝ) : ℝ :=
  if x = a0 then 0
  else (oBisect (fun t => 0 < t ∧ a0 + t⁻¹ • (x - a0) ∈ Q) (oNorm (x - a0) / (2 * R)) (oNorm (x - a0) / r)
    (oValSteps a0 r x η)).2

/-- The value with the stop (c2): fail when it needs more than `B` steps. -/
noncomputable def oGaugeValCap (Q : Set (Fin d → ℝ)) (a0 : Fin d → ℝ) (r R : ℝ) (B : ℕ) (x : Fin d → ℝ) (η : ℝ) :
    Option ℝ :=
  if B < oValSteps a0 r x η then none else some (oGaugeVal Q a0 r R x η)

/-! ## Procedure LINE -/

/-- A window of LINE: the five points `p₀ + k λ`, `k ≤ 4`, and the values measured there. -/
structure LineWin where
  p0 : ℝ
  lam : ℝ
  v0 : ℝ
  v1 : ℝ
  v2 : ℝ
  v3 : ℝ
  v4 : ℝ

/-- The measured spread `σ₄ - σ₁` of a window, `σ_k` the chord slopes. -/
noncomputable def LineWin.spread (W : LineWin) : ℝ := ((W.v4 - W.v3) - (W.v1 - W.v0)) / W.lam

/-- The measured second difference at the middle point, `v₃ + v₁ - 2 v₂`. -/
def LineWin.sd (W : LineWin) : ℝ := W.v3 + W.v1 - 2 * W.v2

/-- The first window: `p₀ = 0`, `λ = ℓ/4`, the five values asked with error `τ λ/400`. -/
noncomputable def lineFirst (ev1 : ℝ → ℝ → Option ℝ) (ℓ τ : ℝ) : Option LineWin := do
  let lam := ℓ / 4
  let v0 ← ev1 0 (τ * lam / 400)
  let v1 ← ev1 lam (τ * lam / 400)
  let v2 ← ev1 (2 * lam) (τ * lam / 400)
  let v3 ← ev1 (3 * lam) (τ * lam / 400)
  let v4 ← ev1 (4 * lam) (τ * lam / 400)
  pure ⟨0, lam, v0, v1, v2, v3, v4⟩

/-- One halving: `[p₁, p₃]` cut into eight intervals of length `λ/4`; the six new values asked with error
`τ λ/1600`; the window of five points starting at `p₁` or the one starting at `p₂`, whichever has the smaller
measured spread (the first on a tie). -/
noncomputable def lineHalve (ev1 : ℝ → ℝ → Option ℝ) (τ : ℝ) (W : LineWin) : Option LineWin := do
  let l := W.lam / 4
  let p1 := W.p0 + W.lam
  let p2 := W.p0 + 2 * W.lam
  let u1 ← ev1 (p1 + l) (τ * W.lam / 1600)
  let u2 ← ev1 (p1 + 2 * l) (τ * W.lam / 1600)
  let u3 ← ev1 (p1 + 3 * l) (τ * W.lam / 1600)
  let u5 ← ev1 (p2 + l) (τ * W.lam / 1600)
  let u6 ← ev1 (p2 + 2 * l) (τ * W.lam / 1600)
  let u7 ← ev1 (p2 + 3 * l) (τ * W.lam / 1600)
  let A : LineWin := ⟨p1, l, W.v1, u1, u2, u3, W.v2⟩
  let B : LineWin := ⟨p2, l, W.v2, u5, u6, u7, W.v3⟩
  pure (if B.spread < A.spread then B else A)

/-- The loop of LINE with at most `j` more halvings: stop at a window whose measured second difference is at most
`τ λ/2`, returning `(p₂, λ)`; fail (stop (c1)) when no halving is left. -/
noncomputable def lineLoop (ev1 : ℝ → ℝ → Option ℝ) (τ : ℝ) : ℕ → LineWin → Option (ℝ × ℝ)
  | j, W =>
    if W.sd ≤ τ * W.lam / 2 then some (W.p0 + 2 * W.lam, W.lam)
    else match j with
      | 0 => none
      | j + 1 => lineHalve ev1 τ W >>= lineLoop ev1 τ j

/-- Procedure LINE on `[0, ℓ]` with at most `J` halvings: `(s, δ)`. -/
noncomputable def line (ev1 : ℝ → ℝ → Option ℝ) (ℓ τ : ℝ) (J : ℕ) : Option (ℝ × ℝ) :=
  lineFirst ev1 ℓ τ >>= lineLoop ev1 τ J

/-! ## Procedure SEP -/

/-- The state of SEP after some coordinates: the point `y^i`, the next length `ℓ_{i+1}`, the scales `δ`. -/
abbrev SepSt (d : ℕ) := (Fin d → ℝ) × ℝ × (Fin d → ℝ)

/-- The search along coordinate `i`: LINE on `s ↦ h(y + s e_i)` with length `ℓ`; then `y + s e_i`, the next length
`τ δ/(16 L)`, and `δ_i = δ`. -/
noncomputable def sepCoord (ev : (Fin d → ℝ) → ℝ → Option ℝ) (τ L : ℝ) (J : ℕ) (i : Fin d) (st : SepSt d) :
    Option (SepSt d) := do
  let r ← line (fun s η => ev (st.1 + s • oUnit i) η) st.2.1 τ J
  pure (st.1 + r.1 • oUnit i, τ * r.2 / (16 * L), Function.update st.2.2 i r.2)

/-- The searches along the coordinates `0, ..., k - 1` from `y⁰` with the first length `ℓ₁`. -/
noncomputable def sepCoords (ev : (Fin d → ℝ) → ℝ → Option ℝ) (y0 : Fin d → ℝ) (τ ℓ1 L : ℝ) (J : ℕ) :
    ℕ → Option (SepSt d)
  | 0 => some (y0, ℓ1, 0)
  | k + 1 => sepCoords ev y0 τ ℓ1 L J k >>= fun st => if h : k < d then sepCoord ev τ L J ⟨k, h⟩ st else some st

/-- The least of the scales, `0` when `d = 0`. -/
noncomputable def oMin (δ : Fin d → ℝ) : ℝ :=
  if h : 0 < d then Finset.univ.inf' ⟨⟨0, h⟩, Finset.mem_univ _⟩ δ else 0

open Classical in
/-- Values asked at the points `x i` with errors `η i`, for every `i`; fail if one fails. -/
noncomputable def oValsAll (ev : (Fin d → ℝ) → ℝ → Option ℝ) (x : Fin d → Fin d → ℝ) (η : Fin d → ℝ) :
    Option (Fin d → ℝ) :=
  if h : ∀ i, (ev (x i) (η i)).isSome then some fun i => (ev (x i) (η i)).get (h i) else none

/-- Procedure SEP(h, y⁰, τ, ℓ₁) for an `L`-Lipschitz `h` read through `ev`, with at most `J` halvings in each LINE:
the point `y = y^d` and the vector `g`, `g_i = (v_i⁺ - v_i⁻)/(2 δ_i)`, the values `v_i^±` at `y ± δ_i e_i` asked with
error `τ δ_i/400`. The value `v₀` at `y`, asked with error `τ min_i δ_i/400`, enters only the stop of a failed value. -/
noncomputable def sep (ev : (Fin d → ℝ) → ℝ → Option ℝ) (y0 : Fin d → ℝ) (τ ℓ1 L : ℝ) (J : ℕ) :
    Option ((Fin d → ℝ) × (Fin d → ℝ)) := do
  let st ← sepCoords ev y0 τ ℓ1 L J d
  let y := st.1
  let δ := st.2.2
  let _v0 ← ev y (τ * oMin δ / 400)
  let vp ← oValsAll ev (fun i => y + δ i • oUnit i) (fun i => τ * δ i / 400)
  let vm ← oValsAll ev (fun i => y - δ i • oUnit i) (fun i => τ * δ i / 400)
  pure (y, fun i => (vp i - vm i) / (2 * δ i))

/-! ## The central cut -/

/-- Lemma E.4: `b = A c/(cᵀ A c)^{1/2}`, `a' = a - b/(d + 1)`, `A' = (d²/(d² - 1)) (A - (2/(d + 1)) b bᵀ)`. -/
noncomputable def ccUpdate (A : Matrix (Fin d) (Fin d) ℝ) (a c : Fin d → ℝ) : Matrix (Fin d) (Fin d) ℝ × (Fin d → ℝ) :=
  let b := (Real.sqrt (c ⬝ᵥ (A *ᵥ c)))⁻¹ • (A *ᵥ c)
  ((((d : ℝ) ^ 2) / ((d : ℝ) ^ 2 - 1)) • (A - (2 / ((d : ℝ) + 1)) • vecMulVec b b), a - ((d : ℝ) + 1)⁻¹ • b)

/-! ## Procedure ELL-cap -/

/-- The constants of ELL-cap: `L_F = tr(P) (R + |w|)`, `θ = min (1, e/(3 L_F R))`, `ε_Q = θ r/2`,
`τ = ε_Q/(36 R² d^{1/2})`, `ℓ₁ = r ε_Q/(24 R)`, `N = ⌈2 d (d + 1) log (2R/(θ r))⌉ + 1`, `J = ⌈log₂ (8/(r τ))⌉`,
`η_min = (τ ℓ₁/1600) 2^{-3d(J + 1)}`, `B = ⌈log₂ (3R/(r η_min))⌉`. -/
structure EllConsts where
  τ : ℝ
  ℓ1 : ℝ
  N : ℕ
  J : ℕ
  B : ℕ

/-- The constants of ELL-cap at `(r, R, P, w, e)`. -/
noncomputable def ellConsts (r R : ℝ) (P : Matrix (Fin d) (Fin d) ℝ) (w : Fin d → ℝ) (e : ℝ) : EllConsts :=
  let LF := P.trace * (R + oNorm w)
  let θ := min 1 (e / (3 * LF * R))
  let εQ := θ * r / 2
  let τ := εQ / (36 * R ^ 2 * Real.sqrt d)
  let ℓ1 := r * εQ / (24 * R)
  let N := ⌈2 * (d : ℝ) * (d + 1) * Real.log (2 * R / (θ * r))⌉₊ + 1
  let J := ⌈Real.logb 2 (8 / (r * τ))⌉₊
  let ηmin := τ * ℓ1 / 1600 * (2 : ℝ) ^ (-(3 * (d : ℝ) * (J + 1)))
  let B := ⌈Real.logb 2 (3 * R / (r * ηmin))⌉₊
  ⟨τ, ℓ1, N, J, B⟩

/-- The state of ELL: the ellipsoid `E(A, a)` and the recorded point of least value so far. -/
structure EllSt (d : ℕ) where
  A : Matrix (Fin d) (Fin d) ℝ
  a : Fin d → ℝ
  best : Option (Fin d → ℝ)

open Classical in
/-- `a` is recorded: it replaces the recorded point when there is none or when its value is smaller. -/
noncomputable def ellRecord (P : Matrix (Fin d) (Fin d) ℝ) (w : Fin d → ℝ) (best : Option (Fin d → ℝ))
    (a : Fin d → ℝ) : Option (Fin d → ℝ) :=
  match best with
  | none => some a
  | some b => if ellF P w a < ellF P w b then some a else some b

open Classical in
/-- One step of ELL-cap: step 1 (`|a| > R`: cut by `a`), step 2 (`a ∉ Q`: SEP on the gauge, stop (c3) if `g = 0`,
cut by `g`), step 3 (record `a`; return it if `P (a - w) = 0`, else cut by `P (a - w)`). `none` is a failure,
`inr μ` a returned point. -/
noncomputable def ellStep (Q : Set (Fin d → ℝ)) (a0 : Fin d → ℝ) (r R : ℝ) (P : Matrix (Fin d) (Fin d) ℝ)
    (w : Fin d → ℝ) (k : EllConsts) (st : EllSt d) : Option (EllSt d ⊕ (Fin d → ℝ)) :=
  if R < oNorm st.a then
    let u := ccUpdate st.A st.a st.a
    some (.inl ⟨u.1, u.2, st.best⟩)
  else if st.a ∉ Q then
    match sep (oGaugeValCap Q a0 r R k.B) st.a k.τ k.ℓ1 (1 / r) k.J with
    | none => none
    | some (_, g) =>
      if g = 0 then none
      else
        let u := ccUpdate st.A st.a g
        some (.inl ⟨u.1, u.2, st.best⟩)
  else
    let best := ellRecord P w st.best st.a
    if P *ᵥ (st.a - w) = 0 then some (.inr st.a)
    else
      let u := ccUpdate st.A st.a (P *ᵥ (st.a - w))
      some (.inl ⟨u.1, u.2, best⟩)

/-- `j` steps of ELL-cap; a returned point stays returned, a failure stays a failure. -/
noncomputable def ellLoop (Q : Set (Fin d → ℝ)) (a0 : Fin d → ℝ) (r R : ℝ) (P : Matrix (Fin d) (Fin d) ℝ)
    (w : Fin d → ℝ) (k : EllConsts) : ℕ → Option (EllSt d ⊕ (Fin d → ℝ))
  | 0 => some (.inl ⟨(R ^ 2) • (1 : Matrix (Fin d) (Fin d) ℝ), 0, none⟩)
  | j + 1 =>
    match ellLoop Q a0 r R P w k j with
    | some (.inl st) => ellStep Q a0 r R P w k st
    | o => o

/-- Procedure ELL-cap(Q, a₀, r, P, w, e) with the radius `R`: stop (c0) if `r > R`; else the `N` steps from
`A₀ = R² I`, `a⁰ = 0`; the returned point, or the recorded point of least value, or fail (stop (c4)). -/
noncomputable def ellCap (Q : Set (Fin d → ℝ)) (a0 : Fin d → ℝ) (r R : ℝ) (P : Matrix (Fin d) (Fin d) ℝ)
    (w : Fin d → ℝ) (e : ℝ) : Option (Fin d → ℝ) :=
  if R < r then none
  else
    let k := ellConsts r R P w e
    match ellLoop Q a0 r R P w k k.N with
    | some (.inr μ) => some μ
    | some (.inl st) => st.best
    | none => none

/-! ## Procedure ELL-1 and the subroutine AP -/

open Classical in
/-- Bisection keeping an accepted lower end: the midpoint replaces `lo` when the question holds there, else `hi`. -/
noncomputable def oBisectLo (Pr : ℝ → Prop) (lo hi : ℝ) : ℕ → ℝ × ℝ
  | 0 => (lo, hi)
  | j + 1 =>
    let I := oBisectLo Pr lo hi j
    if Pr ((I.1 + I.2) / 2) then ((I.1 + I.2) / 2, I.2) else (I.1, (I.1 + I.2) / 2)

open Classical in
/-- Procedure ELL-1(Q, a₀, r, p, w, e) on `ℝ` with the radius `R`, `L_F = p (R + |w|)`, `ξ = e/L_F`: fail if
`r > R` or `|a₀| > R`, or if `a₀ ∉ Q`; return `w' = clamp(w, -R, R)` if `w' ∈ Q`; else bisect between `a₀` and `w'`
for `⌈log₂ (|w' - a₀|/ξ)⌉` steps and return the accepted end. -/
noncomputable def ellOne (Q : Set ℝ) (a0 r R p w e : ℝ) : Option ℝ :=
  if R < r ∨ R < |a0| then none
  else if a0 ∉ Q then none
  else
    let w' := max (-R) (min R w)
    if w' ∈ Q then some w'
    else
      let ξ := e / (p * (R + |w|))
      some (oBisectLo (· ∈ Q) a0 w' ⌈Real.logb 2 (|w' - a0| / ξ)⌉₊).1

/-- The subroutine AP of DF2-O: ELL-1 on the coordinate line when `d = 1`, ELL-cap otherwise. -/
noncomputable def apCall (Q : Set (Fin d → ℝ)) (a0 : Fin d → ℝ) (r R : ℝ) (P : Matrix (Fin d) (Fin d) ℝ)
    (w : Fin d → ℝ) (e : ℝ) : Option (Fin d → ℝ) :=
  if h : d = 1 then
    (ellOne {x | (fun _ => x) ∈ Q} (a0 ⟨0, by omega⟩) r R (P ⟨0, by omega⟩ ⟨0, by omega⟩) (w ⟨0, by omega⟩) e).map
      fun x _ => x
  else ellCap Q a0 r R P w e

/-! ## Statements -/

/-- Lemma E.4: for `d ≥ 2`, `A` positive definite and `c ≠ 0`, the matrix `A'` is positive definite,
`E(A, a) ∩ {x : ⟨c, x - a⟩ ≤ 0} ⊆ E(A', a')`, and
`det A' = det A (d²/(d² - 1))^{d-1} (d/(d + 1))² ≤ det A e^{-1/(d+1)}`. -/
def LemmaCC : Prop :=
  ∀ (d : ℕ) (A : Matrix (Fin d) (Fin d) ℝ) (a c : Fin d → ℝ), 2 ≤ d → A.PosDef → c ≠ 0 →
    (ccUpdate A a c).1.PosDef ∧
      (∀ x, ellIn A a x → c ⬝ᵥ (x - a) ≤ 0 → ellIn (ccUpdate A a c).1 (ccUpdate A a c).2 x) ∧
      (ccUpdate A a c).1.det = A.det * ((d : ℝ) ^ 2 / ((d : ℝ) ^ 2 - 1)) ^ (d - 1) * ((d : ℝ) / (d + 1)) ^ 2 ∧
      (ccUpdate A a c).1.det ≤ A.det * Real.exp (-1 / ((d : ℝ) + 1))

/-- Lemma E.5: a ball `B(b, ρ)` inside `E(A, a)`, `A` positive definite, gives `det A ≥ ρ^{2d}`. -/
def LemmaBALL : Prop :=
  ∀ (d : ℕ) (A : Matrix (Fin d) (Fin d) ℝ) (a b : Fin d → ℝ) (ρ : ℝ), A.PosDef → 0 ≤ ρ →
    (∀ x ∈ oBall b ρ, ellIn A a x) → ρ ^ (2 * d) ≤ A.det

/-- Lemma E.2: `φ` convex and `L`-Lipschitz on `ℝ`, `0 < τ ≤ L`, `ℓ > 0`, `J = ⌈log₂ (8L/τ)⌉`, and
values that do not fail and have their error at the queries LINE makes: points `s ∈ [0, ℓ]` and errors
`η ≥ τ ℓ 4^{-J}/1600` (the first window asks `τ ℓ/1600`, the `k`-th halving `τ ℓ 4^{-k}/1600`, `k ≤ J`). Then LINE
with the cap `J` returns `(s, δ)` with `0 ≤ s ≤ ℓ`, `ℓ 4^{-(J+1)} ≤ δ ≤ ℓ/4` and
`φ(s + δ) + φ(s - δ) - 2 φ(s) ≤ τ δ/2 + τ δ/100`. -/
def LemmaLINE : Prop :=
  ∀ (φ : ℝ → ℝ) (L ℓ τ : ℝ) (ev1 : ℝ → ℝ → Option ℝ), ConvexOn ℝ Set.univ φ →
    (∀ x y, |φ x - φ y| ≤ L * |x - y|) → 0 < τ → τ ≤ L → 0 < ℓ →
    (∀ s η, 0 ≤ s → s ≤ ℓ → τ * ℓ * (4 : ℝ) ^ (-(⌈Real.logb 2 (8 * L / τ)⌉₊ : ℝ)) / 1600 ≤ η →
      ∃ v, ev1 s η = some v ∧ |v - φ s| ≤ η) →
    ∃ s δ, line ev1 ℓ τ ⌈Real.logb 2 (8 * L / τ)⌉₊ = some (s, δ) ∧ 0 ≤ s ∧ s ≤ ℓ ∧
      ℓ * (4 : ℝ) ^ (-((⌈Real.logb 2 (8 * L / τ)⌉₊ : ℝ) + 1)) ≤ δ ∧ δ ≤ ℓ / 4 ∧
      φ (s + δ) + φ (s - δ) - 2 * φ s ≤ τ * δ / 2 + τ * δ / 100

/-- Lemma E.3: `d ≥ 1`, `h` convex and `L`-Lipschitz on `ℝ^d` (Euclidean norm), `0 < τ ≤ L`, `ℓ₁ > 0`,
`J = ⌈log₂ (8L/τ)⌉`, and values that do not fail and have their error at the queries SEP makes: points `x` with
`|x - y⁰| ≤ 2 ℓ₁` and errors `η ≥ η_min = (τ ℓ₁/1600) 2^{-3d(J+1)}` (the searches ask within `(64/63) ℓ₁` of `y⁰`, the
final values within `(64/63 + 1/4) ℓ₁`; `ℓ_{i+1} ≥ ℓ_i 2^{-3(J+1)}` since `16L/τ ≤ 2^{J+1}`, and every error is at
least `τ ℓ_d 4^{-J}/1600 ≥ η_min`). Then SEP with the cap `J` in each LINE returns `(y, g)` with
`|y - y⁰| ≤ (64/63) ℓ₁` and `h(z) ≥ h(y) + ⟨g, z - y⟩ - τ |z - y|₁` for every `z`. -/
def LemmaSEP : Prop :=
  ∀ (d : ℕ) (h : (Fin d → ℝ) → ℝ) (L τ ℓ1 : ℝ) (y0 : Fin d → ℝ) (ev : (Fin d → ℝ) → ℝ → Option ℝ),
    1 ≤ d → ConvexOn ℝ Set.univ h → (∀ x y, |h x - h y| ≤ L * oNorm (x - y)) → 0 < τ → τ ≤ L → 0 < ℓ1 →
    (∀ x η, oNorm (x - y0) ≤ 2 * ℓ1 →
      τ * ℓ1 / 1600 * (2 : ℝ) ^ (-(3 * (d : ℝ) * (⌈Real.logb 2 (8 * L / τ)⌉₊ + 1))) ≤ η →
      ∃ v, ev x η = some v ∧ |v - h x| ≤ η) →
    ∃ y g, sep ev y0 τ ℓ1 L ⌈Real.logb 2 (8 * L / τ)⌉₊ = some (y, g) ∧ oNorm (y - y0) ≤ 64 / 63 * ℓ1 ∧
      ∀ z, h y + g ⬝ᵥ (z - y) - τ * ∑ i, |z i - y i| ≤ h z

/-- The gauge (first paragraph): for `Q` closed and convex with `B(a₀, r) ⊆ Q ⊆ B_R` and `r > 0`, the
gauge `γ` of `Q` about `a₀` is convex and `(1/r)`-Lipschitz (Euclidean norm), `|x - a₀|/(2R) ≤ γ(x) ≤ |x - a₀|/r`,
and `γ(x) ≤ 1` exactly when `x ∈ Q`. -/
def LemmaGAUGE : Prop :=
  ∀ (d : ℕ) (Q : Set (Fin d → ℝ)) (a0 : Fin d → ℝ) (r R : ℝ), Convex ℝ Q → IsClosed Q → 0 < r → oBall a0 r ⊆ Q →
    Q ⊆ oBall 0 R →
    ConvexOn ℝ Set.univ (oGauge Q a0) ∧ (∀ x y, |oGauge Q a0 x - oGauge Q a0 y| ≤ 1 / r * oNorm (x - y)) ∧
      (∀ x, oNorm (x - a0) / (2 * R) ≤ oGauge Q a0 x ∧ oGauge Q a0 x ≤ oNorm (x - a0) / r) ∧
      ∀ x, oGauge Q a0 x ≤ 1 ↔ x ∈ Q

/-- The value of the gauge by bisection (first paragraph): for `Q` convex with `B(a₀, r) ⊆ Q ⊆ B_R` and
`r > 0`, the value at any point `x` with any error `η > 0` is within `η` of `γ(x)`. -/
def LemmaGVAL : Prop :=
  ∀ (d : ℕ) (Q : Set (Fin d → ℝ)) (a0 : Fin d → ℝ) (r R : ℝ), Convex ℝ Q → 0 < r → oBall a0 r ⊆ Q →
    Q ⊆ oBall 0 R → ∀ x η, 0 < η → |oGaugeVal Q a0 r R x η - oGauge Q a0 x| ≤ η

/-- The stop (c2) at the queries of ELL-cap (proof of Proposition ELL-cap (b)): for `r > 0`,
`η_min > 0` and a cap `B ≥ ⌈log₂ (3R/(r η_min))⌉`, the capped value at a point `x` with `|x - a₀| ≤ 3R` and an
error `η ≥ η_min` is the value. -/
def LemmaGCAP : Prop :=
  ∀ (d : ℕ) (Q : Set (Fin d → ℝ)) (a0 : Fin d → ℝ) (r R ηmin : ℝ) (B : ℕ) (x : Fin d → ℝ) (η : ℝ), 0 < r →
    0 < ηmin → ⌈Real.logb 2 (3 * R / (r * ηmin))⌉₊ ≤ B → oNorm (x - a0) ≤ 3 * R → ηmin ≤ η →
    oGaugeValCap Q a0 r R B x η = some (oGaugeVal Q a0 r R x η)

/-- Propositions ELL and ELL-cap (b): for `d ≥ 2`, `Q` closed and convex with `B(a₀, r) ⊆ Q ⊆ B_R`,
`r > 0`, `P` positive definite and `e > 0`, ELL-cap returns a point `μ ∈ Q` with `F(μ) ≤ F(x) + e` for every
`x ∈ Q`. -/
def PropELL : Prop :=
  ∀ (d : ℕ) (Q : Set (Fin d → ℝ)) (a0 : Fin d → ℝ) (r R : ℝ) (P : Matrix (Fin d) (Fin d) ℝ) (w : Fin d → ℝ)
    (e : ℝ), 2 ≤ d → Convex ℝ Q → IsClosed Q → 0 < r → oBall a0 r ⊆ Q → Q ⊆ oBall 0 R → P.PosDef → 0 < e →
    ∃ μ, ellCap Q a0 r R P w e = some μ ∧ μ ∈ Q ∧ ∀ x ∈ Q, ellF P w μ ≤ ellF P w x + e

/-- Proposition ELL-cap (a): on every input, ELL-cap fails or returns a point of `Q` of norm at
most `R`. -/
def PropELLcap : Prop :=
  ∀ (d : ℕ) (Q : Set (Fin d → ℝ)) (a0 : Fin d → ℝ) (r R : ℝ) (P : Matrix (Fin d) (Fin d) ℝ) (w : Fin d → ℝ)
    (e : ℝ), ellCap Q a0 r R P w e = none ∨ ∃ μ, ellCap Q a0 r R P w e = some μ ∧ μ ∈ Q ∧ oNorm μ ≤ R

/-- Proposition ELL-1: (a) on every input ELL-1 fails or returns a point of `Q ∩ [-R, R]`; (b) for
an interval `Q` with `[a₀ - r, a₀ + r] ⊆ Q ⊆ [-R, R]`, `r > 0`, `p > 0` and `e > 0`, it returns a point `μ ∈ Q`
with `p (μ - w)²/2 ≤ p (x - w)²/2 + e` for every `x ∈ Q`. -/
def PropELL1 : Prop :=
  ∀ (Q : Set ℝ) (a0 r R p w e : ℝ),
    (ellOne Q a0 r R p w e = none ∨ ∃ μ, ellOne Q a0 r R p w e = some μ ∧ μ ∈ Q ∧ |μ| ≤ R) ∧
    (Q.OrdConnected → Set.Icc (a0 - r) (a0 + r) ⊆ Q → Q ⊆ Set.Icc (-R) R → 0 < r → 0 < p → 0 < e →
      ∃ μ, ellOne Q a0 r R p w e = some μ ∧ μ ∈ Q ∧ ∀ x ∈ Q, p * (μ - w) ^ 2 / 2 ≤ p * (x - w) ^ 2 / 2 + e)

/-- (SPEC-AP) for the subroutine AP of DF2-O, at every accuracy `e > 0`: (a) for `d ≥ 1`, `Q` closed and convex with `B(a₀, r) ⊆ Q ⊆ B_R`, `r > 0`, `P`
positive definite and `e > 0`, `apCall` returns a point `μ ∈ Q` with `F(μ) ≤ F(x) + e` for every `x ∈ Q` (`PropELL`
for `d ≥ 2`; `PropELL1` (b) on the coordinate line for `d = 1`); (b) on every input it fails or returns a point of
`Q` of norm at most `R` (`PropELLcap`; `PropELL1` (a)). -/
def PropAP : Prop :=
  ∀ (d : ℕ) (Q : Set (Fin d → ℝ)) (a0 : Fin d → ℝ) (r R : ℝ) (P : Matrix (Fin d) (Fin d) ℝ) (w : Fin d → ℝ)
    (e : ℝ),
    (1 ≤ d → Convex ℝ Q → IsClosed Q → 0 < r → oBall a0 r ⊆ Q → Q ⊆ oBall 0 R → P.PosDef → 0 < e →
      ∃ μ, apCall Q a0 r R P w e = some μ ∧ μ ∈ Q ∧ ∀ x ∈ Q, ellF P w μ ≤ ellF P w x + e) ∧
    (apCall Q a0 r R P w e = none ∨ ∃ μ, apCall Q a0 r R P w e = some μ ∧ μ ∈ Q ∧ oNorm μ ≤ R)

end AdversarialBco.Poly
