/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.XLangO
public import AdversarialBco.Poly.Df2Oracle

@[expose] public section

/-!
# UNI-CM, UNI-GAUGE, UNI-SEP: the routines and the contracts of their blocks (the interface)

UNI-CM, UNI-GAUGE and UNI-SEP (the paper's section on certified questions and the gauge). The interface that the
consumers of UNI-SEP (ELL-O of UNI-ELL, TRI-OGD-O of UNI-POS) and of the gauge (the play of UNI-PLAY) call. Proofs
are in the modules named below; this file has the definitions and the statements, as `Prop`s.

**The routines as pure functions** (computable, on `ℤ` and `ℚ`; the programs compute exactly these):

* `cmQ orc a r₀ k y`: UNI-CM, one query of the oracle at `cmPt a r₀ k y = a + (1 + 2·2^{-k}/r₀)(y - a)` with the
  precision `k`.
* `gaugeIt T a₀ x H j`, `gaugeQ`: UNI-GAUGE, `j` steps of bisection on `[0, H]` for the gauge of `x` about `a₀`, the
  question `T` at the ray point `gaugePt a₀ x H j m = a₀ + (2^j/(H m))(x - a₀)` of the counter `m` (`t = H m/2^j`),
  the ends kept as counters `(l, u)`, `0 ≤ l < u ≤ 2^j`; the value is the upper end `H u/2^j`.
* `lineZ`, `sepZ`: Procedures LINE and SEP of Poly/Df2Oracle.lean (`line`, `sep`) on the grid `2^{-E}`, in integers:
  a point is `X/2^E`, a value is `evN X/2^{eu}`, `L = 2^{eL}`, `τ = 2^{-eτ}`, `ℓ₁ = 2^{-e₁}`. The windows of LINE
  and the scales are powers of two, so every step is exact once `E ≥ e₁ + d (2J + 6 + eτ + eL)` (`SepAcc`). The
  arguments: `len₁ = 2^{E-e₁}` (the first length), `sh = 2^{eτ+4+eL}` (`ℓ_{i+1} = δ_i/sh`, that is `τ δ/(16 L)`),
  `cA = 2^{E+eτ+1}`, `cB = 2^{eu}` (the stop `v₃ + v₁ - 2v₂ ≤ τλ/2` reads `sd · cA ≤ Λ · cB`), `cE = 2^E`. The output
  `(Y, G)`: `y = Y/2^E`, `g = G/2^{eu+1}`. The value `v₀` at `y` that `sep` asks only to fail is not asked: the
  evaluators here never fail.

**The mathematics** (`Prop`s):

* `TestCert T Q a₀ η`: an accept puts the point in `Q`, a reject puts its gauge about `a₀` above `1 - η`.
* `CmCert`: UNI-CM certifies the body `K` about `a` with `η = 3·2^{-k}/r₀` (an accept also puts the point in the
  interior of `K`: `uni_cm_weakMem`).
* `GaugeAcc`: `γ ≤ gaugeQ ≤ γ/(1 - η) + H/2^j` when `γ ≤ H` (UNI-GAUGE (b); with `H = 2‖y‖₁` certified by a cross
  check in a position with `B(0, 1)` inside, `H/2^j ≤ 2√d R 2^{-j} π(y)`, the factor `2√d` of m4).
  `GaugeCertEnd`: every upper end below `H` was accepted (UNI-GAUGE (a)).
* `SepAcc`: Lemma SEP on the grid: an evaluator within `η_min = (τ ℓ₁/1600) 2^{-3d(J+1)}` at the grid points within
  `2ℓ₁` of `y⁰` of a convex `L`-Lipschitz `h` gives `(Y, G)` with `|y - y⁰| ≤ (64/63) ℓ₁` and
  `h(z) ≥ h(y) + ⟨g, z - y⟩ - τ |z - y|₁` for every `z`, at `J = ⌈log₂(8L/τ)⌉ = eL + eτ + 3`.
* `SepZero`: (SEP0) of UNI-SEP, the cut moved back to the base point, and `|g| ≤ L + τ√d`.

**The blocks on the oracle machine** (`Prop`s on a code builder, so that a consumer proves its block against the
contract before the code is written):

* `TestOK`: a test block writes `T (N/D)` (`1` or `0`) into a natural, for the point `(D; N)` of an array.
* `EvalOK`: an evaluator block writes `evN X` into a scalar, for the grid point `(2^E; X)` of an array.
* `CMBlockOK cmc`: the code `cmc` is a test block for `cmQ`, from the data `a`, `r₀`, `k` in its cells (`CMDat`).
* `GaugeBlockOK gc`: for every test block `TB` (`TestOK`), `gc TB` writes the counter `u` of `gaugeIt` into a scalar.
* `SepBlockOK sepc`: for every evaluator block `EV` (`EvalOK` on `SepDom`), `sepc EV` writes `sepZ`'s output, or a
  failure flag, within `sepK d J Kev` units.

Every block keeps the draws, writes only its frame (`FrameA`), and takes a data predicate (`Dat`) of its parameter
block that its own writes keep; the cells of a block and of its parameter block are disjoint (`SepDisj`,
`GaugeDisj`). Magnitudes: every value the block computes is below `2^ℓ` when the inputs are below the stated bit
bounds; the bounds are crude and polynomial.
-/

namespace AdversarialBco.Uni

open AdversarialBco AdversarialBco.Poly AdversarialBco.Poly.Mach AdversarialBco.Bit.Transfer

variable {d : ℕ}

/-! ## Points -/

/-- The rational point with denominator `D` and numerators `N`. -/
def ptDN (D : ℤ) (N : Fin d → ℤ) : Fin d → ℚ := fun i => (N i : ℚ) / D

/-- A rational point as a real vector. -/
def qR (y : Fin d → ℚ) : Fin d → ℝ := fun i => (y i : ℝ)

/-- The point `X / 2^E` of the grid as a real vector. -/
noncomputable def gridR (E : ℕ) (X : Fin d → ℤ) : Fin d → ℝ := fun i => (X i : ℝ) / 2 ^ E

/-- The unit vector `e_i` with integer entries. -/
def eZ (i : Fin d) : Fin d → ℤ := Pi.single i 1

/-! ## UNI-CM -/

/-- UNI-CM, the point asked: `a + (1 + 2·2^{-k}/r₀)(y - a)`. -/
def cmPt (a : Fin d → ℚ) (r0 : ℚ) (k : ℕ) (y : Fin d → ℚ) : Fin d → ℚ :=
  fun i => a i + (1 + 2 * (1 / 2 : ℚ) ^ k / r0) * (y i - a i)

/-- UNI-CM, the certified membership test: one query at `cmPt a r₀ k y` with the precision `k`. -/
def cmQ (orc : (Fin d → ℚ) → ℕ → Bool) (a : Fin d → ℚ) (r0 : ℚ) (k : ℕ) (y : Fin d → ℚ) : Bool :=
  orc (cmPt a r0 k y) k

/-! ## UNI-GAUGE -/

/-- The ray point of the counter `m`: `a₀ + (2^j/(H m))(x - a₀)`, the point `a₀ + (x - a₀)/t` at `t = H m/2^j`. -/
def gaugePt (a0 x : Fin d → ℚ) (H : ℚ) (j m : ℕ) : Fin d → ℚ :=
  fun i => a0 i + (2 : ℚ) ^ j / (H * m) * (x i - a0 i)

/-- The bisection of the gauge in counters: from `(0, 2^j)`, the midpoint `m` replaces the upper end when `T` accepts
the ray point of `m`, the lower end otherwise. -/
def gaugeIt (T : (Fin d → ℚ) → Bool) (a0 x : Fin d → ℚ) (H : ℚ) (j : ℕ) : ℕ → ℕ × ℕ
  | 0 => (0, 2 ^ j)
  | k + 1 =>
    let I := gaugeIt T a0 x H j k
    if T (gaugePt a0 x H j ((I.1 + I.2) / 2)) then (I.1, (I.1 + I.2) / 2) else ((I.1 + I.2) / 2, I.2)

/-- UNI-GAUGE: the value of the gauge of `x` about `a₀` after `j` steps, the upper end `H u/2^j`. -/
def gaugeQ (T : (Fin d → ℚ) → Bool) (a0 x : Fin d → ℚ) (H : ℚ) (j : ℕ) : ℚ :=
  H * (gaugeIt T a0 x H j j).2 / 2 ^ j

/-! ## UNI-SEP: LINE and SEP on the grid -/

/-- A window of LINE: the start `p0` and the spacing `lam` as numerators at the scale `2^E`, and the numerators of the
five values at `p0 + k lam`. -/
structure WinZ where
  p0 : ℤ
  lam : ℤ
  v0 : ℤ
  v1 : ℤ
  v2 : ℤ
  v3 : ℤ
  v4 : ℤ

/-- The measured second difference at the middle point, `v₃ + v₁ - 2 v₂`. -/
def WinZ.sd (W : WinZ) : ℤ := W.v3 + W.v1 - 2 * W.v2

/-- The measured spread times the spacing, `(v₄ - v₃) - (v₁ - v₀)`. -/
def WinZ.sp (W : WinZ) : ℤ := (W.v4 - W.v3) - (W.v1 - W.v0)

/-- The first window: `p0 = 0`, `lam = len/4`. -/
def lineFirstZ (f : ℤ → ℤ) (len : ℤ) : WinZ :=
  ⟨0, len / 4, f 0, f (len / 4), f (2 * (len / 4)), f (3 * (len / 4)), f (4 * (len / 4))⟩

/-- One halving: the window of five points from `p₁ = p0 + lam` or from `p₂ = p0 + 2 lam` with the spacing `lam/4`,
whichever has the smaller measured spread (the first on a tie). -/
def lineHalveZ (f : ℤ → ℤ) (W : WinZ) : WinZ :=
  let l := W.lam / 4
  let p1 := W.p0 + W.lam
  let p2 := W.p0 + 2 * W.lam
  let A : WinZ := ⟨p1, l, W.v1, f (p1 + l), f (p1 + 2 * l), f (p1 + 3 * l), W.v2⟩
  let B : WinZ := ⟨p2, l, W.v2, f (p2 + l), f (p2 + 2 * l), f (p2 + 3 * l), W.v3⟩
  if B.sp < A.sp then B else A

/-- The loop of LINE with at most `j` more halvings: stop at a window with `sd · cA ≤ lam · cB`, returning
`(p0 + 2 lam, lam)`; fail when no halving is left. -/
def lineLoopZ (f : ℤ → ℤ) (cA cB : ℤ) : ℕ → WinZ → Option (ℤ × ℤ)
  | j, W =>
    if W.sd * cA ≤ W.lam * cB then some (W.p0 + 2 * W.lam, W.lam)
    else match j with
      | 0 => none
      | j + 1 => lineLoopZ f cA cB j (lineHalveZ f W)

/-- Procedure LINE on `[0, len]` with at most `J` halvings: `(s, δ)` as numerators at the scale `2^E`. -/
def lineZ (f : ℤ → ℤ) (len cA cB : ℤ) (J : ℕ) : Option (ℤ × ℤ) :=
  lineLoopZ f cA cB J (lineFirstZ f len)

/-- The state of SEP: the point `Y`, the next length, the scales `Δ`. -/
abbrev SepStZ (d : ℕ) := (Fin d → ℤ) × ℤ × (Fin d → ℤ)

/-- The search along coordinate `i`: LINE on `s ↦ evN (Y + s e_i)`; then `Y + s e_i`, the next length `δ/sh`, and
`Δ_i = δ`. -/
def sepCoordZ (evN : (Fin d → ℤ) → ℤ) (sh cA cB : ℤ) (J : ℕ) (i : Fin d) (st : SepStZ d) : Option (SepStZ d) := do
  let r ← lineZ (fun s => evN (st.1 + s • eZ i)) st.2.1 cA cB J
  pure (st.1 + r.1 • eZ i, r.2 / sh, Function.update st.2.2 i r.2)

/-- The searches along the coordinates `0, ..., k - 1` from `Y₀` with the first length `len₁`. -/
def sepCoordsZ (evN : (Fin d → ℤ) → ℤ) (Y0 : Fin d → ℤ) (len1 sh cA cB : ℤ) (J : ℕ) : ℕ → Option (SepStZ d)
  | 0 => some (Y0, len1, 0)
  | k + 1 => sepCoordsZ evN Y0 len1 sh cA cB J k >>= fun st =>
      if h : k < d then sepCoordZ evN sh cA cB J ⟨k, h⟩ st else some st

/-- Procedure SEP on the grid: the point `Y` and `G`, `G_i = (evN (Y + Δ_i e_i) - evN (Y - Δ_i e_i)) (cE/Δ_i)`;
`y = Y/2^E`, `g = G/2^{eu+1}`. -/
def sepZ (evN : (Fin d → ℤ) → ℤ) (Y0 : Fin d → ℤ) (len1 sh cA cB cE : ℤ) (J : ℕ) :
    Option ((Fin d → ℤ) × (Fin d → ℤ)) := do
  let st ← sepCoordsZ evN Y0 len1 sh cA cB J d
  pure (st.1, fun i => (evN (st.1 + st.2.2 i • eZ i) - evN (st.1 - st.2.2 i • eZ i)) * (cE / st.2.2 i))

/-- `sepZ` at the exponents: `len₁ = 2^{E-e₁}`, `sh = 2^{eτ+4+eL}`, `cA = 2^{E+eτ+1}`, `cB = 2^{eu}`, `cE = 2^E`,
`J = eL + eτ + 3`. -/
def sepE (evN : (Fin d → ℤ) → ℤ) (Y0 : Fin d → ℤ) (E e1 eτ eL eu : ℕ) : Option ((Fin d → ℤ) × (Fin d → ℤ)) :=
  sepZ evN Y0 (2 ^ (E - e1)) (2 ^ (eτ + 4 + eL)) (2 ^ (E + eτ + 1)) (2 ^ eu) (2 ^ E) (eL + eτ + 3)

/-! ## The mathematics -/

/-- A test certifies the body `Q` about `a₀` with the band `η`: an accept puts the point in `Q`, a reject puts its
gauge about `a₀` above `1 - η`. -/
def TestCert (T : (Fin d → ℚ) → Bool) (Q : Set (Fin d → ℝ)) (a0 : Fin d → ℝ) (η : ℝ) : Prop :=
  ∀ y : Fin d → ℚ, (T y = true → qR y ∈ Q) ∧ (T y = false → 1 - η < oGauge Q a0 (qR y))

/-- UNI-CM certifies `K` about `a` with the band `3·2^{-k}/r₀`, for every weak membership oracle of a convex `K` with
`B̄(a, r₀) ⊆ K`, at every precision `k`. -/
def CmCert : Prop :=
  ∀ (d : ℕ) (K : Set (E d)) (a : Fin d → ℚ) (r0 : ℚ) (k : ℕ) (orc : (Fin d → ℚ) → ℕ → Bool),
    Convex ℝ K → 0 < r0 → Metric.closedBall (BitRAM.toE a) (r0 : ℝ) ⊆ K → BitRAMO.WeakMemOracle K orc →
    TestCert (cmQ orc a r0 k) {x | WithLp.toLp 2 x ∈ K} (qR a) (3 * (2 : ℝ)⁻¹ ^ k / r0)

/-- UNI-GAUGE (b): for a test certifying `Q` about `a₀` with a band `η < 1` and `H > 0` at least the gauge of `x`,
`γ(x) ≤ gaugeQ ≤ γ(x)/(1 - η) + H/2^j`. -/
def GaugeAcc : Prop :=
  ∀ (d : ℕ) (T : (Fin d → ℚ) → Bool) (Q : Set (Fin d → ℝ)) (a0 x : Fin d → ℚ) (H : ℚ) (j : ℕ) (η : ℝ),
    0 ≤ η → η < 1 → TestCert T Q (qR a0) η → 0 < H → oGauge Q (qR a0) (qR x) ≤ H →
    oGauge Q (qR a0) (qR x) ≤ gaugeQ T a0 x H j ∧
      (gaugeQ T a0 x H j : ℝ) ≤ oGauge Q (qR a0) (qR x) / (1 - η) + H / 2 ^ j

/-- UNI-GAUGE (a): an upper end below `2^j` was accepted, so the ray point of the value is certified. -/
def GaugeCertEnd : Prop :=
  ∀ (d : ℕ) (T : (Fin d → ℚ) → Bool) (a0 x : Fin d → ℚ) (H : ℚ) (j : ℕ),
    (gaugeIt T a0 x H j j).2 < 2 ^ j → T (gaugePt a0 x H j (gaugeIt T a0 x H j j).2) = true

/-- UNI-SEP: Lemma SEP on the grid. `h` convex and `2^{eL}`-Lipschitz, the evaluator within
`η_min = (τ ℓ₁/1600) 2^{-3d(J+1)}` of `h` at the grid points within `2ℓ₁` of `y⁰ = Y₀/2^E` (`τ = 2^{-eτ}`,
`ℓ₁ = 2^{-e₁}`, `J + 1 = eL + eτ + 4`), and the grid fine enough: SEP returns `(Y, G)` with `|y - y⁰| ≤ (64/63) ℓ₁`
and `h(z) ≥ h(y) + ⟨g, z - y⟩ - τ |z - y|₁` for every `z`, `y = Y/2^E`, `g = G/2^{eu+1}`. -/
def SepAcc : Prop :=
  ∀ (d : ℕ) (h : (Fin d → ℝ) → ℝ) (evN : (Fin d → ℤ) → ℤ) (Y0 : Fin d → ℤ) (E e1 eτ eL eu : ℕ),
    1 ≤ d → ConvexOn ℝ Set.univ h → (∀ x y, |h x - h y| ≤ 2 ^ eL * oNorm (x - y)) →
    e1 + d * (2 * (eL + eτ + 3) + 6 + eτ + eL) ≤ E →
    (∀ X, oNorm (gridR E X - gridR E Y0) ≤ 2 * (2 : ℝ)⁻¹ ^ e1 →
      |(evN X : ℝ) / 2 ^ eu - h (gridR E X)| ≤
        (2 : ℝ)⁻¹ ^ eτ * (2 : ℝ)⁻¹ ^ e1 / 1600 * (2 : ℝ)⁻¹ ^ (3 * d * (eL + eτ + 4))) →
    ∃ Y G, sepE evN Y0 E e1 eτ eL eu = some (Y, G) ∧
      oNorm (gridR E Y - gridR E Y0) ≤ 64 / 63 * (2 : ℝ)⁻¹ ^ e1 ∧
      ∀ z, h (gridR E Y) + (fun i => (G i : ℝ) / 2 ^ (eu + 1)) ⬝ᵥ (z - gridR E Y) -
        (2 : ℝ)⁻¹ ^ eτ * ∑ i, |z i - gridR E Y i| ≤ h z

/-- (SEP0) of UNI-SEP: a `τ`-subgradient `g` at a point `y` within `ρ` of `y⁰`, of an
`L`-Lipschitz `h`, `L ≥ 0`, is a cut at `y⁰` up to `τ√d |z - y⁰| + (2L + 2τ√d) ρ`, and `|g| ≤ L + τ√d` (at `d = 0`
every `L` is a Lipschitz constant, and a negative one would make the claim false). -/
def SepZero : Prop :=
  ∀ (d : ℕ) (h : (Fin d → ℝ) → ℝ) (L τ ρ : ℝ) (y0 y g : Fin d → ℝ),
    (∀ x y, |h x - h y| ≤ L * oNorm (x - y)) → 0 ≤ L → 0 ≤ τ → oNorm (y - y0) ≤ ρ →
    (∀ z, h y + g ⬝ᵥ (z - y) - τ * ∑ i, |z i - y i| ≤ h z) →
    oNorm g ≤ L + τ * Real.sqrt d ∧
      ∀ z, h y0 + g ⬝ᵥ (z - y0) - τ * Real.sqrt d * oNorm (z - y0) - (2 * L + 2 * τ * Real.sqrt d) * ρ ≤ h z

/-! ## Contracts of the blocks -/

/-- A test block: from every environment satisfying `Dat` whose array `ap` holds a point `(D; N)` (entry `0` the
denominator `D > 0`, entries `1, ..., d` the numerators, all below `2^bt`), `TB` writes `1` into the natural `nt` if
`T (N/D)` holds and `0` otherwise, within `K` units, writes only the frame `S`, `N`, `Ar`, and keeps the draws. -/
def TestOK (L : Layout) (XO : XCtxO d) (ℓa ℓ : ℕ) (TB : XCmdO) (Dat : Env d → Prop) (ap nt bt : ℕ)
    (T : (Fin d → ℚ) → Bool) (K : ℕ) (S N : ℕ → Prop) (Ar : ℕ → ℕ → Prop) : Prop :=
  ∀ (σ : Env d) (D : ℤ) (Nv : Fin d → ℤ), Dat σ → 0 < D → D < 2 ^ bt → (∀ i, |Nv i| < 2 ^ bt) →
    σ.arr ap 0 = D → (∀ i : Fin d, σ.arr ap (1 + (i : ℕ)) = Nv i) →
    XRunsBO L XO ℓa ℓ TB σ K (fun σ' => σ'.nat nt = (if T (ptDN D Nv) then 1 else 0) ∧ FrameA S N Ar σ σ' ∧
      σ'.draws = σ.draws)

/-- An evaluator block: from every environment satisfying `Dat` whose array `aev` holds a grid point `(2^E; X)` of the
domain `Dom`, `EV` writes `evN X` into the scalar `vout`, within `K` units, writes only the frame `S`, `N`, `Ar`, and
keeps the draws. -/
def EvalOK (L : Layout) (XO : XCtxO d) (ℓa ℓ : ℕ) (EV : XCmdO) (Dat : Env d → Prop) (aev vout E : ℕ)
    (Dom : (Fin d → ℤ) → Prop) (evN : (Fin d → ℤ) → ℤ) (K : ℕ) (S N : ℕ → Prop) (Ar : ℕ → ℕ → Prop) : Prop :=
  ∀ (σ : Env d) (X : Fin d → ℤ), Dat σ → Dom X → σ.arr aev 0 = 2 ^ E → (∀ i : Fin d, σ.arr aev (1 + (i : ℕ)) = X i) →
    XRunsBO L XO ℓa ℓ EV σ K (fun σ' => σ'.sc vout = evN X ∧ FrameA S N Ar σ σ' ∧ σ'.draws = σ.draws)

/-- A predicate on environments kept by every change within the frame `S`, `N`, `Ar` that keeps the draws. -/
def Stable (Dat : Env d → Prop) (S N : ℕ → Prop) (Ar : ℕ → ℕ → Prop) : Prop :=
  ∀ σ σ' : Env d, Dat σ → FrameA S N Ar σ σ' → σ'.draws = σ.draws → Dat σ'

/-! ### UNI-CM -/

/-- The cells of the CM block: the centre `a` in array `aa` as `(Da; Na)`, `r₀ = sc cr0n/sc cr0d`, the precision `k` in
the natural `nk` and `2^k` in the scalar `c2k`; the point tested in array `ap`, the answer in the natural `nt`; the
query point in array `aq`; scratch scalars `u, ..., u + 15` and naturals `n0, ..., n0 + 3`. -/
structure CMLay where
  aa : ℕ
  cr0n : ℕ
  cr0d : ℕ
  nk : ℕ
  c2k : ℕ
  ap : ℕ
  nt : ℕ
  aq : ℕ
  u : ℕ
  n0 : ℕ

/-- The layout of the CM block fits `L`, its cells are distinct and its arrays hold a point. -/
structure CMLay.OK (L : Layout) (c : CMLay) : Prop where
  arrs : c.aa < L.NA ∧ c.ap < L.NA ∧ c.aq < L.NA
  arrs_ne : c.aq ≠ c.aa ∧ c.aq ≠ c.ap
  scs : c.cr0n < L.NS ∧ c.cr0d < L.NS ∧ c.c2k < L.NS ∧ c.u + 16 ≤ L.NS
  scs_ne : c.cr0n < c.u ∧ c.cr0d < c.u ∧ c.c2k < c.u
  nats : c.nk < L.NN ∧ c.nt < L.NN ∧ c.n0 + 4 ≤ L.NN
  nats_ne : c.nk ≠ c.nt ∧ c.nk < c.n0 ∧ c.nt < c.n0

/-- The data of the CM block. -/
def CMDat (c : CMLay) (Da : ℤ) (Na : Fin d → ℤ) (rn rd : ℤ) (k : ℕ) (σ : Env d) : Prop :=
  σ.arr c.aa 0 = Da ∧ (∀ i : Fin d, σ.arr c.aa (1 + (i : ℕ)) = Na i) ∧ σ.sc c.cr0n = rn ∧ σ.sc c.cr0d = rd ∧
    σ.nat c.nk = k ∧ σ.sc c.c2k = 2 ^ k

/-- The scalars the CM block writes. -/
def cmS (c : CMLay) (y : ℕ) : Prop := c.u ≤ y ∧ y < c.u + 16

/-- The naturals the CM block writes. -/
def cmN (c : CMLay) (j : ℕ) : Prop := j = c.nt ∨ (c.n0 ≤ j ∧ j < c.n0 + 4)

/-- The array cells the CM block writes. -/
def cmAr (c : CMLay) (b _k : ℕ) : Prop := b = c.aq

/-- The units of the CM block. -/
def cmK (d : ℕ) : ℕ := 32 * d + 64

/-! ### UNI-GAUGE -/

/-- The cells of the gauge block: the point `x` in array `ax` as `(D; N)`, the centre `a₀` in array `aa` as `(Da; Na)`,
`H = sc cHn/sc cHd`, `j` in the natural `nj` and `2^j` in the scalar `c2j`; the test point in array `atp`, the test's
answer in the natural `nt`; the counter `u` of the value into the scalar `gout`; scratch scalars `u, ..., u + 15` and
naturals `n0, ..., n0 + 3`. -/
structure GaugeLay where
  ax : ℕ
  aa : ℕ
  cHn : ℕ
  cHd : ℕ
  nj : ℕ
  c2j : ℕ
  atp : ℕ
  nt : ℕ
  gout : ℕ
  u : ℕ
  n0 : ℕ

/-- The layout of the gauge block fits `L`, its cells are distinct and its arrays hold a point. -/
structure GaugeLay.OK (L : Layout) (g : GaugeLay) : Prop where
  arrs : g.ax < L.NA ∧ g.aa < L.NA ∧ g.atp < L.NA
  arrs_ne : g.atp ≠ g.ax ∧ g.atp ≠ g.aa
  scs : g.cHn < L.NS ∧ g.cHd < L.NS ∧ g.c2j < L.NS ∧ g.gout < L.NS ∧ g.u + 16 ≤ L.NS
  scs_ne : g.cHn < g.u ∧ g.cHd < g.u ∧ g.c2j < g.u ∧ g.gout < g.u ∧ g.gout ≠ g.cHn ∧ g.gout ≠ g.cHd ∧
    g.gout ≠ g.c2j
  nats : g.nj < L.NN ∧ g.nt < L.NN ∧ g.n0 + 4 ≤ L.NN
  nats_ne : g.nj ≠ g.nt ∧ g.nj < g.n0 ∧ g.nt < g.n0

/-- The scalars the gauge block writes. -/
def gaugeS (g : GaugeLay) (y : ℕ) : Prop := y = g.gout ∨ (g.u ≤ y ∧ y < g.u + 16)

/-- The naturals the gauge block writes (the test's answer included). -/
def gaugeN (g : GaugeLay) (j : ℕ) : Prop := j = g.nt ∨ (g.n0 ≤ j ∧ j < g.n0 + 4)

/-- The array cells the gauge block writes. -/
def gaugeAr (g : GaugeLay) (b _k : ℕ) : Prop := b = g.atp

/-- The cells of the gauge block that its test block must not write: its data and its state. -/
def GaugeDisj (g : GaugeLay) (S N : ℕ → Prop) (Ar : ℕ → ℕ → Prop) : Prop :=
  (∀ y, S y → y ≠ g.cHn ∧ y ≠ g.cHd ∧ y ≠ g.c2j ∧ y ≠ g.gout ∧ ¬ (g.u ≤ y ∧ y < g.u + 16)) ∧
    (∀ j, N j → j ≠ g.nj ∧ ¬ (g.n0 ≤ j ∧ j < g.n0 + 4)) ∧
    (∀ b k, Ar b k → b ≠ g.ax ∧ b ≠ g.aa ∧ b ≠ g.atp)

/-- The units of the gauge block with a test block of `Kt` units. -/
def gaugeK (d j Kt : ℕ) : ℕ := 2 * (j + 1) * (Kt + 32 * d + 64)

/-- The contract of the gauge block `gc`: for every test block `TB` for `T` (answer in `nt`, point in `atp`, points
below `2^bt`) whose data `TDat` the writes of the gauge and of `TB` keep and whose frame avoids the gauge's cells,
`gc TB` writes the upper counter of `gaugeIt T a₀ x H j` after `j` steps into `gout`, for `x = N/D`, `a₀ = Na/Da`,
`H = Hn/Hd`, all below `2^b`, when `3b + j + 2 ≤ bt` and `bt + 4 ≤ ℓ`. -/
def GaugeBlockOK (L : Layout) (XO : XCtxO d) (ℓa ℓ : ℕ) (g : GaugeLay) (gc : XCmdO → XCmdO) : Prop :=
  ∀ (TB : XCmdO) (TDat : Env d → Prop) (T : (Fin d → ℚ) → Bool) (Kt bt : ℕ) (St Nt : ℕ → Prop)
    (Art : ℕ → ℕ → Prop) (σ : Env d) (D : ℤ) (N : Fin d → ℤ) (Da : ℤ) (Na : Fin d → ℤ) (Hn Hd : ℤ) (j b : ℕ),
    LayOK L d ℓa → GaugeLay.OK L g → 1 ≤ d →
    TestOK L XO ℓa ℓ TB TDat g.atp g.nt bt T Kt St Nt Art → GaugeDisj g St Nt Art →
    Stable TDat (fun y => gaugeS g y ∨ St y) (fun j => gaugeN g j ∨ Nt j) (fun b k => gaugeAr g b k ∨ Art b k) →
    TDat σ →
    σ.arr g.ax 0 = D → (∀ i : Fin d, σ.arr g.ax (1 + (i : ℕ)) = N i) →
    σ.arr g.aa 0 = Da → (∀ i : Fin d, σ.arr g.aa (1 + (i : ℕ)) = Na i) →
    σ.sc g.cHn = Hn → σ.sc g.cHd = Hd → σ.nat g.nj = j → σ.sc g.c2j = 2 ^ j →
    0 < D → 0 < Da → 0 < Hn → 0 < Hd → D < 2 ^ b → (∀ i, |N i| < 2 ^ b) → Da < 2 ^ b → (∀ i, |Na i| < 2 ^ b) →
    Hn < 2 ^ b → Hd < 2 ^ b → 3 * b + j + 2 ≤ bt → bt + 4 ≤ ℓ → j + 1 < 2 ^ ℓa →
    XRunsBO L XO ℓa ℓ (gc TB) σ (gaugeK d j Kt) (fun σ' =>
      σ'.sc g.gout = ((gaugeIt T (ptDN Da Na) (ptDN D N) ((Hn : ℚ) / Hd) j j).2 : ℝ) ∧
        FrameA (fun y => gaugeS g y ∨ St y) (fun j => gaugeN g j ∨ Nt j) (fun b k => gaugeAr g b k ∨ Art b k) σ σ' ∧
        σ'.draws = σ.draws)

/-! ### UNI-SEP -/

/-- The cells of the SEP block: the base point `Y₀` in array `ay0` (entries `0, ..., d - 1`), the outputs `Y`, `G` in
arrays `ay`, `ag`, the scales `Δ` in array `adl`; the evaluator's point in array `aev` as `(2^E; X)` and its value in the
scalar `vout`; the constants `2^E`, `2^{E-e₁}`, `2^{eτ+4+eL}`, `2^{E+eτ+1}`, `2^{eu}` in the scalars `cE`, `cL1`, `cSh`,
`cA`, `cB`; `J` in the natural `nJ`; the flag (`1` success, `0` failure) in the natural `nok`; scratch scalars
`u, ..., u + 47` and naturals `n0, ..., n0 + 15`. -/
structure SepLay where
  ay0 : ℕ
  ay : ℕ
  ag : ℕ
  adl : ℕ
  aev : ℕ
  vout : ℕ
  cE : ℕ
  cL1 : ℕ
  cSh : ℕ
  cA : ℕ
  cB : ℕ
  nJ : ℕ
  nok : ℕ
  u : ℕ
  n0 : ℕ

/-- The layout of the SEP block fits `L` and its cells are distinct. -/
structure SepLay.OK (L : Layout) (s : SepLay) : Prop where
  arrs : s.ay0 < L.NA ∧ s.ay < L.NA ∧ s.ag < L.NA ∧ s.adl < L.NA ∧ s.aev < L.NA
  arrs_ne : [s.ay0, s.ay, s.ag, s.adl, s.aev].Nodup
  scs : s.vout < L.NS ∧ s.cE < L.NS ∧ s.cL1 < L.NS ∧ s.cSh < L.NS ∧ s.cA < L.NS ∧ s.cB < L.NS ∧ s.u + 48 ≤ L.NS
  scs_ne : [s.vout, s.cE, s.cL1, s.cSh, s.cA, s.cB].Nodup ∧ s.vout < s.u ∧ s.cE < s.u ∧ s.cL1 < s.u ∧
    s.cSh < s.u ∧ s.cA < s.u ∧ s.cB < s.u
  nats : s.nJ < L.NN ∧ s.nok < L.NN ∧ s.n0 + 16 ≤ L.NN
  nats_ne : s.nJ ≠ s.nok ∧ s.nJ < s.n0 ∧ s.nok < s.n0

/-- The scalars the SEP block writes itself. -/
def sepS (s : SepLay) (y : ℕ) : Prop := y = s.vout ∨ (s.u ≤ y ∧ y < s.u + 48)

/-- The naturals the SEP block writes itself. -/
def sepN (s : SepLay) (j : ℕ) : Prop := j = s.nok ∨ (s.n0 ≤ j ∧ j < s.n0 + 16)

/-- The array cells the SEP block writes itself. -/
def sepAr (s : SepLay) (b _k : ℕ) : Prop := b = s.ay ∨ b = s.ag ∨ b = s.adl ∨ b = s.aev

/-- The cells of the SEP block that its evaluator must not write: its data and its state (the evaluator may write its
own value `vout`). -/
def SepDisj (s : SepLay) (S N : ℕ → Prop) (Ar : ℕ → ℕ → Prop) : Prop :=
  (∀ y, S y → y ≠ s.cE ∧ y ≠ s.cL1 ∧ y ≠ s.cSh ∧ y ≠ s.cA ∧ y ≠ s.cB ∧ ¬ (s.u ≤ y ∧ y < s.u + 48)) ∧
    (∀ j, N j → j ≠ s.nJ ∧ j ≠ s.nok ∧ ¬ (s.n0 ≤ j ∧ j < s.n0 + 16)) ∧
    (∀ b k, Ar b k → b ≠ s.ay0 ∧ b ≠ s.ay ∧ b ≠ s.ag ∧ b ≠ s.adl ∧ b ≠ s.aev)

/-- The grid points where SEP asks values: every coordinate within `2 · 2^{E-e₁}` of `Y₀` (the searches move coordinate
`i` by at most `ℓ_i ≤ ℓ₁`, the final values by `δ_i ≤ ℓ_i/4` more). -/
def SepDom (Y0 : Fin d → ℤ) (E e1 : ℕ) (X : Fin d → ℤ) : Prop := ∀ i, |X i - Y0 i| ≤ 2 * 2 ^ (E - e1)

/-- The output of the SEP block: on success the flag `1` and `Y`, `G` in their arrays, on failure the flag `0`. -/
def SepOut (s : SepLay) (r : Option ((Fin d → ℤ) × (Fin d → ℤ))) (σ' : Env d) : Prop :=
  match r with
  | some (Y, G) => σ'.nat s.nok = 1 ∧ ∀ i : Fin d, σ'.arr s.ay i = Y i ∧ σ'.arr s.ag i = G i
  | none => σ'.nat s.nok = 0

/-- The units of the SEP block with an evaluator of `Kev` units: at most `d (6J + 5) + 2d` values, each with the
point written in `O(d)` units. -/
def sepK (d J Kev : ℕ) : ℕ := 16 * (d + 1) * (J + 1) * (Kev + 64 * d + 256)

/-- The contract of the SEP block `sepc`: for every evaluator block `EV` (point in `aev`, value in `vout`) on the
domain `SepDom` with values below `2^bv`, whose data `Dat` the writes of SEP and of `EV` keep and whose frame avoids
SEP's cells, `sepc EV` writes the output of `sepE evN Y₀ E e₁ eτ eL eu` (or the failure flag) within `sepK d J Kev`
units, for `J = eL + eτ + 3`, the grid fine enough, `Y₀` below `2^bY` and `E + eτ + eu + bY + bv + 8 ≤ ℓ`. -/
def SepBlockOK (L : Layout) (XO : XCtxO d) (ℓa ℓ : ℕ) (s : SepLay) (sepc : XCmdO → XCmdO) : Prop :=
  ∀ (EV : XCmdO) (Dat : Env d → Prop) (evN : (Fin d → ℤ) → ℤ) (Kev bv : ℕ) (Sev Nev : ℕ → Prop)
    (Arev : ℕ → ℕ → Prop) (σ : Env d) (Y0 : Fin d → ℤ) (E e1 eτ eL eu bY : ℕ),
    LayOK L d ℓa → SepLay.OK L s → 1 ≤ d →
    EvalOK L XO ℓa ℓ EV Dat s.aev s.vout E (SepDom Y0 E e1) evN Kev Sev Nev Arev →
    (∀ X, SepDom Y0 E e1 X → |evN X| < 2 ^ bv) → SepDisj s Sev Nev Arev →
    Stable Dat (fun y => sepS s y ∨ Sev y) (fun j => sepN s j ∨ Nev j) (fun b k => sepAr s b k ∨ Arev b k) →
    Dat σ →
    (∀ i : Fin d, σ.arr s.ay0 i = Y0 i) → (∀ i, |Y0 i| < 2 ^ bY) →
    σ.sc s.cE = 2 ^ E → σ.sc s.cL1 = 2 ^ (E - e1) → σ.sc s.cSh = 2 ^ (eτ + 4 + eL) →
    σ.sc s.cA = 2 ^ (E + eτ + 1) → σ.sc s.cB = 2 ^ eu → σ.nat s.nJ = eL + eτ + 3 →
    e1 + d * (2 * (eL + eτ + 3) + 6 + eτ + eL) ≤ E → E + eτ + eu + bY + bv + 8 ≤ ℓ → E + eτ + 8 < 2 ^ ℓa →
    XRunsBO L XO ℓa ℓ (sepc EV) σ (sepK d (eL + eτ + 3) Kev) (fun σ' =>
      SepOut s (sepE evN Y0 E e1 eτ eL eu) σ' ∧
        FrameA (fun y => sepS s y ∨ Sev y) (fun j => sepN s j ∨ Nev j) (fun b k => sepAr s b k ∨ Arev b k) σ σ' ∧
        σ'.draws = σ.draws)

end AdversarialBco.Uni
