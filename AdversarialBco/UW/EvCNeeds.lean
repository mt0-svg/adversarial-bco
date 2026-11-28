/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.UW.Defs

@[expose] public section

/-!
# The needs of the events (c), (d), (e) of Theorem UW

The arithmetic that the proofs of `EvLQPropUW`, `EvSDFPropUW` and `EvDQPropUW` read at the end, in the form they
read it. Each need is the bound of Lemma U at the levels of the event
(variance `V`, range `R`, the logarithm at a net of the ball and the failure `k δc`), plus the discretization of the
net and the bias of the weight and the clip (Lemma SK'), against the level of the event: `b₁` for (c), `B_n/(L λ²)`
for (e), `B_n` for (d). The levels are those of Theorem U's proofs (Poly/Df2EvSILQ.lean, Df2EvSIDQ.lean,
Df2EvSISDF.lean) with the sure ranges `y0`, `b0 + 1` in place of the bounds of event (a):

* `lvQ`: the bound of `|c - μ_s|²_{P_s}` for `c` within `δ⁴` of a point of `S_t` (`qL`);
* `lvWb`: the bound of `E[(e² + pip²)²]`; `lvX = log(1/δ_e)`;
* `lvBias`: Lemma SK' (ii) to (iv), the bias of one round is at most `lvBias (E_z D⁴)^{1/4}`, with
  `P(B | past) ≤ 4 δ_e⁹` and `E[Y⁴ | past] ≤ (13 √d (1 + 2/ε))⁴`;
* (c): `lvVc`, `lvRc`, `lvGc`, `lvBc` (variance, range with the bias, discretization, bias of a round);
* (e): `lvVe`, `lvRe`, `lvKe`, `lvBe`;
* (d): `lvXv`, `lvRd0` (range per unit of `vᵀ P_s v` without the bias), `lvBd` (bias per unit of `q`),
  `lvRd = lvRd0 + lvBd`.

`EvNeedsW d n ρ` holds the three needs at `parW d n ρ.u`; `EvNeedsUW` asks them on the regime.
-/

namespace AdversarialBco.UW

open AdversarialBco.Poly

/-! ## The levels -/

/-- `x = log(1/δ_e)`. -/
noncomputable def lvX (p : Df2OPar) : ℝ := Real.log (1 / p.δe)

/-- The bound of `|c - μ_s|²_{P_s}` for `c` within `δ_e⁴` of a point of `S_t`. -/
noncomputable def lvQ (p : Df2OPar) : ℝ := (1 + p.δe) / (2 * p.Le * p.lam ^ 2) + 2 * p.δe ^ 6

/-- The bound of the second moment of `e² + pip²` in one round. -/
noncomputable def lvWb (p : Df2OPar) (d : ℕ) : ℝ := 72 + 25600 * (p.R ^ 4 + 3 * (d : ℝ) ^ 2) / p.eps ^ 4

/-- Lemma SK': the bias of the weight and the clip in one round, per unit of `(E_z D⁴)^{1/4}`:
`2 (13 √d (1 + 2/ε)) (4 δ_e⁹)^{1/2}`. -/
noncomputable def lvBias (p : Df2OPar) (d : ℕ) : ℝ := 52 * Real.sqrt d * (1 + 2 / p.eps) * Real.sqrt (p.δe ^ 9)

/-! ### Event (c), LQ -/

/-- The variance level of (c) (Theorem U's `VL`). -/
noncomputable def lvVc (p : Df2OPar) (d n : ℕ) : ℝ :=
  p.k0 * (lvQ p * (8 * lvX p * (9 * n) +
    n * (Real.sqrt (lvWb p d) * Real.sqrt (Real.sqrt 105 * Real.exp (-(8 * lvX p) / 4)))))

/-- The bias of a round of (c): `lvBias (E_z D⁴)^{1/4}` with `(E_z D⁴)^{1/4} ≤ 2 κ₀^{1/2} q^{1/2}`. -/
noncomputable def lvBc (p : Df2OPar) (d : ℕ) : ℝ := lvBias p d * (2 * Real.sqrt p.k0 * Real.sqrt (lvQ p))

/-- The range level of (c): `|Y^w| ≤ y0`, `|ξ|² ≤ b0 + 1` where `Y^w ≠ 0`, `|⟨s'_s, c - μ_s⟩| ≤ (8/ε) 2R` and the
bias. -/
noncomputable def lvRc (p : Df2OPar) (d : ℕ) (b0 y0 : ℝ) : ℝ :=
  y0 * Real.sqrt p.k0 * Real.sqrt ((b0 + 1) * lvQ p) + 8 / p.eps * (2 * p.R) + lvBc p d

/-- The bound of `|ĝ_s - s'_s(μ_s)|` under the sure ranges. -/
noncomputable def lvGc (p : Df2OPar) (b0 y0 : ℝ) : ℝ :=
  y0 * Real.sqrt p.k0 * Real.sqrt ((b0 + 1) / p.δe) + 8 / p.eps

/-! ### Event (e), DQ -/

/-- The variance level of (e) (Theorem U's `VD`). -/
noncomputable def lvVe (p : Df2OPar) (d n : ℕ) : ℝ :=
  (p.lam * p.k0) ^ 2 * (lvQ p ^ 2 * ((16 * lvX p) ^ 2 * (9 * n) +
    n * (Real.sqrt (lvWb p d) * Real.sqrt (Real.sqrt 2027025 * Real.exp (-Real.sqrt ((16 * lvX p) ^ 2) / 4)))))

/-- The bias of a round of (e): `(E_z D⁴)^{1/4} ≤ 7 λ κ₀ q`. -/
noncomputable def lvBe (p : Df2OPar) (d : ℕ) : ℝ := lvBias p d * (7 * (p.lam * p.k0) * lvQ p)

/-- The range level of (e): `|Y^w| ≤ y0`, `|⟨P A ξ, h⟩² - hᵀ P h| ≤ (b0 + 2) hᵀ P h`, the Hessian of the surrogate,
and the bias. -/
noncomputable def lvRe (p : Df2OPar) (d : ℕ) (b0 y0 : ℝ) : ℝ :=
  y0 * (p.lam * p.k0) * ((b0 + 2) * lvQ p) +
    p.lam * (8 / p.eps) / (1 - p.lam) * Real.sqrt (2 * d * p.sig2) * lvQ p + lvBe p d

/-- The bound of `|vᵀ (ŝ''_s - s''_s(μ_s)) v|/|v|²` under the sure ranges. -/
noncomputable def lvKe (p : Df2OPar) (d : ℕ) (b0 y0 : ℝ) : ℝ :=
  p.lam * p.k0 * y0 * ((b0 + 2) / p.δe) + p.lam * (8 / p.eps) / (1 - p.lam) * Real.sqrt (d / p.δe)

/-! ### Event (d), S-DF -/

/-- The variance factor of (d) (Theorem U's `xvS`). -/
noncomputable def lvXv (p : Df2OPar) (d n : ℕ) : ℝ :=
  (16 * lvX p) ^ 2 * (9 * n) +
    n * (Real.sqrt (lvWb p d) * Real.sqrt (Real.sqrt 2027025 * Real.exp (-Real.sqrt ((16 * lvX p) ^ 2) / 4)))

/-- The range of a round of (d) per unit of `vᵀ P_s v`, without the bias (Theorem U's `rcS` under the sure ranges). -/
noncomputable def lvRd0 (p : Df2OPar) (d : ℕ) (b0 y0 : ℝ) : ℝ :=
  p.lam * p.k0 * y0 * (b0 + 2) + p.lam * (8 / p.eps) / (1 - p.lam) * Real.sqrt (2 * d * p.sig2)

/-- The bias of a round of (d) per unit of `q`: `(E_z D⁴)^{1/4} ≤ 7 λ κ₀ vᵀ P_s v`. -/
noncomputable def lvBd (p : Df2OPar) (d : ℕ) : ℝ := lvBias p d * (7 * (p.lam * p.k0))

/-- The range level of (d) per unit of `q`. -/
noncomputable def lvRd (p : Df2OPar) (d : ℕ) (b0 y0 : ℝ) : ℝ := lvRd0 p d b0 y0 + lvBd p d

/-! ## The needs -/

/-- The logarithm of Lemma U for (c) at a net of `Cc` points, with `κ = 1/R`, at the failure `δc/21`. -/
noncomputable def lvLogC (p : Df2OPar) (d n : ℕ) (b0 y0 δc Cc : ℝ) : ℝ :=
  Real.log (4 * (n * Cc) * max ((lvRc p d b0 y0)⁻¹ * lvRc p d b0 y0)
    ((lvRc p d b0 y0)⁻¹ * Real.sqrt (lvVc p d n)) / (δc / 21))

/-- The logarithm of Lemma U for (e) at a net of `Cc` points, with `κ = 1/R`, at the failure `δc/8`. -/
noncomputable def lvLogE (p : Df2OPar) (d n : ℕ) (b0 y0 δc Cc : ℝ) : ℝ :=
  Real.log (4 * (n * Cc) * max ((lvRe p d b0 y0)⁻¹ * lvRe p d b0 y0)
    ((lvRe p d b0 y0)⁻¹ * Real.sqrt (lvVe p d n)) / (δc / 8))

/-- The logarithm of Lemma U for (d) at a net of `Cc` points of the unit ball, the levels `V = (λ κ₀)² q² Xv` and
`R = lvRd q + δ_e²`, `κ = δ_e⁻²`, at the failure `δc/7`. -/
noncomputable def lvLogD (p : Df2OPar) (d n : ℕ) (b0 y0 δc Cc q : ℝ) : ℝ :=
  Real.log (4 * (n * Cc) * max ((p.δe ^ 2)⁻¹ * (lvRd p d b0 y0 * q + p.δe ^ 2))
    ((p.δe ^ 2)⁻¹ * Real.sqrt ((p.lam * p.k0) ^ 2 * q ^ 2 * lvXv p d n)) / (δc / 7))

/-- **The needs of the events (c), (d), (e)** at the table T4U `parW d n ρ.u`, the sure ranges `ρ.b0`, `ρ.y0` and the
level `ρ.δc`:

* `needC` (rows lq_c1, lq_c2, bias_c): Freedman's level of (c) plus the discretization and the bias is at most `b₁`;
* `needE` (rows dq_e1, dq_e2, bias_e): the same for (e) against `B_n/(L λ²)`;
* `needD` (Lemma L (L3), rows sdf_sum and the small terms): for every `q ∈ [0, 1/δ_e]` the logarithm of (d) is
  nonnegative, the sum form of (d) holds at it, and the discretization of the unit ball at `δ_e⁴` fits in
  `4 δ_e B_n`. -/
structure EvNeedsW (d n : ℕ) (ρ : RefW) : Prop where
  needC : ∀ Cc : ℝ, 1 ≤ Cc → Cc ≤ (1 + 2 * (parW d n ρ.u).R / (parW d n ρ.u).δe ^ 4) ^ d →
    3 * Real.sqrt (lvVc (parW d n ρ.u) d n * lvLogC (parW d n ρ.u) d n ρ.b0 ρ.y0 ρ.δc Cc) +
      2 * lvRc (parW d n ρ.u) d ρ.b0 ρ.y0 * lvLogC (parW d n ρ.u) d n ρ.b0 ρ.y0 ρ.δc Cc +
      n * lvGc (parW d n ρ.u) ρ.b0 ρ.y0 * (parW d n ρ.u).δe ^ 4 + n * lvBc (parW d n ρ.u) d ≤
    b1W (parW d n ρ.u) d n ρ.u
  needE : ∀ Cc : ℝ, 1 ≤ Cc → Cc ≤ (1 + 2 * (parW d n ρ.u).R / (parW d n ρ.u).δe ^ 4) ^ d →
    3 * Real.sqrt (lvVe (parW d n ρ.u) d n * lvLogE (parW d n ρ.u) d n ρ.b0 ρ.y0 ρ.δc Cc) +
      2 * lvRe (parW d n ρ.u) d ρ.b0 ρ.y0 * lvLogE (parW d n ρ.u) d n ρ.b0 ρ.y0 ρ.δc Cc +
      n * lvKe (parW d n ρ.u) d ρ.b0 ρ.y0 * ((parW d n ρ.u).δe ^ 4 * (4 * (parW d n ρ.u).R)) +
      n * lvBe (parW d n ρ.u) d ≤
    bnW (parW d n ρ.u) d n ρ.u / ((parW d n ρ.u).Le * (parW d n ρ.u).lam ^ 2)
  needD : ∀ Cc q : ℝ, 1 ≤ Cc → Cc ≤ (1 + 2 * 1 / (parW d n ρ.u).δe ^ 4) ^ d → 0 ≤ q →
    q * (parW d n ρ.u).δe ≤ 1 →
    0 ≤ lvLogD (parW d n ρ.u) d n ρ.b0 ρ.y0 ρ.δc Cc q ∧
    3 * ((parW d n ρ.u).lam * (parW d n ρ.u).k0) *
        Real.sqrt (lvXv (parW d n ρ.u) d n * lvLogD (parW d n ρ.u) d n ρ.b0 ρ.y0 ρ.δc Cc q) +
      2 * lvRd (parW d n ρ.u) d ρ.b0 ρ.y0 * lvLogD (parW d n ρ.u) d n ρ.b0 ρ.y0 ρ.δc Cc q +
      n * lvBd (parW d n ρ.u) d ≤ bnW (parW d n ρ.u) d n ρ.u ∧
    bnW (parW d n ρ.u) d n ρ.u * (2 * (parW d n ρ.u).δe ^ 3) +
      2 * (parW d n ρ.u).δe ^ 2 * lvLogD (parW d n ρ.u) d n ρ.b0 ρ.y0 ρ.δc Cc q +
      2 * n * lvRd0 (parW d n ρ.u) d ρ.b0 ρ.y0 * (parW d n ρ.u).δe ^ 3 ≤
    4 * (parW d n ρ.u).δe * bnW (parW d n ρ.u) d n ρ.u

/-- **The needs of the events (c), (d), (e) on the regime.** -/
def EvNeedsUW : Prop := ∀ (d n : ℕ) (ρ : RefW), RegimeW d n ρ → EvNeedsW d n ρ

end AdversarialBco.UW
