/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.UW.Defs
public import AdversarialBco.Unified.AsmMain
public import AdversarialBco.Poly.Df2EvSIU

@[expose] public section

/-!
# Theorem UW: the interfaces of its Lean proof

Each brick of the paper proof of Theorem UW as a named
`Prop`, stated on the objects of UW/Defs.lean and on the objects of Theorem U's proof that stay as they are. A brick
that generalises a Prop of Theorem U keeps its name with a `W` (weight, clip or scale `u`) or `UW` suffix. The
reduction `theoremUW_of_all : AllUW I C → TheoremUW` is UW/Reduction.lean.

## The implementation `ImplW`

BL-OW enters as data: its program `P` with the cost constants `C'`, `k`; the schedule `(u, b0, y0)` that PARAM
computes and the reference shares; its pure plays; and the shift and the
advice of its run record. The coin layout of BL-OW is BL-O's (R5w reads no coin), so the
windows are `DO`, `DO'`, the coupled world is `extO` and the record `recUW` is Theorem U's `recO` with the shift, the
advice and the plays of BL-OW: the losses, the position, the soundness event and the coupling are `recO`'s.

## The Props, by group

* Group A, the reference at T4U with sure ranges:
  - `RowsUW` (UW-ROWS): `RowsW`, the rows of `Df2Rows` at `parW` and the rows that read `u`, the
    closure and event (b) under the clip;
  - `SIFactsUW` (Proposition sifacts at `parW`): `Df2SIFacts` with `df2oPar d n δ` replaced by `parW d n u`;
  - `DetUW` (DET at T4U on the weighted epoch): `Df2Det` with the levels `sYW`, `b1W`, `bnW`, without event (a);
  - `CondIncrW`, `CondBiasW`, `LemmaUSetW` (UW-CENTRE, verbatim): the centred increment, the bias
    of Lemma SK' (i), (iv), and Lemma U for the centred increments;
  - `EvProbUW` (W-SETE and W-EV at the level `δc`: events (a) to (e) and Azuma, with Lemma SK'), `RefRegUW`
    (W-DET), `RefPropUW` (their conjunction, `RefPropW` for P° of Theorem UW), `CoupStepPropUW` (Step 2 of SHADOW);
* Group B, BL-OW and its bit chain:
  - `BLOMachOK I.P I.C' I.k` (Theorem U's Prop, unchanged), `BLOWLink`, `PlayIntUW` (the program and its cost);
  - `SchedUW` (PARAM's `u`, `b0`, `y0` in the regime);
  - `PosRecUW`, `MeasRecUW`, `BitsRecUW`, `EngineRecUW` (the four W-hypotheses of SHADOW on `recUW`; `PosRecUW` and
    `BitsRecUW` are proved for every `ImplW` in UW/Rec.lean);
  - `DomW` (DOM-W, C7); `obsW_lip` (Lemma E2w, the two 1-Lipschitz maps)
    and `obsW_sure` (Lemma WR (ii), (iii) and Lemma SK' (i) for the observation) are proved below;
* Group C, the arithmetic: `ThrUW` (Lemma thr at T4U: the threshold, the budget `δ_ref ≤ δ/2`, the trivial range).

`AsmUW I C` collects what the assembly reads; `AllUW I C` the bricks and the routes between them
(`detOf`, `refRegOf`, `evProbOf`, `engineOf`), each route the assembly of one group. The final proof is
`AdversarialBco.UW.theoremUW : TheoremUW`, the name the Comparator challenge of `TheoremMinimaxMatched` expects, as
`theoremUW_of_all` applied to the proved bricks.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped Matrix

namespace AdversarialBco.UW

open AdversarialBco.RealRAM AdversarialBco.Poly AdversarialBco.Poly.Layer2 AdversarialBco.Bit.Cpl
open AdversarialBco.Unified.World AdversarialBco.Unified.Asm
open AdversarialBco.Unified.BLO (NeO kDel DO DO' parO BLOMachOK)
open AdversarialBco.Unified (NoisyAdv regretU initU sizeU envWorld)
open AdversarialBco.BitRAM (toE)
open AdversarialBco.BitRAMO (InstrO WorldO playedO WeakMemOracle)
open AdversarialBco.Poly.EvSI (gam)

variable {d : ℕ}

/-! ## Group A: the reference at T4U with sure ranges -/

/-- `θ_n = 2 η B_n` at the level `B_n` with `u`. -/
noncomputable def thnW (p : Df2OPar) (d n : ℕ) (u : ℝ) : ℝ := 2 * p.eta * bnW p d n u

/-- `dev' = η κ B_n/(2 L λ²)`. -/
noncomputable def devPW (p : Df2OPar) (d n : ℕ) (u : ℝ) : ℝ := p.eta * p.kap * bnW p d n u / (2 * p.Le * p.lam ^ 2)

/-- `dev = b₁ + B_n/(4 L λ²)`. -/
noncomputable def devW (p : Df2OPar) (d n : ℕ) (u : ℝ) : ℝ := b1W p d n u + bnW p d n u / (4 * p.Le * p.lam ^ 2)

/-- `dev_κ = b₁ + B_n/(8 L λ²)`. -/
noncomputable def devKW (p : Df2OPar) (d n : ℕ) (u : ℝ) : ℝ := b1W p d n u + bnW p d n u / (8 * p.Le * p.lam ^ 2)

/-- `stab = 2 η² κ₀ s_Y ξ̄` under the sure ranges, `ξ̄ = b0 + 1`. -/
noncomputable def stabW (p : Df2OPar) (n : ℕ) (ρ : RefW) : ℝ := 2 * p.eta ^ 2 * p.k0 * sYW n ρ.y0 ρ.δc * (ρ.b0 + 1)

/-- **The rows of T4U with sure ranges**: every row of Theorem U's record
`Df2Rows` at `parW`, the rows of the deterministic layer at the levels with `u` (`r12` to `r24b` with `B_n`, `b₁` of
`bnW`, `b1W` and the stability term `stabW`), the closure (`a ≥ 1/2`, `q ≥ 1/4` from `|c_Y| ≤ η κ λ κ₀ y0` and
`|ξ|² - 1 ≤ b0` where the weight is positive), and event (b) under the clip (`y0² log(7/δc) ≤ n`). The event
needs are the hypotheses of the event lemmas, read inside `EvProbUW`. -/
structure RowsW (d n : ℕ) (ρ : RefW) : Prop where
  base : Df2Rows (parW d n ρ.u) d n
  r12w : thnW (parW d n ρ.u) d n ρ.u ≤ 1
  r19ow : 2 * (parW d n ρ.u).eta + d * (parW d n ρ.u).Le / (parW d n ρ.u).lam + df2Pri (parW d n ρ.u) +
    stabW (parW d n ρ.u) n ρ + (parW d n ρ.u).eta * devKW (parW d n ρ.u) d n ρ.u + 1 ≤ (parW d n ρ.u).rho
  r20w : 2 * devPW (parW d n ρ.u) d n ρ.u ≤ (parW d n ρ.u).gam * (parW d n ρ.u).rho
  r21w : 16 * (parW d n ρ.u).c1 * (parW d n ρ.u).rho * (parW d n ρ.u).Le * (parW d n ρ.u).lam ^ 2 +
    2 * thnW (parW d n ρ.u) d n ρ.u < 1
  r22w : 3 * (parW d n ρ.u).eta + d * (parW d n ρ.u).Le / (parW d n ρ.u).lam +
    10 * (parW d n ρ.u).eta / ((parW d n ρ.u).eps * (parW d n ρ.u).lam) + 2 * df2Pri (parW d n ρ.u) +
    (parW d n ρ.u).eta * devW (parW d n ρ.u) d n ρ.u ≤ ((parW d n ρ.u).theta - (parW d n ρ.u).alpha) * (parW d n ρ.u).rho
  r24ow : 2 * (parW d n ρ.u).eta + 8 * df2Pri (parW d n ρ.u) + 7 * stabW (parW d n ρ.u) n ρ +
    7 * ((parW d n ρ.u).eta * devKW (parW d n ρ.u) d n ρ.u) + 7 * ((parW d n ρ.u).eta * devW (parW d n ρ.u) d n ρ.u) +
    devPW (parW d n ρ.u) d n ρ.u + 7 * (parW d n ρ.u).theta * (parW d n ρ.u).rho + 7 ≤
      ((parW d n ρ.u).c1 - (parW d n ρ.u).gam) * (parW d n ρ.u).rho
  r24bw : 3 + 2 * df2Pri (parW d n ρ.u) + stabW (parW d n ρ.u) n ρ +
    (parW d n ρ.u).eta * devKW (parW d n ρ.u) d n ρ.u + (parW d n ρ.u).eta * devW (parW d n ρ.u) d n ρ.u +
    devPW (parW d n ρ.u) d n ρ.u + (parW d n ρ.u).theta * (parW d n ρ.u).rho ≤
      ((parW d n ρ.u).c1 - (parW d n ρ.u).gam) * (parW d n ρ.u).rho
  clo_a : (parW d n ρ.u).eta * (parW d n ρ.u).kap * (parW d n ρ.u).lam * (parW d n ρ.u).k0 * ρ.y0 ≤ 1 / 2
  clo_q : (parW d n ρ.u).eta * (parW d n ρ.u).kap * (parW d n ρ.u).lam * (parW d n ρ.u).k0 * ρ.y0 * ρ.b0 ≤ 3 / 4
  evb : ρ.y0 ^ 2 * Real.log (7 / ρ.δc) ≤ n

/-- **UW-ROWS**: the rows hold on the regime. -/
def RowsUW : Prop := ∀ (d n : ℕ) (ρ : RefW), RegimeW d n ρ → RowsW d n ρ

/-- The analytic facts of SI at the record `p`: the body of `Df2SIFacts` with `df2oPar d n δ` replaced by `p`. -/
def SIFactsAt (p : Df2OPar) (Kt : Set (E d)) (g : E d → ℝ) : Prop :=
  (ConvexOn ℝ Set.univ (df2Ext p Kt g) ∧ (∀ x, 0 ≤ df2Ext p Kt g x) ∧
    (∀ x y, |df2Ext p Kt g x - df2Ext p Kt g y| ≤ 8 / p.eps * ‖x - y‖) ∧
    ∀ y ∈ df2KepsOf Kt p.eps, df2Ext p Kt g (WithLp.toLp 2 y) = g (WithLp.toLp 2 y)) ∧
  ∀ (mu : Fin d → ℝ) (A : Matrix (Fin d) (Fin d) ℝ), Df2StateOK p Kt mu A →
    (ContDiff ℝ 2 (df2SurrOf p Kt g mu A) ∧ ConvexOn ℝ Set.univ (df2SurrOf p Kt g mu A) ∧
      ∀ z, df2SurrOf p Kt g mu A z ≤ df2Ext p Kt g z) ∧
    (∀ z ∈ df2KepsOf Kt p.eps, -(10 / (p.lam * p.eps)) ≤ df2SurrOf p Kt g mu A (WithLp.toLp 2 z) ∧
      df2SurrOf p Kt g mu A (WithLp.toLp 2 z) ≤ 1) ∧
    ((∫ z, df2Ext p Kt g (WithLp.toLp 2 mu + Matrix.toEuclideanCLM (𝕜 := ℝ) A z) ∂(stdGaussian (E d))) -
        df2SurrOf p Kt g mu A (WithLp.toLp 2 mu) ≤
      2 / p.lam * (df2HessM (df2SurrOf p Kt g mu A) (WithLp.toLp 2 mu) * (A * Aᵀ)).trace + 2 * p.δe * d / p.lam) ∧
    (∀ (z : E d) (v : Fin d → ℝ), |df2Sq (df2HessM (df2SurrOf p Kt g mu A) z) v| ≤
      p.lam * (8 / p.eps) / (1 - p.lam) * Real.sqrt (2 * d * p.sig2) * df2Sq (A * Aᵀ)⁻¹ v) ∧
    (∀ (z : E d) (v : Fin d → ℝ), |df2Sq (df2HessM (df2SurrOf p Kt g mu A) z) v| ≤
      p.lam * (8 / p.eps) / (1 - p.lam) * Real.sqrt (d / p.δe) * (v ⬝ᵥ v)) ∧
    (∀ x y : Fin d → ℝ, p.lam ^ 2 * df2Sq (A * Aᵀ)⁻¹ (x - y) ≤ 1 / p.Le →
      ((2 : ℝ) • df2HessM (df2SurrOf p Kt g mu A) (WithLp.toLp 2 y) + p.δe • (A * Aᵀ)⁻¹ -
        df2HessM (df2SurrOf p Kt g mu A) (WithLp.toLp 2 x)).PosSemidef) ∧
    (∀ y : Fin d → ℝ, p.lam ^ 2 * df2Sq (A * Aᵀ)⁻¹ (y - mu) ≤ 1 / p.Le →
      df2SurrOf p Kt g mu A (WithLp.toLp 2 mu) - df2SurrOf p Kt g mu A (WithLp.toLp 2 y) ≤
        df2GradM (df2SurrOf p Kt g mu A) (WithLp.toLp 2 mu) ⬝ᵥ (mu - y) -
          1 / 4 * df2Sq (df2HessM (df2SurrOf p Kt g mu A) (WithLp.toLp 2 mu)) (y - mu) + p.δe / p.lam ^ 2)

/-- **Proposition sifacts at T4U**: the facts of SI at `parW d n u` for `1 ≤ u`, `ε ≤ 1/2`. -/
def SIFactsUW : Prop :=
  ∀ (d n : ℕ) (u : ℝ) (Kt : Set (E d)) (g : E d → ℝ), 1 ≤ d → 1 ≤ n → 1 ≤ u → (parW d n u).eps ≤ 1 / 2 →
    Df2Body d (parW d n u).R Kt → AdmLoss Kt g → SIFactsAt (parW d n u) Kt g

/-- The context of an epoch of the reference of Theorem UW: T4U, the horizon `n`, the body, the routines. -/
noncomputable def ctxW (d n : ℕ) (ρ : RefW) (Kt : Set (E d)) (ap : ℕ → ApFun d) : Df2Ctx d :=
  ⟨parW d n ρ.u, n, Kt, ap⟩

/-- The four events of DET with sure ranges at the levels of T4U, on the weighted path `πw`. -/
def EvDetW (n : ℕ) (ρ : RefW) (c : Df2Ctx d) (πw : Df2Path d) (m : ℕ) : Prop :=
  EvYW c πw (sYW n ρ.y0 ρ.δc) m ∧ EvLQW c πw (b1W c.p d n ρ.u) m ∧ EvSDFW c πw (bnW c.p d n ρ.u) m ∧
    EvDQW c πw (bnW c.p d n ρ.u) m

/-- **DET at T4U with sure ranges** (`Df2Det` for the weighted epoch): on every path, the weighted epoch of length
`m ≤ n` meets (a) and (b5') of E1-loc when the four events with sure ranges hold on its weighted path. No event (a):
the closure is sure under the clip and the weight. -/
def DetUW : Prop :=
  ∀ (d n : ℕ) (ρ : RefW) (Kt : Set (E d)) (ap : ℕ → ApFun d) (π : Df2Path d) (m : ℕ),
    RegimeW d n ρ → 1 ≤ m → m ≤ n → Df2Body d (parW d n ρ.u).R Kt → (∀ s, ApSpec (ap s)) →
    (∀ s < m, AdmLoss Kt (π.g s)) →
    EvDetW n ρ (ctxW d n ρ Kt ap) (pathW (ctxW d n ρ Kt ap) ρ.b0 ρ.y0 π) m →
    (ctxW d n ρ Kt ap).EpochOK (pathW (ctxW d n ρ Kt ap) ρ.b0 ρ.y0 π) m

/-- **(W1) `cond_incr_w`**: the increment `X = W(ξ, E + P e) D`, centred at its conditional
mean, is a martingale difference with the paper's variance proxy `E_z[(E² + P²) D²]`. -/
def CondIncrW : Prop :=
  ∀ (d : ℕ) {Ω S : Type} (𝒢 : MeasurableSpace Ω) {m0 : MeasurableSpace Ω} [MeasurableSpace S] (μ : Measure Ω)
    [IsProbabilityMeasure μ], 𝒢 ≤ m0 → ∀ (σ : Ω → S) (ξ : Ω → Fin d → ℝ) (e : Ω → ℝ),
    Measurable[𝒢] σ → Measurable ξ → Measurable e → μ.map ξ = gam d →
    Indep (MeasurableSpace.comap ξ inferInstance) 𝒢 μ → Integrable (fun ω => Real.exp (e ω ^ 2)) μ →
    μ[e | 𝒢 ⊔ MeasurableSpace.comap ξ inferInstance] =ᵐ[μ] 0 →
    μ[fun ω => Real.exp (e ω ^ 2) | 𝒢 ⊔ MeasurableSpace.comap ξ inferInstance] ≤ᵐ[μ] (fun _ => 2) →
    ∀ (E P D : S × (Fin d → ℝ) → ℝ), Measurable E → Measurable P → Measurable D →
    ∀ (K : ℝ) (k : ℕ), 0 ≤ K → (∀ x, |E x| ≤ K * (1 + ‖x.2‖) ^ k) → (∀ x, |P x| ≤ K * (1 + ‖x.2‖) ^ k) →
    (∀ x, |D x| ≤ K * (1 + ‖x.2‖) ^ k) →
    ∀ (Wf : (Fin d → ℝ) → ℝ → ℝ), Measurable (Function.uncurry Wf) → (∀ x y, |Wf x y| ≤ |y|) →
      Integrable (fun ω => Wf (ξ ω) (E (σ ω, ξ ω) + P (σ ω, ξ ω) * e ω) * D (σ ω, ξ ω)) μ ∧
      Integrable (fun ω => (Wf (ξ ω) (E (σ ω, ξ ω) + P (σ ω, ξ ω) * e ω) * D (σ ω, ξ ω)) ^ 2) μ ∧
      μ[fun ω => Wf (ξ ω) (E (σ ω, ξ ω) + P (σ ω, ξ ω) * e ω) * D (σ ω, ξ ω) -
          μ[fun ω => Wf (ξ ω) (E (σ ω, ξ ω) + P (σ ω, ξ ω) * e ω) * D (σ ω, ξ ω) | 𝒢] ω | 𝒢] =ᵐ[μ] 0 ∧
      μ[fun ω => (Wf (ξ ω) (E (σ ω, ξ ω) + P (σ ω, ξ ω) * e ω) * D (σ ω, ξ ω) -
          μ[fun ω => Wf (ξ ω) (E (σ ω, ξ ω) + P (σ ω, ξ ω) * e ω) * D (σ ω, ξ ω) | 𝒢] ω) ^ 2 | 𝒢] ≤ᵐ[μ]
        fun ω => ∫ z, (E (σ ω, z) ^ 2 + P (σ ω, z) ^ 2) * D (σ ω, z) ^ 2 ∂(gam d)

/-- **(W2) `cond_bias_w`** (Lemma SK' (i) and (iv)): when the weight and the clip change
the observation only on `Bset`, the conditional mean of `X = W(ξ, Y) D` is Lemma ub's mean `E_z[E D]` up to
`2 (E[Y⁴ | 𝒢])^{1/4} (E_z D⁴)^{1/4} P(Bset | 𝒢)^{1/2}`. -/
def CondBiasW : Prop :=
  ∀ (d : ℕ) {Ω S : Type} (𝒢 : MeasurableSpace Ω) {m0 : MeasurableSpace Ω} [MeasurableSpace S] (μ : Measure Ω)
    [IsProbabilityMeasure μ], 𝒢 ≤ m0 → ∀ (σ : Ω → S) (ξ : Ω → Fin d → ℝ) (e : Ω → ℝ),
    Measurable[𝒢] σ → Measurable ξ → Measurable e → μ.map ξ = gam d →
    Indep (MeasurableSpace.comap ξ inferInstance) 𝒢 μ → Integrable (fun ω => Real.exp (e ω ^ 2)) μ →
    μ[e | 𝒢 ⊔ MeasurableSpace.comap ξ inferInstance] =ᵐ[μ] 0 →
    μ[fun ω => Real.exp (e ω ^ 2) | 𝒢 ⊔ MeasurableSpace.comap ξ inferInstance] ≤ᵐ[μ] (fun _ => 2) →
    ∀ (E P D : S × (Fin d → ℝ) → ℝ), Measurable E → Measurable P → Measurable D →
    ∀ (K : ℝ) (k : ℕ), 0 ≤ K → (∀ x, |E x| ≤ K * (1 + ‖x.2‖) ^ k) → (∀ x, |P x| ≤ K * (1 + ‖x.2‖) ^ k) →
    (∀ x, |D x| ≤ K * (1 + ‖x.2‖) ^ k) →
    ∀ (Wf : (Fin d → ℝ) → ℝ → ℝ), Measurable (Function.uncurry Wf) → (∀ x y, |Wf x y| ≤ |y|) →
    ∀ (Bset : Set Ω), MeasurableSet Bset →
      (∀ ω ∉ Bset, Wf (ξ ω) (E (σ ω, ξ ω) + P (σ ω, ξ ω) * e ω) = E (σ ω, ξ ω) + P (σ ω, ξ ω) * e ω) →
      ∀ᵐ ω ∂μ, |μ[fun ω => Wf (ξ ω) (E (σ ω, ξ ω) + P (σ ω, ξ ω) * e ω) * D (σ ω, ξ ω) | 𝒢] ω -
          ∫ z, E (σ ω, z) * D (σ ω, z) ∂(gam d)| ≤
        2 * (μ[fun ω => (E (σ ω, ξ ω) + P (σ ω, ξ ω) * e ω) ^ 4 | 𝒢] ω) ^ (1 / 4 : ℝ) *
          (∫ z, D (σ ω, z) ^ 4 ∂(gam d)) ^ (1 / 4 : ℝ) * (μ[Bset.indicator 1 | 𝒢] ω) ^ (1 / 2 : ℝ)

/-- **(W3) `lemmaU_setW`**: Lemma U for the increments `W(ξ_s, E_s + P_s e_s) D_c` centred at
their conditional means, the conclusion of `lemmaU_setE` with `zSeq` replaced; the levels `V`, `R` are functions of
the path, so event (d) goes through it too. -/
def LemmaUSetW : Prop :=
  ∀ (d : ℕ) {Ω S ι : Type} [m0 : MeasurableSpace Ω] [MeasurableSpace S] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (𝒢 : Filtration ℕ m0) (C : Finset ι) (m n : ℕ), m ≤ n →
    ∀ (σ : ℕ → Ω → S) (ξ : ℕ → Ω → Fin d → ℝ) (e : ℕ → Ω → ℝ),
    (∀ s < m, Measurable[𝒢 s] (σ s)) → (∀ s, Measurable[𝒢 (s + 1)] (ξ s)) → (∀ s, μ.map (ξ s) = gam d) →
    (∀ s, Indep (MeasurableSpace.comap (ξ s) inferInstance) (𝒢 s) μ) → (∀ s, Measurable[𝒢 (s + 1)] (e s)) →
    (∀ s, Integrable (fun ω => Real.exp (e s ω ^ 2)) μ) →
    (∀ s, μ[e s | 𝒢 s ⊔ MeasurableSpace.comap (ξ s) inferInstance] =ᵐ[μ] 0) →
    (∀ s, μ[fun ω => Real.exp (e s ω ^ 2) | 𝒢 s ⊔ MeasurableSpace.comap (ξ s) inferInstance] ≤ᵐ[μ] fun _ => 2) →
    ∀ (E P : ℕ → S × (Fin d → ℝ) → ℝ) (D : ι → ℕ → S × (Fin d → ℝ) → ℝ),
    (∀ s < m, Measurable (E s)) → (∀ s < m, Measurable (P s)) → (∀ c s, s < m → Measurable (D c s)) →
    ∀ (Kc : ι → ℝ) (k : ℕ), (∀ c, 0 ≤ Kc c) →
    (∀ c s, s < m → ∀ x, |E s x| ≤ Kc c * (1 + ‖x.2‖) ^ k) →
    (∀ c s, s < m → ∀ x, |P s x| ≤ Kc c * (1 + ‖x.2‖) ^ k) →
    (∀ c s, s < m → ∀ x, |D c s x| ≤ Kc c * (1 + ‖x.2‖) ^ k) →
    ∀ (Wf : (Fin d → ℝ) → ℝ → ℝ), Measurable (Function.uncurry Wf) → (∀ x y, |Wf x y| ≤ |y|) →
    ∀ (κ δ' : ℝ), 0 < κ → 0 < δ' → δ' ≤ 1 → ∀ (V R : ι → ℕ → Ω → ℝ),
      μ {ω | ∃ c ∈ C, ∃ t < m, 0 ≤ V c t ω ∧ 1 ≤ κ * R c t ω ∧
          ∑ s ∈ Finset.range (t + 1),
            ∫ z, (E s (σ s ω, z) ^ 2 + P s (σ s ω, z) ^ 2) * D c s (σ s ω, z) ^ 2 ∂(gam d) ≤ V c t ω ∧
          (∀ s ≤ t, |(fun c s ω => if s < m then
              Wf (ξ s ω) (E s (σ s ω, ξ s ω) + P s (σ s ω, ξ s ω) * e s ω) * D c s (σ s ω, ξ s ω) else 0) c s ω -
            μ[(fun c s ω => if s < m then
              Wf (ξ s ω) (E s (σ s ω, ξ s ω) + P s (σ s ω, ξ s ω) * e s ω) * D c s (σ s ω, ξ s ω) else 0) c s |
              𝒢 s] ω| ≤ R c t ω) ∧
          3 * Real.sqrt (V c t ω * Real.log (4 * (n * C.card) * max (κ * R c t ω) (κ * Real.sqrt (V c t ω)) / δ')) +
            2 * R c t ω * Real.log (4 * (n * C.card) * max (κ * R c t ω) (κ * Real.sqrt (V c t ω)) / δ') <
            |∑ s ∈ Finset.range (t + 1),
              ((fun c s ω => if s < m then
                  Wf (ξ s ω) (E s (σ s ω, ξ s ω) + P s (σ s ω, ξ s ω) * e s ω) * D c s (σ s ω, ξ s ω) else 0) c s ω -
                μ[(fun c s ω => if s < m then
                  Wf (ξ s ω) (E s (σ s ω, ξ s ω) + P s (σ s ω, ξ s ω) * e s ω) * D c s (σ s ω, ξ s ω) else 0) c s |
                  𝒢 s] ω)|} ≤ ENNReal.ofReal δ'

/-- **W-SETE and W-EV at the level `δc`**: off `Ω_ref` of Theorem UW, the case has probability at most `δ_ref(δc)`
(events (a) at the level, (b) to (e) with sure ranges at T4U, through Lemma SK' and the wrapper, and Azuma). The
first clause of `RefPropW` for P° of Theorem UW. -/
def EvProbUW : Prop :=
  ∀ (d n : ℕ) (ρ : RefW) (K : Set (E d)) (Ω : Type) [MeasurableSpace Ω] (W : CWorld d Ω) (B : RunW d n K W),
    RegimeW d n ρ → IsClosed K → Convex ℝ K → WorldLawOK W → Measurable[W.𝓕 0] B.pos → CoupLaw B.Coup →
    BLMeasW B → W.μ {ω | B.Case ρ.δc ω ∧ ¬ GoodU B ρ ω} ≤ ENNReal.ofReal (deltaRefW n ρ.δc)

/-- **W-DET at T4U**: on the case and `Ω_ref` of Theorem UW, P°'s regret is at most `bRegW`. The second clause of
`RefPropW` for P° of Theorem UW. -/
def RefRegUW : Prop :=
  ∀ (d n : ℕ) (ρ : RefW) (K : Set (E d)) (Ω : Type) [MeasurableSpace Ω] (W : CWorld d Ω) (B : RunW d n K W),
    RegimeW d n ρ → IsClosed K → Convex ℝ K → ∀ ω, B.Case ρ.δc ω → GoodU B ρ ω →
      regretPts K (B.loss ω) (fun t => refPlayU B ρ t ω) n ≤ bRegW d n ρ.u ρ.δc

/-- **(O1) for P° of Theorem UW** (`RefPropW` with `cRoundW`, T4U, the level `δc` and `GoodU`). -/
def RefPropUW : Prop :=
  ∀ (d n : ℕ) (ρ : RefW) (K : Set (E d)) (Ω : Type) [MeasurableSpace Ω] (W : CWorld d Ω) (B : RunW d n K W),
    RegimeW d n ρ → IsClosed K → Convex ℝ K → WorldLawOK W → Measurable[W.𝓕 0] B.pos → CoupLaw B.Coup →
    BLMeasW B →
      W.μ {ω | B.Case ρ.δc ω ∧ ¬ GoodU B ρ ω} ≤ ENNReal.ofReal (deltaRefW n ρ.δc) ∧
        ∀ ω, B.Case ρ.δc ω → GoodU B ρ ω → regretPts K (B.loss ω) (fun t => refPlayU B ρ t ω) n ≤ bRegW d n ρ.u ρ.δc

/-- **Step 2 of SHADOW for P° of Theorem UW** (`CoupStepPropW` with `modeU`). -/
def CoupStepPropUW : Prop :=
  ∀ (d n : ℕ) (ρ : RefW) (K : Set (E d)) (Ω : Type) [MeasurableSpace Ω] (W : CWorld d Ω) (B : RunW d n K W)
    (κ0 κ1 : ℝ),
    RegimeW d n ρ → IsClosed K → Convex ℝ K → WorldLawOK W → Measurable[W.𝓕 0] B.pos → CoupLaw B.Coup →
    CoupTV B.Coup → BLMeasW B → 0 ≤ κ0 → 0 ≤ κ1 → ∀ t,
      W.μ {ω | DU B ρ t ω ∧ 0 < (shRU B ρ t ω).2 ∧ tvB (shRU B ρ t ω).1 (shRU B ρ t ω).2 ≤ κ0 + κ1 * |W.nz t ω|} ≤
        ENNReal.ofReal (κ0 + κ1)

/-! ## Group B: BL-OW, its record and its bit chain -/

/-- **BL-OW as data**: the program with its cost constants, PARAM-W's schedule `(u', b0, y0)` shared with the
reference (`u' = u_up = up_p(1 + k_δ ℓ_2/(7 d ℓ⁻))`, no cap; `b0`, `y0` from
upward enclosures on the grid `2^{-p}`), the pure plays, and the shift and the advice of its run record on the
extension of an environment with BL-O's windows (the coin layout of BL-O is unchanged). -/
structure ImplW where
  P : List InstrO
  C' : ℝ
  k : ℕ
  u : ℕ → ℕ → ℚ → ℝ
  b0 : ℕ → ℕ → ℚ → ℝ
  y0 : ℕ → ℕ → ℚ → ℝ
  play : (d n : ℕ) → ℚ → ℚ → ℚ → (Fin d → ℚ) → WorldO d → ℕ → Fin d → ℚ
  sh : ∀ {d : ℕ} {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} {K : Set (E d)} {coin : Ω → ℕ → Bool}
    {loss : ℕ → Ω → E d → ℝ} {noise : ℕ → Ω → ℝ} (n : ℕ) (δ r0 R0 : ℚ) (a : Fin d → ℚ)
    (_orc : (Fin d → ℚ) → ℕ → Bool), NoisyAdv K n (DO d n δ r0 R0 a) (DO' d n δ r0 R0 a) μ coin loss noise →
    Convex ℝ K → ℕ → Ω × (ℕ → ℝ) → Df2Mode d → ℝ × ℝ
  adv : ∀ {d : ℕ} {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} {K : Set (E d)} {coin : Ω → ℕ → Bool}
    {loss : ℕ → Ω → E d → ℝ} {noise : ℕ → Ω → ℝ} (n : ℕ) (δ r0 R0 : ℚ) (a : Fin d → ℚ)
    (_orc : (Fin d → ℚ) → ℕ → Bool), NoisyAdv K n (DO d n δ r0 R0 a) (DO' d n δ r0 R0 a) μ coin loss noise →
    Convex ℝ K → ℕ → Ω × (ℕ → ℝ) → Df2Mode d → Adv d

/-- The reference's parameters at the input: PARAM's schedule and the level `δ_c = 1/(2^{k_δ} N_0)`. -/
noncomputable def refAt (I : ImplW) (d n : ℕ) (δ : ℚ) : RefW :=
  ⟨I.u d n δ, I.b0 d n δ, I.y0 d n δ, deltaC d n (kDel δ)⟩

/-- **BL-OW's run record** on the extension: `recO` with BL-OW's shift, advice and plays. -/
noncomputable def recUW (I : ImplW) {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} {K : Set (E d)}
    {coin : Ω → ℕ → Bool} {loss : ℕ → Ω → E d → ℝ} {noise : ℕ → Ω → ℝ} (n : ℕ) (δ r0 R0 : ℚ) (a : Fin d → ℚ)
    (orc : (Fin d → ℚ) → ℕ → Bool) (h : NoisyAdv K n (DO d n δ r0 R0 a) (DO' d n δ r0 R0 a) μ coin loss noise)
    (hK : Convex ℝ K) : RunW d n K (extO n δ r0 R0 a h) :=
  { recO n δ r0 R0 a orc h hK with
    sh := I.sh n δ r0 R0 a orc h hK
    adv := I.adv n δ r0 R0 a orc h hK
    play := fun t p => toE (I.play d n δ r0 R0 a (envWorld orc coin loss noise p.1) t) }

/-- **The program link** for BL-OW. -/
def BLOWLink (I : ImplW) : Prop :=
  ∀ (d n : ℕ) (δ r0 R0 : ℚ) (a : Fin d → ℚ), 1 ≤ d → 1 ≤ n → 0 < δ → δ < 1 → 0 < r0 → r0 ≤ R0 →
    ∀ (w : WorldO d) (t : ℕ), t < n → playedO I.P w (initU d n δ r0 R0 a) t = toE (I.play d n δ r0 R0 a w t)

/-- **The plays are interior** (`PlayIntO` for BL-OW). -/
def PlayIntUW (I : ImplW) : Prop :=
  ∀ (d n : ℕ) (δ r0 R0 : ℚ) (a : Fin d → ℚ) (K : Set (E d)) (w : WorldO d), 1 ≤ d → 0 < r0 → Convex ℝ K →
    Metric.closedBall (toE a) (r0 : ℝ) ⊆ K → WeakMemOracle K w.orc →
    ∀ t, toE (I.play d n δ r0 R0 a w t) ∈ interior K

/-- **PARAM-W's schedule** (Lemma PARAM-W (ii), (iv)): in the case (`ε(u_δ) ≤ 1/8`, inside case (i) of the proof of
Theorem UW, so `u' = u_up`), the reference at PARAM-W's values is in its regime,
and `u_δ ≤ u' ≤ u_δ (1 + 2^{-p-12}) + 2^{-p}`, below `uF d n (k_δ + 1)`. -/
def SchedUW (I : ImplW) : Prop :=
  ∀ (d n : ℕ) (δ : ℚ), 1 ≤ d → 1 ≤ n → 0 < δ → δ < 1 → RunCaseUW d n δ →
    RegimeW d n (refAt I d n δ) ∧ uF d n (kDel δ) ≤ I.u d n δ ∧ I.u d n δ ≤ uF d n (kDel δ + 1)

/-- **(POS) for BL-OW's record** (`PosRecO` for `recUW`, at the level `δc`). -/
def PosRecUW (I : ImplW) : Prop :=
  ∀ (d n : ℕ) (δ r0 R0 : ℚ) (a : Fin d → ℚ) (K : Set (E d)) (orc : (Fin d → ℚ) → ℕ → Bool)
    (hI : InpU n δ r0 R0 a K orc), RunCaseUW d n δ →
    ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) (coin : Ω → ℕ → Bool) (loss : ℕ → Ω → E d → ℝ)
      (noise : ℕ → Ω → ℝ) (h : NoisyAdv K n (DO d n δ r0 R0 a) (DO' d n δ r0 R0 a) μ coin loss noise),
      ∃ δpos : ℝ, 0 ≤ δpos ∧ δpos ≤ (δ : ℝ) / 4 ∧
        PosHypW (recUW I n δ r0 R0 a orc h hI.convex) (refAt I d n δ).δc δpos

/-- **(O4-M) for BL-OW's record** (`MeasRecO` for `recUW`). -/
def MeasRecUW (I : ImplW) : Prop :=
  ∀ (d n : ℕ) (δ r0 R0 : ℚ) (a : Fin d → ℚ) (K : Set (E d)) (orc : (Fin d → ℚ) → ℕ → Bool)
    (hI : InpU n δ r0 R0 a K orc), RunCaseUW d n δ →
    ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) (coin : Ω → ℕ → Bool) (loss : ℕ → Ω → E d → ℝ)
      (noise : ℕ → Ω → ℝ) (h : NoisyAdv K n (DO d n δ r0 R0 a) (DO' d n δ r0 R0 a) μ coin loss noise),
      BLMeasW (recUW I n δ r0 R0 a orc h hI.convex)

/-- **(O4), the bit clause for BL-OW's record** (`BitsRecO` for `recUW`; the soundness event is `recO`'s). -/
def BitsRecUW (I : ImplW) : Prop :=
  ∀ (d n : ℕ) (δ r0 R0 : ℚ) (a : Fin d → ℚ) (K : Set (E d)) (orc : (Fin d → ℚ) → ℕ → Bool)
    (hI : InpU n δ r0 R0 a K orc), RunCaseUW d n δ →
    ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) (coin : Ω → ℕ → Bool) (loss : ℕ → Ω → E d → ℝ)
      (noise : ℕ → Ω → ℝ) (h : NoisyAdv K n (DO d n δ r0 R0 a) (DO' d n δ r0 R0 a) μ coin loss noise),
      ∃ δbits : ℝ, 0 ≤ δbits ∧ δbits ≤ (δ : ℝ) / 8 ∧ BitsHypW (recUW I n δ r0 R0 a orc h hI.convex) δbits

/-- **Step 1 of SHADOW for BL-OW's record** (for `recUW` and P° of Theorem UW): Theorem BUD-W, Lemmas
E2w, WR, errors-W and GUARD-W (against the reference's threshold `W_ref = R + 4d (N_0/(L_f u'))^{1/2}`) in pieces C
and D. -/
def EngineRecUW (I : ImplW) : Prop :=
  ∀ (d n : ℕ) (δ r0 R0 : ℚ) (a : Fin d → ℚ) (K : Set (E d)) (orc : (Fin d → ℚ) → ℕ → Bool)
    (hI : InpU n δ r0 R0 a K orc), RunCaseUW d n δ →
    ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) (coin : Ω → ℕ → Bool) (loss : ℕ → Ω → E d → ℝ)
      (noise : ℕ → Ω → ℝ) (h : NoisyAdv K n (DO d n δ r0 R0 a) (DO' d n δ r0 R0 a) μ coin loss noise),
      ∃ κ0 κ1 : ℝ, 0 ≤ κ0 ∧ 0 ≤ κ1 ∧ (n : ℝ) * (κ0 + κ1) ≤ (δ : ℝ) / 8 ∧
        EngineHypUW (recUW I n δ r0 R0 a orc h hI.convex) (refAt I d n δ) κ0 κ1

/-- **DOM-W** (C7): `c̄_w (1 + Ξ_{w1}²) ≤ 1.75·10^{-35}` with `c̄_w = κ_c y0`, `κ_c = η κ λ κ₀` at
T4U, `Ξ_{w1} = (b0 + 1)^{1/2} + 2^{-p-1} + 1` at BL-O's precision `p`. -/
def DomW : Prop :=
  ∀ (d n : ℕ) (δ : ℚ) (ρ : RefW), 0 < δ → δ < 1 → RunCaseUW d n δ → RegimeW d n ρ →
    (parW d n ρ.u).eta * (parW d n ρ.u).kap * (parW d n ρ.u).lam * (parW d n ρ.u).k0 * ρ.y0 *
        (1 + (Real.sqrt (ρ.b0 + 1) + 1 / 2 ^ ((parO d n δ).p + 1) + 1) ^ 2) ≤ 1.75e-35

/-! ### Lemma E2w and Lemma WR on the observation (proved) -/

theorem wgt_mem (b0 s : ℝ) : 0 ≤ wgt b0 s ∧ wgt b0 s ≤ 1 :=
  ⟨le_min zero_le_one (le_max_left _ _), min_le_left _ _⟩

theorem wgt_lip (b0 s s' : ℝ) : |wgt b0 s' - wgt b0 s| ≤ |s' - s| := by
  unfold wgt
  have h1 := abs_min_sub_min_le_max (1 : ℝ) (max 0 (b0 + 1 - s')) 1 (max 0 (b0 + 1 - s))
  have h2 := abs_max_sub_max_le_max (0 : ℝ) (b0 + 1 - s') 0 (b0 + 1 - s)
  have e1 : max |(1 : ℝ) - 1| |max 0 (b0 + 1 - s') - max 0 (b0 + 1 - s)| =
      |max 0 (b0 + 1 - s') - max 0 (b0 + 1 - s)| := by
    rw [sub_self, abs_zero]; exact max_eq_right (abs_nonneg _)
  have e2 : max |(0 : ℝ) - 0| |b0 + 1 - s' - (b0 + 1 - s)| = |s' - s| := by
    rw [sub_self, abs_zero, show b0 + 1 - s' - (b0 + 1 - s) = -(s' - s) by ring, abs_neg]
    exact max_eq_right (abs_nonneg _)
  rw [e1] at h1
  rw [e2] at h2
  exact h1.trans h2

theorem clipW_abs_le {y0 : ℝ} (hy0 : 0 ≤ y0) (y : ℝ) : |clipW y0 y| ≤ y0 := by
  unfold clipW
  rw [abs_le]
  constructor
  · exact le_max_left _ _
  · exact max_le (by linarith) (min_le_left _ _)

theorem clipW_lip (y0 y y' : ℝ) : |clipW y0 y' - clipW y0 y| ≤ |y' - y| := by
  unfold clipW
  have h1 := abs_max_sub_max_le_max (-y0) (min y0 y') (-y0) (min y0 y)
  have h2 := abs_min_sub_min_le_max y0 y' y0 y
  have e1 : max |-y0 - -y0| |min y0 y' - min y0 y| = |min y0 y' - min y0 y| := by
    rw [sub_self, abs_zero]; exact max_eq_right (abs_nonneg _)
  have e2 : max |y0 - y0| |y' - y| = |y' - y| := by
    rw [sub_self, abs_zero]; exact max_eq_right (abs_nonneg _)
  rw [e1] at h1
  rw [e2] at h2
  exact h1.trans h2

/-- **Lemma E2w**, the step of its proof that reads the two maps: the weighted observation is
`y0`-Lipschitz in `|ξ|²` and `1`-Lipschitz in `Y`. -/
theorem obsW_lip {y0 : ℝ} (hy0 : 0 ≤ y0) (b0 : ℝ) (ξ ξ' : Fin d → ℝ) (Y Y' : ℝ) :
    |obsW b0 y0 ξ' Y' - obsW b0 y0 ξ Y| ≤ y0 * |ξ' ⬝ᵥ ξ' - ξ ⬝ᵥ ξ| + |Y' - Y| := by
  unfold obsW
  set φ' := wgt b0 (ξ' ⬝ᵥ ξ')
  set φ := wgt b0 (ξ ⬝ᵥ ξ)
  have hφ := wgt_mem b0 (ξ ⬝ᵥ ξ)
  have e : φ' * clipW y0 Y' - φ * clipW y0 Y = (φ' - φ) * clipW y0 Y' + φ * (clipW y0 Y' - clipW y0 Y) := by ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul]
  have h1 : |φ' - φ| * |clipW y0 Y'| ≤ |ξ' ⬝ᵥ ξ' - ξ ⬝ᵥ ξ| * y0 :=
    mul_le_mul (wgt_lip b0 _ _) (clipW_abs_le hy0 Y') (abs_nonneg _) (abs_nonneg _)
  have h2 : |φ| * |clipW y0 Y' - clipW y0 Y| ≤ 1 * |Y' - Y| := by
    rw [abs_of_nonneg hφ.1]
    exact mul_le_mul hφ.2 (clipW_lip y0 Y Y') (abs_nonneg _) zero_le_one
  linarith

/-- **Lemma WR** (ii), (iii) and **Lemma SK'** (i) on the observation: `|Y^w| ≤
y0` and `|Y^w| ≤ |Y|`; the weight vanishes for `|ξ|² ≥ b0 + 1`; and `Y^w = Y` when `|ξ|² ≤ b0` and `|Y| ≤ y0`. -/
theorem obsW_sure {y0 : ℝ} (hy0 : 0 ≤ y0) (b0 : ℝ) (ξ : Fin d → ℝ) (Y : ℝ) :
    |obsW b0 y0 ξ Y| ≤ y0 ∧ |obsW b0 y0 ξ Y| ≤ |Y| ∧ (b0 + 1 ≤ ξ ⬝ᵥ ξ → obsW b0 y0 ξ Y = 0) ∧
      (ξ ⬝ᵥ ξ ≤ b0 → |Y| ≤ y0 → obsW b0 y0 ξ Y = Y) := by
  have hφ := wgt_mem b0 (ξ ⬝ᵥ ξ)
  have hc : |clipW y0 Y| ≤ |Y| := by
    have := clipW_lip y0 0 Y
    have h0 : clipW y0 0 = 0 := by
      unfold clipW; rw [min_eq_right hy0, max_eq_right (by linarith)]
    simpa [h0] using this
  refine ⟨?_, ?_, fun h => ?_, fun h hY => ?_⟩
  · unfold obsW
    rw [abs_mul, abs_of_nonneg hφ.1]
    exact (mul_le_mul hφ.2 (clipW_abs_le hy0 Y) (abs_nonneg _) zero_le_one).trans (by simp)
  · unfold obsW
    rw [abs_mul, abs_of_nonneg hφ.1]
    exact (mul_le_mul hφ.2 hc (abs_nonneg _) zero_le_one).trans (by simp)
  · unfold obsW wgt
    rw [max_eq_left (by linarith), min_eq_right zero_le_one, zero_mul]
  · unfold obsW wgt clipW
    rw [abs_le] at hY
    rw [max_eq_right (by linarith), min_eq_left (by linarith), min_eq_right hY.2, max_eq_right hY.1, one_mul]

/-! ## Group C: the arithmetic -/

/-- **Lemma thr at T4U**: the threshold is nonnegative; `δ_ref(δc) ≤ δ/2`; in the case, at every
`u` of the schedule's bracket, `B_n + 1 ≤` the threshold (`C_Λ ≥ 1.001 C_reg`); off it, `n ≤` the threshold (the
trivial range, cases (ii), (iii) and the sliver; `C_Λ ≥ 8 · 14500` since the case splits at `ε(u_δ) = 1/8`). -/
def ThrUW (C : ℝ) : Prop :=
  ∀ (d n : ℕ) (δ : ℚ), 1 ≤ d → 1 ≤ n → 0 < δ → δ < 1 →
    0 ≤ thrUW C d n δ ∧ deltaRefW n (deltaC d n (kDel δ)) ≤ (δ : ℝ) / 2 ∧
      (RunCaseUW d n δ → ∀ u : ℝ, uF d n (kDel δ) ≤ u → u ≤ uF d n (kDel δ + 1) →
        bRegW d n u (deltaC d n (kDel δ)) + 1 ≤ thrUW C d n δ) ∧
      (¬ RunCaseUW d n δ → (n : ℝ) ≤ thrUW C d n δ)

/-! ## What the assembly reads, and the bricks with their routes -/

/-- **The named hypotheses of the assembly of `TheoremUW`**: the program and its cost, the
schedule, the four W-hypotheses of SHADOW on `recUW`, (O1) and Step 2 for P° of Theorem UW, and Lemma thr. The
measurability of the regret is Theorem U's `regMeasU`. -/
structure AsmUW (I : ImplW) (C : ℝ) : Prop where
  mach : BLOMachOK I.P I.C' I.k
  link : BLOWLink I
  playInt : PlayIntUW I
  sched : SchedUW I
  pos : PosRecUW I
  meas : MeasRecUW I
  bits : BitsRecUW I
  engine : EngineRecUW I
  ref : RefPropUW
  coup : CoupStepPropUW
  thr : ThrUW C

/-- **Every brick of Theorem UW and the routes between them**, by group. Group A: `rows`, `sifacts`, the wrapper
(`condIncr`, `condBias`, `lemmaUSet`), `coup`, and its three routes (`detOf`: DET at T4U from the rows and sifacts;
`refRegOf`: W-DET from DET; `evProbOf`: the events from the rows, Lemma SK' and the wrapper). Group B: the program
(`mach`, `link`, `playInt`, `sched`), the record (`pos`, `meas`, `bits`), DOM-W (`dom`) and its route `engineOf`
(BUD-W, E2w, WR, errors-W and the tracking). Group C: `thr`. -/
structure AllUW (I : ImplW) (C : ℝ) : Prop where
  rows : RowsUW
  sifacts : SIFactsUW
  condIncr : CondIncrW
  condBias : CondBiasW
  lemmaUSet : LemmaUSetW
  coup : CoupStepPropUW
  detOf : RowsUW → SIFactsUW → DetUW
  refRegOf : DetUW → RefRegUW
  evProbOf : RowsUW → CondIncrW → CondBiasW → LemmaUSetW → EvProbUW
  mach : BLOMachOK I.P I.C' I.k
  link : BLOWLink I
  playInt : PlayIntUW I
  sched : SchedUW I
  pos : PosRecUW I
  meas : MeasRecUW I
  bits : BitsRecUW I
  dom : DomW
  engineOf : DomW → EngineRecUW I
  thr : ThrUW C

end AdversarialBco.UW
