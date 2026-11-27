/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.ShadowWEv
public import AdversarialBco.Bit.ShadowCoup

@[expose] public section

/-!
# The abstract coupled world

Proposition SHADOW and the reference analysis of the bit chain (Bit/ShadowIface.lean and the files after it) live on
the world `WΩ = (gs, noise)` under `gaussStream ⊗ ν` with the filtration `cσ d`. Here the same objects on any
probability space `Ω` with a world map `w : Ω → WΩ` and an abstract filtration `𝓕` (`CWorld`), which may hold more
than the stream and the noise: the losses of an environment of `TheoremUnified` and its other randomness.

* `CWorld`, `WorldLawOK`: the world and its law clauses: the terms of the stream known before round `t` and the
  noises of the rounds `< t` are `𝓕 t`-measurable; the stream has the law `gaussStream`; (W1) the draw of round `t`
  is independent of `𝓕 t`, the coupling coordinates of round `t` of `F*_t = 𝓕 t ∨ σ(draw group, noise of round t)`;
  (W2) the noise of round `t` has conditional mean `0` and conditional `E exp(ε²) ≤ 2` given
  `H_t = 𝓕 t ∨ σ(draw of round t)` (UNI-NOISE, (W1), (W2), on the filtration itself);
* `WorldLawOK.xi_law`, `WorldLawOK.z_law`: the laws of the draw and of the coupling coordinates;
* `LossProcW`, `RunW`: `Df2LossProcF` and `Run` with `Ω` in place of `WΩ`; the definitions of `Run` (the mode, the
  plays, the noise, the virtual epochs, the events of P°) read the world through `w`;
* `PosHypW`, `BLMeasW`, `BitsHypW`, `EngineHypW`, `ShadowPropW`, `RefPropW`, `CoupStepPropW`: the hypotheses and the
  statements of Bit/ShadowIface.lean on `CWorld`.
-/

open MeasureTheory ProbabilityTheory

namespace AdversarialBco.Unified.World

open AdversarialBco.RealRAM AdversarialBco.Poly AdversarialBco.Poly.Layer2 AdversarialBco.Bit.Cpl
open AdversarialBco.Poly.Conj1 (fL)

variable {d : ℕ}

/-! ## The abstract coupled world -/

/-- An abstract coupled world: a measure `μ` on `Ω`, the world map `w ω = (gs, noise)`, and a filtration `𝓕`. -/
structure CWorld (d : ℕ) (Ω : Type) [m0 : MeasurableSpace Ω] where
  /-- The measure. -/
  μ : Measure Ω
  /-- The Gaussian stream and the noise at `ω`. -/
  w : Ω → WΩ
  /-- The filtration: what is known before round `t`. -/
  𝓕 : Filtration ℕ m0

namespace CWorld

variable {Ω : Type} [m0 : MeasurableSpace Ω] (W : CWorld d Ω)

/-- The Gaussian stream. -/
def gs (ω : Ω) : ℕ → ℝ := (W.w ω).1

/-- The noise of round `t`. -/
def nz (t : ℕ) (ω : Ω) : ℝ := (W.w ω).2 t

/-- The draw of round `t`. -/
def xi (t : ℕ) (ω : Ω) : Fin d → ℝ := ξc d t (W.w ω)

/-- The draw group of round `t`. -/
def xg (t : ℕ) (ω : Ω) : Fin (d + 1) → ℝ := ξg d t (W.w ω)

/-- The coupling coordinates of round `t`. -/
def zz (t : ℕ) (ω : Ω) : Fin 3 → ℝ := zc d t (W.w ω)

/-- `F*_t`: the filtration before round `t`, the draw group and the noise of round `t`. -/
abbrev Fσ (t : ℕ) : MeasurableSpace Ω :=
  W.𝓕 t ⊔ MeasurableSpace.comap (W.xg t) inferInstance ⊔ MeasurableSpace.comap (W.nz t) inferInstance

/-- `H_t` of (E3): the filtration before round `t` and the draw of round `t`. -/
abbrev HC (t : ℕ) : MeasurableSpace Ω := W.𝓕 t ⊔ MeasurableSpace.comap (W.xi t) inferInstance

end CWorld

/-- The law clauses of an abstract coupled world. -/
structure WorldLawOK {Ω : Type} [MeasurableSpace Ω] (W : CWorld d Ω) : Prop where
  /-- The measure is a probability measure. -/
  prob : IsProbabilityMeasure W.μ
  /-- The world map is measurable. -/
  w_meas : Measurable W.w
  /-- The terms of the stream known before round `t` are known before round `t`. -/
  g_adapt : ∀ t, ∀ i ∈ idxC d t, Measurable[W.𝓕 t] fun ω => W.gs ω i
  /-- The noises of the rounds `< t` are known before round `t`. -/
  e_adapt : ∀ t s, s < t → Measurable[W.𝓕 t] (W.nz s)
  /-- The stream is a Gaussian stream. -/
  g_law : W.μ.map W.gs = gaussStream
  /-- (W1) The draw of round `t` is independent of the past. -/
  xi_indep : ∀ t, Indep (MeasurableSpace.comap (W.xi t) inferInstance) (W.𝓕 t) W.μ
  /-- (W1) The coupling coordinates of round `t` are independent of `F*_t`. -/
  z_indep : ∀ t, Indep (MeasurableSpace.comap (W.zz t) inferInstance) (W.Fσ t) W.μ
  /-- (W2) `exp (ε_t²)` is integrable. -/
  e_int : ∀ t, Integrable (fun ω => Real.exp (W.nz t ω ^ 2)) W.μ
  /-- (W2) The noise of round `t` is centred given `H_t`. -/
  e_mean : ∀ t, W.μ[W.nz t | W.HC t] =ᵐ[W.μ] 0
  /-- (W2) Given `H_t`, the conditional expectation of `exp (ε_t²)` is at most `2`. -/
  e_exp : ∀ t, W.μ[fun ω => Real.exp (W.nz t ω ^ 2) | W.HC t] ≤ᵐ[W.μ] fun _ => 2

namespace WorldLawOK

variable {Ω : Type} [MeasurableSpace Ω] {W : CWorld d Ω}

theorem gs_meas (h : WorldLawOK W) : Measurable W.gs := measurable_fst.comp h.w_meas

/-- The law of the draw follows from the law of the stream. -/
theorem xi_law (h : WorldLawOK W) (t : ℕ) : W.μ.map (W.xi t) = gaussK d := by
  have hx : W.xi t = (fun x : ℕ → ℝ => fun c : Fin d => x (cIdx d t c)) ∘ W.gs := rfl
  rw [hx, ← Measure.map_map (by fun_prop) h.gs_meas, h.g_law, gaussStream,
    infinitePi_comp_inj _ _ (xiIdx_inj t), Measure.infinitePi_eq_pi]

/-- The law of the coupling coordinates follows from the law of the stream. -/
theorem z_law (h : WorldLawOK W) (t : ℕ) : W.μ.map (W.zz t) = gaussK 3 := by
  have hx : W.zz t = (fun x : ℕ → ℝ => fun k : Fin 3 => x (zIdx d t k)) ∘ W.gs := by
    funext ω k
    show zc d t (W.w ω) k = W.gs ω (zIdx d t k)
    rw [zc_eq]; rfl
  rw [hx, ← Measure.map_map (by fun_prop) h.gs_meas, h.g_law, gaussStream,
    infinitePi_comp_inj _ _ (zIdx_inj t), Measure.infinitePi_eq_pi]

end WorldLawOK

/-! ## The losses and the run record on an abstract world -/

/-- A loss process adapted to a filtration of an abstract space (`Df2LossProcF` with `Ω` in place of `WΩ`). -/
structure LossProcW (d n : ℕ) (K : Set (E d)) {Ω : Type} [m0 : MeasurableSpace Ω] (𝒢 : Filtration ℕ m0) where
  /-- The parameter space of the losses. -/
  Λ : Type
  /-- Its sigma-field. -/
  [mΛ : MeasurableSpace Λ]
  /-- The loss of round `t` at the parameter `l`. -/
  L : ℕ → Λ → E d → ℝ
  /-- The parameter of round `t` on `ω`. -/
  lam : ℕ → Ω → Λ
  /-- Every loss of the rounds `t < n` is admissible. -/
  adm : ∀ t < n, ∀ l, AdmLoss K (L t l)
  /-- At each point of the interior of `K`, the loss of a round `t < n` is measurable in the parameter. -/
  meas : ∀ t < n, ∀ y ∈ interior K, Measurable fun l => L t l y
  /-- The parameter of a round `t < n` is known before round `t`. -/
  lam_meas : ∀ t < n, Measurable[𝒢 t] (lam t)

attribute [instance] LossProcW.mΛ

/-- `lamAt` of Conj1/WorldVEAd.lean on an abstract space. -/
noncomputable def lamAtW {Ω Λ : Type} (n : ℕ) (lam : ℕ → Ω → Λ) (a s : ℕ) (ω : Ω) : Λ :=
  if a + s < n then lam (a + s) ω else lam a ω

/-- `Run` of Bit/ShadowIface.lean on an abstract coupled world. -/
structure RunW (d n : ℕ) (K : Set (E d)) {Ω : Type} [MeasurableSpace Ω] (W : CWorld d Ω) where
  /-- The losses, chosen against BL. -/
  F : LossProcW d n K W.𝓕
  /-- BL's position. -/
  pos : Ω → PgSp d
  /-- The shift of round `t` at P°'s mode before round `t`. -/
  sh : ℕ → Ω → Df2Mode d → ℝ × ℝ
  /-- The advice of round `t` at P°'s mode before round `t`. -/
  adv : ℕ → Ω → Df2Mode d → Adv d
  /-- BL's play of round `t`. -/
  play : ℕ → Ω → E d
  /-- BL's soundness event. -/
  bits : Set Ω
  /-- The coupling. -/
  Coup : ℝ → ℝ → (Fin 3 → ℝ) → ℝ

namespace RunW

variable {n : ℕ} {K : Set (E d)} {Ω : Type} [MeasurableSpace Ω] {W : CWorld d Ω}

/-- The losses on `ω`. -/
def loss (B : RunW d n K W) (ω : Ω) : ℕ → E d → ℝ := fun t => B.F.L t (B.F.lam t ω)

open Classical in
/-- The loss that P°'s round `t` reads: the loss on the interior of `K` for `t < n`, `0` past the horizon. -/
noncomputable def lossR (B : RunW d n K W) (t : ℕ) (ω : Ω) : E d → ℝ :=
  if t < n then fL K B.F.L t (B.F.lam t ω) else 0

/-- The coupled dither of round `t` at P°'s mode `m` before round `t`. -/
noncomputable def zeta (B : RunW d n K W) (t : ℕ) (ω : Ω) (m : Df2Mode d) : ℝ :=
  B.Coup (B.sh t ω m).1 (B.sh t ω m).2 (W.zz t ω)

/-- The mode of P° before round `t`. -/
noncomputable def mode (B : RunW d n K W) (δ : ℝ) : ℕ → Ω → Df2Mode d
  | 0, _ => .run (df2Init (df2oPar d n δ) d)
  | t + 1, ω => (cRoundA n δ K (B.pos ω) (apAdv (B.adv t ω (mode B δ t ω))) (B.lossR t ω) (W.nz t ω)
      (W.xi t ω) (B.zeta t ω (mode B δ t ω)) (mode B δ t ω)).2

/-- The play of P° in round `t`. -/
noncomputable def refPlay (B : RunW d n K W) (δ : ℝ) (t : ℕ) (ω : Ω) : E d :=
  (cRoundA n δ K (B.pos ω) (apAdv (B.adv t ω (B.mode δ t ω))) (B.lossR t ω) (W.nz t ω) (W.xi t ω)
    (B.zeta t ω (B.mode δ t ω)) (B.mode δ t ω)).1

/-- The noise of P°'s path in round `t`: `(ε_t + ζ*_t)/2`. -/
noncomputable def eRef (B : RunW d n K W) (δ : ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  (W.nz t ω + B.zeta t ω (B.mode δ t ω)) / 2

/-- The context of P°'s virtual epoch started before round `a`. -/
noncomputable def ctx (B : RunW d n K W) (δ : ℝ) (a : ℕ) (ω : Ω) : Df2Ctx d :=
  df2CtxAtF d n δ (kTh n δ K (B.pos ω)) fun s => apAdv (B.adv (a + s) ω (B.mode δ (a + s) ω))

/-- The path of P°'s virtual epoch started before round `a`. -/
noncomputable def path (B : RunW d n K W) (δ : ℝ) (a : ℕ) (ω : Ω) : Df2Path d :=
  ⟨fun s => gTh n δ K (fun t => B.F.L t (lamAtW n B.F.lam a s ω)) a s (B.pos ω), fun s => B.eRef δ (a + s) ω,
    fun s => W.xi (a + s) ω⟩

/-- The case of the analysis: BL's position is good. -/
def Case (B : RunW d n K W) (δ : ℝ) (ω : Ω) : Prop := PgGood d K (df2oPar d n δ).R (some (B.pos ω))

/-- The mean loss of round `t` of P° given the past. -/
noncomputable def mean (B : RunW d n K W) (δ : ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  ∫ z, B.loss ω t ((cRoundA n δ K (B.pos ω) apCall (B.lossR t ω) 0 z 0 (B.mode δ t ω)).1) ∂gaussK d

/-- The Azuma event of P°. -/
def Az (B : RunW d n K W) (δ : ℝ) (ω : Ω) : Prop :=
  ∑ t ∈ Finset.range n, B.loss ω t (B.refPlay δ t ω) ≤
    ∑ t ∈ Finset.range n, B.mean δ t ω + Real.sqrt (2 * n * Real.log (7 / (df2oPar d n δ).δe))

/-- `Ω_ref`: every virtual epoch of P° meets the five events of DET at its horizon, and the Azuma event holds. -/
def Good (B : RunW d n K W) (δ : ℝ) (ω : Ω) : Prop :=
  (∀ a < n, (B.ctx δ a ω).EvG (B.path δ a ω) (n - a) ∧ (B.ctx δ a ω).EvY (B.path δ a ω) (n - a) ∧
    (B.ctx δ a ω).EvLQ (B.path δ a ω) (n - a) ∧ (B.ctx δ a ω).EvSDF (B.path δ a ω) (n - a) ∧
    (B.ctx δ a ω).EvDQ (B.path δ a ω) (n - a)) ∧ B.Az δ ω

/-- The shift of round `t` on P°'s run. -/
noncomputable def shR (B : RunW d n K W) (δ : ℝ) (t : ℕ) (ω : Ω) : ℝ × ℝ := B.sh t ω (B.mode δ t ω)

/-- Round `t` decouples. -/
def D (B : RunW d n K W) (δ : ℝ) (t : ℕ) (ω : Ω) : Prop :=
  B.zeta t ω (B.mode δ t ω) ≠ (B.shR δ t ω).1 + (B.shR δ t ω).2 * W.zz t ω 0 / 2

end RunW

/-! ## The hypotheses -/

section Hyp

variable {n : ℕ} {K : Set (E d)} {Ω : Type} [MeasurableSpace Ω] {W : CWorld d Ω}

/-- (POS): BL's position is known before round 0 and good off an event of probability at most `δpos`. -/
structure PosHypW (B : RunW d n K W) (δ δpos : ℝ) : Prop where
  meas : Measurable[W.𝓕 0] B.pos
  bad : W.μ {ω | ¬ B.Case δ ω} ≤ ENNReal.ofReal δpos

/-- (O4-M): the shift of round `t` is measurable at `F*_t` jointly with the mode, the advice after round `t`. -/
structure BLMeasW (B : RunW d n K W) : Prop where
  sh : ∀ t, Measurable[(W.Fσ t).prod inferInstance] fun x : Ω × Df2Mode d => B.sh t x.1 x.2
  adv : ∀ t, Measurable[(W.𝓕 (t + 1)).prod inferInstance] fun x : Ω × Df2Mode d => B.adv t x.1 x.2

/-- (O4), the bit clause. -/
def BitsHypW (B : RunW d n K W) (δbits : ℝ) : Prop := W.μ B.bitsᶜ ≤ ENNReal.ofReal δbits

/-- Step 1 of SHADOW on the good events. -/
structure EngineHypW (B : RunW d n K W) (δ κ0 κ1 : ℝ) : Prop where
  shift : ∀ ω, B.Case δ ω → B.Good δ ω → ω ∈ B.bits → ∀ t < n, (∀ s < t, ¬ B.D δ s ω) →
    0 < (B.shR δ t ω).2 ∧ tvB (B.shR δ t ω).1 (B.shR δ t ω).2 ≤ κ0 + κ1 * |W.nz t ω|
  regret : ∀ ω, B.Case δ ω → B.Good δ ω → ω ∈ B.bits → (∀ s < n, ¬ B.D δ s ω) →
    ∑ t ∈ Finset.range n, B.loss ω t (B.play t ω) ≤ ∑ t ∈ Finset.range n, B.loss ω t (B.refPlay δ t ω) + 1

end Hyp

/-! ## The statements -/

/-- Proposition SHADOW on an abstract coupled world. -/
def ShadowPropW : Prop :=
  ∀ (d n : ℕ) (δ : ℝ) (K : Set (E d)) (Ω : Type) [MeasurableSpace Ω] (W : CWorld d Ω) (B : RunW d n K W)
    (δpos δbits κ0 κ1 : ℝ),
    Regime d n δ → IsClosed K → Convex ℝ K → WorldLawOK W → PosHypW B δ δpos → CoupLaw B.Coup → CoupTV B.Coup →
    BLMeasW B → BitsHypW B δbits → EngineHypW B δ κ0 κ1 → 0 ≤ δpos → 0 ≤ δbits → 0 ≤ κ0 → 0 ≤ κ1 →
      W.μ {ω | bReg d n δ + 1 < regretPts K (B.loss ω) (fun t => B.play t ω) n} ≤
        ENNReal.ofReal (δpos + deltaRef d n δ + δbits + n * (κ0 + κ1))

/-- (O1) on an abstract coupled world. -/
def RefPropW : Prop :=
  ∀ (d n : ℕ) (δ : ℝ) (K : Set (E d)) (Ω : Type) [MeasurableSpace Ω] (W : CWorld d Ω) (B : RunW d n K W),
    Regime d n δ → IsClosed K → Convex ℝ K → WorldLawOK W → Measurable[W.𝓕 0] B.pos → CoupLaw B.Coup →
    BLMeasW B →
      W.μ {ω | B.Case δ ω ∧ ¬ B.Good δ ω} ≤ ENNReal.ofReal (deltaRef d n δ) ∧
        ∀ ω, B.Case δ ω → B.Good δ ω → regretPts K (B.loss ω) (fun t => B.refPlay δ t ω) n ≤ bReg d n δ

/-- Step 2 of SHADOW on an abstract coupled world. -/
def CoupStepPropW : Prop :=
  ∀ (d n : ℕ) (δ : ℝ) (K : Set (E d)) (Ω : Type) [MeasurableSpace Ω] (W : CWorld d Ω) (B : RunW d n K W)
    (κ0 κ1 : ℝ),
    Regime d n δ → IsClosed K → Convex ℝ K → WorldLawOK W → Measurable[W.𝓕 0] B.pos → CoupLaw B.Coup →
    CoupTV B.Coup → BLMeasW B → 0 ≤ κ0 → 0 ≤ κ1 → ∀ t,
      W.μ {ω | B.D δ t ω ∧ 0 < (B.shR δ t ω).2 ∧ tvB (B.shR δ t ω).1 (B.shR δ t ω).2 ≤ κ0 + κ1 * |W.nz t ω|} ≤
        ENNReal.ofReal (κ0 + κ1)

end AdversarialBco.Unified.World
