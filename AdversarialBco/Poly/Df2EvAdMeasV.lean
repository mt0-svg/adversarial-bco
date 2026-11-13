/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.Df2SetEAdV
public import AdversarialBco.Poly.Df2EvAdMeas

@[expose] public section

/-!
# The epoch with an adapted parameter and an advice per round: the process

The context at `ω` is `ctxWV = df2CtxAtF d n δ (Kθ (θ 0 ω)) (fun s => apθ (ψ s ω))`, the path `pathWAd` of
Df2EvAdMeas.lean. Round `s` maps the mode through `roundOfV s ((θ s, ψ s), mode, ξ_s, e_s)`, which is `roundOf` at
the routine `apθ (ψ s)`; `Df2EpochMeasV` makes it measurable jointly in the advice (`measurable_roundOfV`), so the
mode before round `s ≤ m` is measurable in `𝒢 s` (`measurable_modeAdV`) since `ψ s` is measurable in `𝒢 (s + 1)`.
The state process `sigAdV s = (θ s, st_s)` and the identities of the increments (`Y_eqAdV`, `fF_sigAdV`,
`fP_sigAdV`, `ghat_dotAdV`, `shh_sqAdV`, `zSeq_eqAdV`) hold for every advice: no increment reads the routine.
-/

open MeasureTheory ProbabilityTheory
open Matrix
open scoped Matrix

namespace AdversarialBco.Poly

open ApMeas

namespace EvGY

variable {d : ℕ} (n : ℕ) (δ : ℝ) {m : ℕ} {Θ : Type} [MeasurableSpace Θ] {V : Type} [MeasurableSpace V]
  (Kθ : Θ → Set (E d)) (gθ : ℕ → Θ → E d → ℝ) (apθ : V → ApFun d)

/-- The round map of round `s` at the parameter and the advice. -/
noncomputable def roundOfV (s : ℕ) (x : (Θ × V) × Df2Mode d × (Fin d → ℝ) × ℝ) : Df2Mode d :=
  roundOf n δ Kθ gθ (apθ x.1.2) s (x.1.1, x.2)

theorem measurable_roundOfV (hmeas : Df2EpochMeasV (df2oPar d n δ) n m Kθ gθ apθ) {s : ℕ} (hs : s < m) :
    Measurable (roundOfV n δ Kθ gθ apθ s) := by
  have heq : roundOfV n δ Kθ gθ apθ s = fun x =>
      if x.2.1.code.1 = 0 then .off else if x.2.1.code.1 = 1 then .guard else
        df2NextAP (apθ x.1.2) (df2oPar d n δ) n (df2KepsOf (Kθ x.1.1) (df2oPar d n δ).eps) x.2.1.code.2 x.2.2.1
          (x.2.1.code.2.A *ᵥ x.2.2.1) (yOf n δ Kθ gθ s x.1.1 x.2.1.code.2 x.2.2.1 x.2.2.2) :=
    funext fun x => roundOf_eq n δ Kθ gθ (apθ x.1.2) s (x.1.1, x.2)
  rw [heq]
  have hcode : Measurable fun x : (Θ × V) × Df2Mode d × (Fin d → ℝ) × ℝ => x.2.1.code :=
    measurable_mode_code.comp (measurable_fst.comp measurable_snd)
  have htag : Measurable fun x : (Θ × V) × Df2Mode d × (Fin d → ℝ) × ℝ => x.2.1.code.1 :=
    measurable_fst.comp hcode
  have hst : Measurable fun x : (Θ × V) × Df2Mode d × (Fin d → ℝ) × ℝ => x.2.1.code.2 :=
    measurable_snd.comp hcode
  have hξ : Measurable fun x : (Θ × V) × Df2Mode d × (Fin d → ℝ) × ℝ => x.2.2.1 :=
    measurable_fst.comp (measurable_snd.comp measurable_snd)
  have he : Measurable fun x : (Θ × V) × Df2Mode d × (Fin d → ℝ) × ℝ => x.2.2.2 :=
    measurable_snd.comp (measurable_snd.comp measurable_snd)
  have hq : Measurable fun x : (Θ × V) × Df2Mode d × (Fin d → ℝ) × ℝ => x.1.1 :=
    measurable_fst.comp measurable_fst
  have hin1 : Measurable fun x : (Θ × V) × Df2Mode d × (Fin d → ℝ) × ℝ =>
      (x.1.1, x.2.1.code.2, x.2.2.1, x.2.2.2) :=
    hq.prodMk (hst.prodMk (hξ.prodMk he))
  have hY : Measurable fun x : (Θ × V) × Df2Mode d × (Fin d → ℝ) × ℝ =>
      yOf n δ Kθ gθ s x.1.1 x.2.1.code.2 x.2.2.1 x.2.2.2 := by
    have h := (measurable_yOf n δ Kθ gθ apNone hmeas.none hs).comp hin1
    exact h
  have hin2 : Measurable fun x : (Θ × V) × Df2Mode d × (Fin d → ℝ) × ℝ =>
      (x.1, x.2.1.code.2, x.2.2.1, yOf n δ Kθ gθ s x.1.1 x.2.1.code.2 x.2.2.1 x.2.2.2) :=
    measurable_fst.prodMk (hst.prodMk (hξ.prodMk hY))
  have hN := hmeas.2.2.comp hin2
  have h := measurable_ite_code htag hN
  exact h

variable {Ω : Type} {m0 : MeasurableSpace Ω}

/-- The context of the epoch at `ω`: the body at `θ 0 ω`, the routine `apθ (ψ s ω)` in round `s`. -/
noncomputable def ctxWV (θ0 : Ω → Θ) (ψ : ℕ → Ω → V) (ω : Ω) : Df2Ctx d :=
  df2CtxAtF d n δ (Kθ (θ0 ω)) fun s => apθ (ψ s ω)

end EvGY

namespace EvAd

open EvGY Layer2

variable {d : ℕ} (n : ℕ) (δ : ℝ) {m : ℕ} {Θ : Type} [MeasurableSpace Θ] {V : Type} [MeasurableSpace V]
  (Kθ : Θ → Set (E d)) (gθ : ℕ → Θ → E d → ℝ) (apθ : V → ApFun d)

variable {Ω : Type} {m0 : MeasurableSpace Ω}

omit [MeasurableSpace Θ] [MeasurableSpace V] in
theorem mode_succ_eqAdV (θ : ℕ → Ω → Θ) (ψ : ℕ → Ω → V) (hK : ∀ s ω, Kθ (θ s ω) = Kθ (θ 0 ω))
    (ξ : ℕ → Ω → Fin d → ℝ) (e : ℕ → Ω → ℝ) (ω : Ω) (s : ℕ) :
    (ctxWV n δ Kθ apθ (θ 0) ψ ω).mode (pathWAd gθ θ ξ e ω) (s + 1) =
      roundOfV n δ Kθ gθ apθ s ((θ s ω, ψ s ω), (ctxWV n δ Kθ apθ (θ 0) ψ ω).mode (pathWAd gθ θ ξ e ω) s,
        ξ s ω, e s ω) := by
  show (df2RoundE (df2CtxAtF d n δ (Kθ (θ 0 ω)) fun s => apθ (ψ s ω)) (apθ (ψ s ω)) _ _ _ _).2 =
    (df2RoundE (df2CtxAt d n δ (Kθ (θ s ω)) (apθ (ψ s ω))) (apθ (ψ s ω)) _ _ _ _).2
  rw [hK s ω]
  rfl

/-- The mode before round `s ≤ m` is measurable in `𝒢 s`, adapted parameter, advice per round. -/
theorem measurable_modeAdV (hmeas : Df2EpochMeasV (df2oPar d n δ) n m Kθ gθ apθ) (𝒢 : Filtration ℕ m0)
    (θ : ℕ → Ω → Θ) (ψ : ℕ → Ω → V)
    (hK : ∀ s ω, Kθ (θ s ω) = Kθ (θ 0 ω)) (ξ : ℕ → Ω → Fin d → ℝ) (e : ℕ → Ω → ℝ)
    (hθ : ∀ s, Measurable[𝒢 s] (θ s)) (hψ : ∀ s, Measurable[𝒢 (s + 1)] (ψ s))
    (hξ : ∀ s, Measurable[𝒢 (s + 1)] (ξ s)) (he : ∀ s, Measurable[𝒢 (s + 1)] (e s)) :
    ∀ s ≤ m, Measurable[𝒢 s] fun ω => (ctxWV n δ Kθ apθ (θ 0) ψ ω).mode (pathWAd gθ θ ξ e ω) s := by
  intro s hs
  induction s with
  | zero => exact (measurable_const : Measurable[𝒢 0] fun _ : Ω => Df2Mode.run (df2Init (df2oPar d n δ) d))
  | succ s ih =>
    have hθ' : Measurable[𝒢 (s + 1)] (θ s) := (hθ s).mono (𝒢.mono (Nat.le_succ s)) le_rfl
    have hm' : Measurable[𝒢 (s + 1)] fun ω => (ctxWV n δ Kθ apθ (θ 0) ψ ω).mode (pathWAd gθ θ ξ e ω) s :=
      (ih (by omega)).mono (𝒢.mono (Nat.le_succ s)) le_rfl
    have htup : Measurable[𝒢 (s + 1)] fun ω =>
        ((θ s ω, ψ s ω), (ctxWV n δ Kθ apθ (θ 0) ψ ω).mode (pathWAd gθ θ ξ e ω) s, ξ s ω, e s ω) :=
      (hθ'.prodMk (hψ s)).prodMk (hm'.prodMk ((hξ s).prodMk (he s)))
    have h := (measurable_roundOfV n δ Kθ gθ apθ (m := m) (s := s) hmeas (by omega)).comp htup
    simp only [Function.comp_def] at h
    simpa only [mode_succ_eqAdV n δ Kθ gθ apθ θ ψ hK ξ e] using h

/-- The state before round `s ≤ m` is measurable in `𝒢 s`. -/
theorem measurable_stAdV (hmeas : Df2EpochMeasV (df2oPar d n δ) n m Kθ gθ apθ) (𝒢 : Filtration ℕ m0)
    (θ : ℕ → Ω → Θ) (ψ : ℕ → Ω → V)
    (hK : ∀ s ω, Kθ (θ s ω) = Kθ (θ 0 ω)) (ξ : ℕ → Ω → Fin d → ℝ) (e : ℕ → Ω → ℝ)
    (hθ : ∀ s, Measurable[𝒢 s] (θ s)) (hψ : ∀ s, Measurable[𝒢 (s + 1)] (ψ s))
    (hξ : ∀ s, Measurable[𝒢 (s + 1)] (ξ s)) (he : ∀ s, Measurable[𝒢 (s + 1)] (e s)) {s : ℕ} (hs : s ≤ m) :
    Measurable[𝒢 s] fun ω => (ctxWV n δ Kθ apθ (θ 0) ψ ω).st (pathWAd gθ θ ξ e ω) s :=
  (EvSI.measurable_stOr (df2Init (df2oPar d n δ) d)).comp
    (measurable_modeAdV n δ Kθ gθ apθ hmeas 𝒢 θ ψ hK ξ e hθ hψ hξ he s hs)

/-! ## The state process of LQ, S-DF and DQ -/

/-- The state process of the increments of LQ, S-DF and DQ, `sigAdV s = (θ s, st_s)`. -/
noncomputable def sigAdV (θ : ℕ → Ω → Θ) (ψ : ℕ → Ω → V) (ξ : ℕ → Ω → Fin d → ℝ) (e : ℕ → Ω → ℝ) (s : ℕ)
    (ω : Ω) : Θ × Df2St d :=
  (θ s ω, (ctxWV n δ Kθ apθ (θ 0) ψ ω).st (pathWAd gθ θ ξ e ω) s)

theorem measurable_sigAdV (hmeas : Df2EpochMeasV (df2oPar d n δ) n m Kθ gθ apθ) (𝒢 : Filtration ℕ m0)
    (θ : ℕ → Ω → Θ) (ψ : ℕ → Ω → V)
    (hK : ∀ s ω, Kθ (θ s ω) = Kθ (θ 0 ω)) (ξ : ℕ → Ω → Fin d → ℝ) (e : ℕ → Ω → ℝ)
    (hθ : ∀ s, Measurable[𝒢 s] (θ s)) (hψ : ∀ s, Measurable[𝒢 (s + 1)] (ψ s))
    (hξ : ∀ s, Measurable[𝒢 (s + 1)] (ξ s)) (he : ∀ s, Measurable[𝒢 (s + 1)] (e s)) {s : ℕ} (hs : s ≤ m) :
    Measurable[𝒢 s] (sigAdV n δ Kθ gθ apθ θ ψ ξ e s) :=
  (hθ s).prodMk (measurable_stAdV n δ Kθ gθ apθ hmeas 𝒢 θ ψ hK ξ e hθ hψ hξ he hs)

section path

variable (θ : ℕ → Ω → Θ) (ψ : ℕ → Ω → V) (ξ : ℕ → Ω → Fin d → ℝ) (e : ℕ → Ω → ℝ) (ω : Ω) (s : ℕ)

omit [MeasurableSpace Θ] [MeasurableSpace V]

/-- `Y_s` as a function of `sigAdV s` and the draw and noise of round `s`. -/
theorem Y_eqAdV (hK : ∀ s ω, Kθ (θ s ω) = Kθ (θ 0 ω)) :
    (ctxWV n δ Kθ apθ (θ 0) ψ ω).Y (pathWAd gθ θ ξ e ω) s =
      EvSI.fF n δ Kθ gθ s (sigAdV n δ Kθ gθ apθ θ ψ ξ e s ω, ξ s ω) +
        EvSI.fP n δ Kθ (sigAdV n δ Kθ gθ apθ θ ψ ξ e s ω, ξ s ω) * e s ω := by
  simp only [Df2Ctx.Y, Df2Ctx.pip, Df2Ctx.play, Df2Ctx.X, Df2Ctx.w, EvSI.fF, EvSI.fP, sigAdV, xOf, df2Ext, ctxWV,
    pathWAd, df2CtxAtF, WithLp.toLp_smul, hK s ω]
  ring

/-- The extension coefficient of round `s` on the state process is the extension of the context. -/
theorem fF_sigAdV (hK : ∀ s ω, Kθ (θ s ω) = Kθ (θ 0 ω)) (z : Fin d → ℝ) :
    EvSI.fF n δ Kθ gθ s (sigAdV n δ Kθ gθ apθ θ ψ ξ e s ω, z) =
      EvSI.eR n δ (Kθ (θ 0 ω)) (gθ s (θ s ω)) (sigAdV n δ Kθ gθ apθ θ ψ ξ e s ω).2 z := by
  simp only [EvSI.fF, EvSI.eR, sigAdV, hK s ω]

/-- The gauge coefficient of round `s` on the state process is the gauge factor of the context. -/
theorem fP_sigAdV (hK : ∀ s ω, Kθ (θ s ω) = Kθ (θ 0 ω)) (z : Fin d → ℝ) :
    EvSI.fP n δ Kθ (sigAdV n δ Kθ gθ apθ θ ψ ξ e s ω, z) =
      EvSI.pR n δ (Kθ (θ 0 ω)) (sigAdV n δ Kθ gθ apθ θ ψ ξ e s ω).2 z := by
  simp only [EvSI.fP, EvSI.pR, sigAdV, hK s ω]

theorem ghat_dotAdV (y : Fin d → ℝ) :
    (ctxWV n δ Kθ apθ (θ 0) ψ ω).ghat (pathWAd gθ θ ξ e ω) s ⬝ᵥ
        (y - ((ctxWV n δ Kθ apθ (θ 0) ψ ω).st (pathWAd gθ θ ξ e ω) s).mu) =
      (ctxWV n δ Kθ apθ (θ 0) ψ ω).Y (pathWAd gθ θ ξ e ω) s *
        EvSI.phiL n δ y (sigAdV n δ Kθ gθ apθ θ ψ ξ e s ω).2 (ξ s ω) := by
  simp only [Df2Ctx.ghat, Df2Ctx.u, Df2Ctx.w, EvSI.phiL, EvSI.lin, sigAdV, smul_dotProduct, smul_eq_mul, ctxWV,
    pathWAd, df2CtxAtF]
  ring

theorem shh_sqAdV (hf : Df2St d → Fin d → ℝ) :
    df2Sq ((ctxWV n δ Kθ apθ (θ 0) ψ ω).shh (pathWAd gθ θ ξ e ω) s)
        (hf ((ctxWV n δ Kθ apθ (θ 0) ψ ω).st (pathWAd gθ θ ξ e ω) s)) =
      (ctxWV n δ Kθ apθ (θ 0) ψ ω).Y (pathWAd gθ θ ξ e ω) s *
        EvSI.phiH n δ hf (sigAdV n δ Kθ gθ apθ θ ψ ξ e s ω).2 (ξ s ω) := by
  simp only [Df2Ctx.shh, sq_smul, sq_sub, EvSI.phiH, EvSI.lin, sigAdV, Df2Ctx.u, Df2Ctx.w, ctxWV, pathWAd,
    df2CtxAtF]
  have hv : ∀ (u v : Fin d → ℝ), df2Sq (vecMulVec u u) v = (u ⬝ᵥ v) ^ 2 := fun u v => by
    simp only [df2Sq, vecMulVec_mulVec]
    rw [op_smul_eq_smul, dotProduct_smul, smul_eq_mul, dotProduct_comm v u]; ring
  rw [hv]
  ring

/-- Under the bound condition, the increment of round `s < m` on the state process is `Y_s φ - ∫ e_s φ`. -/
theorem zSeq_eqAdV (hK : ∀ s ω, Kθ (θ s ω) = Kθ (θ 0 ω)) {ι : Type*} {m : ℕ} (M : ℝ)
    (φ : ι → Df2St d → (Fin d → ℝ) → ℝ) (c : ι) {s : ℕ} (hs : s < m)
    (hst : EvSI.stB M (sigAdV n δ Kθ gθ apθ θ ψ ξ e s ω).2) :
    EvSI.zSeq m (fun c s => EvSI.aOf n δ Kθ gθ M s (φ c)) (fun c _ => EvSI.bOf n δ Kθ M (φ c))
        (sigAdV n δ Kθ gθ apθ θ ψ ξ e) ξ e c s ω =
      (ctxWV n δ Kθ apθ (θ 0) ψ ω).Y (pathWAd gθ θ ξ e ω) s * φ c (sigAdV n δ Kθ gθ apθ θ ψ ξ e s ω).2 (ξ s ω) -
        ∫ z, EvSI.eR n δ (Kθ (θ 0 ω)) (gθ s (θ s ω)) (sigAdV n δ Kθ gθ apθ θ ψ ξ e s ω).2 z *
          φ c (sigAdV n δ Kθ gθ apθ θ ψ ξ e s ω).2 z ∂(EvSI.gam d) := by
  rw [EvSI.zSeq_of_lt _ _ _ _ _ _ hs]
  unfold EvSI.incr
  rw [EvSI.mean_aOf n δ Kθ gθ M s (φ c) _ hst, Y_eqAdV n δ Kθ gθ apθ θ ψ ξ e ω s hK]
  simp only [fF_sigAdV n δ Kθ gθ apθ θ ψ ξ e ω s hK]
  unfold EvSI.aOf EvSI.bOf
  simp only [hst, ↓reduceIte, fF_sigAdV n δ Kθ gθ apθ θ ψ ξ e ω s hK]
  ring

end path

end EvAd

end AdversarialBco.Poly
