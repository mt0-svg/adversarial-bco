/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.Df2SetEAd
public import AdversarialBco.Poly.Df2EvSIProc
public import AdversarialBco.Poly.Df2EvSIRound

@[expose] public section

/-!
# The epoch on setting (E) with an adapted parameter: the process

On an instance of `Df2OnSetEAd` the loss of round `s` is read at `θ s`, measurable in `𝒢 s`, and the body at `θ 0`
(`hK : ∀ s ω, Kθ (θ s ω) = Kθ (θ 0 ω)`). The round map of round `s` is `EvGY.roundOf` at the parameter `θ s`, so the
mode before round `s ≤ m` is measurable in `𝒢 s` (`measurable_modeAd`), and so is the state process
`sigAd s = (θ s, st_s)` that the increments of LQ, S-DF and DQ read (`measurable_sigAd`).

The frozen functions of Df2EvSIProc.lean read the body at the first slot, `θ s`; the context reads it at `θ 0`. The
identities that join them (`Y_eqAd`, `fF_sigAd`, `fP_sigAd`, `zSeq_eqAd`) rewrite with `hK` once.

`df2OnSetE_of_ad` gives the fixed setting from the adapted one (`θ s := θ`).
-/

open MeasureTheory ProbabilityTheory
open Matrix
open scoped Matrix

namespace AdversarialBco.Poly

/-- The fixed setting (E) is the case of a constant parameter. -/
theorem df2OnSetE_of_ad {k : ℝ} {Bad : (d : ℕ) → Df2Ctx d → Df2Path d → ℕ → Prop} (h : Df2OnSetEAd k Bad) :
    Df2OnSetE k Bad := by
  intro d n m δ hd hn hm1 hmn hδ0 hδ1 heps Θ _ Kθ gθ ap hbody hadm hap hmeas Ω m0 μ hμ 𝒢 θ ξ e hθ hE
  exact h d n m δ hd hn hm1 hmn hδ0 hδ1 heps Θ Kθ gθ ap hbody hadm hap hmeas Ω μ hμ 𝒢 (fun _ => θ) ξ e
    (fun s => hθ.mono (𝒢.mono (Nat.zero_le s)) le_rfl) (fun _ _ => rfl) hE

theorem df2EvGProp_of_ad (h : Df2EvGPropAd) : Df2EvGProp := df2OnSetE_of_ad h

theorem df2EvYProp_of_ad (h : Df2EvYPropAd) : Df2EvYProp := df2OnSetE_of_ad h

theorem df2EvLQProp_of_ad (h : Df2EvLQPropAd) : Df2EvLQProp := df2OnSetE_of_ad h

theorem df2EvSDFProp_of_ad (h : Df2EvSDFPropAd) : Df2EvSDFProp := df2OnSetE_of_ad h

theorem df2EvDQProp_of_ad (h : Df2EvDQPropAd) : Df2EvDQProp := df2OnSetE_of_ad h

theorem df2E1Loc_of_ad (h : Df2E1LocAd) : Df2E1Loc := df2OnSetE_of_ad h

namespace EvAd

open ApMeas EvGY Layer2

variable {d : ℕ} (n : ℕ) (δ : ℝ) {m : ℕ} {Θ : Type} [MeasurableSpace Θ] (Kθ : Θ → Set (E d))
  (gθ : ℕ → Θ → E d → ℝ) (ap : ApFun d)

variable {Ω : Type} {m0 : MeasurableSpace Ω}

/-- The path of the epoch at `ω`, the loss of round `s` read at the parameter of round `s`. -/
def pathWAd (θ : ℕ → Ω → Θ) (ξ : ℕ → Ω → Fin d → ℝ) (e : ℕ → Ω → ℝ) (ω : Ω) : Df2Path d :=
  ⟨fun s => gθ s (θ s ω), fun s => e s ω, fun s => ξ s ω⟩

omit [MeasurableSpace Θ] in
/-- The losses of the path are admissible on the body of the context. -/
theorem admAd (hadm : ∀ q, ∀ s < m, AdmLoss (Kθ q) (gθ s q)) (θ : ℕ → Ω → Θ)
    (hK : ∀ s ω, Kθ (θ s ω) = Kθ (θ 0 ω)) (ω : Ω) : ∀ s < m, AdmLoss (Kθ (θ 0 ω)) (gθ s (θ s ω)) :=
  fun s hs => hK s ω ▸ hadm (θ s ω) s hs

omit [MeasurableSpace Θ] in
theorem mode_succ_eqAd (θ : ℕ → Ω → Θ) (hK : ∀ s ω, Kθ (θ s ω) = Kθ (θ 0 ω)) (ξ : ℕ → Ω → Fin d → ℝ)
    (e : ℕ → Ω → ℝ) (ω : Ω) (s : ℕ) :
    (ctxW n δ Kθ ap (θ 0) ω).mode (pathWAd gθ θ ξ e ω) (s + 1) =
      roundOf n δ Kθ gθ ap s (θ s ω, (ctxW n δ Kθ ap (θ 0) ω).mode (pathWAd gθ θ ξ e ω) s, ξ s ω, e s ω) := by
  show (df2RoundE (df2CtxAt d n δ (Kθ (θ 0 ω)) ap) _ _ _ _).2 = (df2RoundE (df2CtxAt d n δ (Kθ (θ s ω)) ap) _ _ _ _).2
  rw [hK s ω]
  rfl

/-- The mode before round `s ≤ m` is measurable in `𝒢 s`, for an adapted parameter. -/
theorem measurable_modeAd (hmeas : Df2EpochMeas (df2oPar d n δ) n m Kθ gθ ap) (𝒢 : Filtration ℕ m0)
    (θ : ℕ → Ω → Θ) (hK : ∀ s ω, Kθ (θ s ω) = Kθ (θ 0 ω)) (ξ : ℕ → Ω → Fin d → ℝ) (e : ℕ → Ω → ℝ)
    (hθ : ∀ s, Measurable[𝒢 s] (θ s))
    (hξ : ∀ s, Measurable[𝒢 (s + 1)] (ξ s)) (he : ∀ s, Measurable[𝒢 (s + 1)] (e s)) :
    ∀ s ≤ m, Measurable[𝒢 s] fun ω => (ctxW n δ Kθ ap (θ 0) ω).mode (pathWAd gθ θ ξ e ω) s := by
  intro s hs
  induction s with
  | zero => exact (measurable_const : Measurable[𝒢 0] fun _ : Ω => Df2Mode.run (df2Init (df2oPar d n δ) d))
  | succ s ih =>
    have hθ' : Measurable[𝒢 (s + 1)] (θ s) := (hθ s).mono (𝒢.mono (Nat.le_succ s)) le_rfl
    have hm' : Measurable[𝒢 (s + 1)] fun ω => (ctxW n δ Kθ ap (θ 0) ω).mode (pathWAd gθ θ ξ e ω) s :=
      (ih (by omega)).mono (𝒢.mono (Nat.le_succ s)) le_rfl
    have htup : Measurable[𝒢 (s + 1)] fun ω =>
        (θ s ω, (ctxW n δ Kθ ap (θ 0) ω).mode (pathWAd gθ θ ξ e ω) s, ξ s ω, e s ω) :=
      hθ'.prodMk (hm'.prodMk ((hξ s).prodMk (he s)))
    have h := (measurable_roundOf n δ Kθ gθ ap (m := m) (s := s) hmeas (by omega)).comp htup
    simp only [Function.comp_def] at h
    simpa only [mode_succ_eqAd n δ Kθ gθ ap θ hK ξ e] using h

/-- The state before round `s ≤ m` is measurable in `𝒢 s`. -/
theorem measurable_stAd (hmeas : Df2EpochMeas (df2oPar d n δ) n m Kθ gθ ap) (𝒢 : Filtration ℕ m0)
    (θ : ℕ → Ω → Θ) (hK : ∀ s ω, Kθ (θ s ω) = Kθ (θ 0 ω)) (ξ : ℕ → Ω → Fin d → ℝ) (e : ℕ → Ω → ℝ)
    (hθ : ∀ s, Measurable[𝒢 s] (θ s))
    (hξ : ∀ s, Measurable[𝒢 (s + 1)] (ξ s)) (he : ∀ s, Measurable[𝒢 (s + 1)] (e s)) {s : ℕ} (hs : s ≤ m) :
    Measurable[𝒢 s] fun ω => (ctxW n δ Kθ ap (θ 0) ω).st (pathWAd gθ θ ξ e ω) s :=
  (EvSI.measurable_stOr (df2Init (df2oPar d n δ) d)).comp
    (measurable_modeAd n δ Kθ gθ ap hmeas 𝒢 θ hK ξ e hθ hξ he s hs)

/-! ## The state process of LQ, S-DF and DQ -/

/-- The state process of the increments of LQ, S-DF and DQ, `sigAd s = (θ s, st_s)`. -/
noncomputable def sigAd (θ : ℕ → Ω → Θ) (ξ : ℕ → Ω → Fin d → ℝ) (e : ℕ → Ω → ℝ) (s : ℕ) (ω : Ω) :
    Θ × Df2St d :=
  (θ s ω, (ctxW n δ Kθ ap (θ 0) ω).st (pathWAd gθ θ ξ e ω) s)

theorem measurable_sigAd (hmeas : Df2EpochMeas (df2oPar d n δ) n m Kθ gθ ap) (𝒢 : Filtration ℕ m0)
    (θ : ℕ → Ω → Θ) (hK : ∀ s ω, Kθ (θ s ω) = Kθ (θ 0 ω)) (ξ : ℕ → Ω → Fin d → ℝ) (e : ℕ → Ω → ℝ)
    (hθ : ∀ s, Measurable[𝒢 s] (θ s))
    (hξ : ∀ s, Measurable[𝒢 (s + 1)] (ξ s)) (he : ∀ s, Measurable[𝒢 (s + 1)] (e s)) {s : ℕ} (hs : s ≤ m) :
    Measurable[𝒢 s] (sigAd n δ Kθ gθ ap θ ξ e s) :=
  (hθ s).prodMk (measurable_stAd n δ Kθ gθ ap hmeas 𝒢 θ hK ξ e hθ hξ he hs)

section path

variable (θ : ℕ → Ω → Θ) (ξ : ℕ → Ω → Fin d → ℝ) (e : ℕ → Ω → ℝ) (ω : Ω) (s : ℕ)

omit [MeasurableSpace Θ]

/-- `Y_s` as a function of `sigAd s` and the draw and noise of round `s`. -/
theorem Y_eqAd (hK : ∀ s ω, Kθ (θ s ω) = Kθ (θ 0 ω)) :
    (ctxW n δ Kθ ap (θ 0) ω).Y (pathWAd gθ θ ξ e ω) s =
      EvSI.fF n δ Kθ gθ s (sigAd n δ Kθ gθ ap θ ξ e s ω, ξ s ω) +
        EvSI.fP n δ Kθ (sigAd n δ Kθ gθ ap θ ξ e s ω, ξ s ω) * e s ω := by
  simp only [Df2Ctx.Y, Df2Ctx.pip, Df2Ctx.play, Df2Ctx.X, Df2Ctx.w, EvSI.fF, EvSI.fP, sigAd, xOf, df2Ext, ctxW,
    pathWAd, df2CtxAt, WithLp.toLp_smul, hK s ω]
  ring

/-- The extension coefficient of round `s` on the state process is the extension of the context. -/
theorem fF_sigAd (hK : ∀ s ω, Kθ (θ s ω) = Kθ (θ 0 ω)) (z : Fin d → ℝ) :
    EvSI.fF n δ Kθ gθ s (sigAd n δ Kθ gθ ap θ ξ e s ω, z) =
      EvSI.eR n δ (Kθ (θ 0 ω)) (gθ s (θ s ω)) (sigAd n δ Kθ gθ ap θ ξ e s ω).2 z := by
  simp only [EvSI.fF, EvSI.eR, sigAd, hK s ω]

/-- The gauge coefficient of round `s` on the state process is the gauge factor of the context. -/
theorem fP_sigAd (hK : ∀ s ω, Kθ (θ s ω) = Kθ (θ 0 ω)) (z : Fin d → ℝ) :
    EvSI.fP n δ Kθ (sigAd n δ Kθ gθ ap θ ξ e s ω, z) =
      EvSI.pR n δ (Kθ (θ 0 ω)) (sigAd n δ Kθ gθ ap θ ξ e s ω).2 z := by
  simp only [EvSI.fP, EvSI.pR, sigAd, hK s ω]

theorem ghat_dotAd (y : Fin d → ℝ) :
    (ctxW n δ Kθ ap (θ 0) ω).ghat (pathWAd gθ θ ξ e ω) s ⬝ᵥ
        (y - ((ctxW n δ Kθ ap (θ 0) ω).st (pathWAd gθ θ ξ e ω) s).mu) =
      (ctxW n δ Kθ ap (θ 0) ω).Y (pathWAd gθ θ ξ e ω) s *
        EvSI.phiL n δ y (sigAd n δ Kθ gθ ap θ ξ e s ω).2 (ξ s ω) := by
  simp only [Df2Ctx.ghat, Df2Ctx.u, Df2Ctx.w, EvSI.phiL, EvSI.lin, sigAd, smul_dotProduct, smul_eq_mul, ctxW,
    pathWAd, df2CtxAt]
  ring

theorem shh_sqAd (hf : Df2St d → Fin d → ℝ) :
    df2Sq ((ctxW n δ Kθ ap (θ 0) ω).shh (pathWAd gθ θ ξ e ω) s)
        (hf ((ctxW n δ Kθ ap (θ 0) ω).st (pathWAd gθ θ ξ e ω) s)) =
      (ctxW n δ Kθ ap (θ 0) ω).Y (pathWAd gθ θ ξ e ω) s *
        EvSI.phiH n δ hf (sigAd n δ Kθ gθ ap θ ξ e s ω).2 (ξ s ω) := by
  simp only [Df2Ctx.shh, sq_smul, sq_sub, EvSI.phiH, EvSI.lin, sigAd, Df2Ctx.u, Df2Ctx.w, ctxW, pathWAd,
    df2CtxAt]
  have hv : ∀ (u v : Fin d → ℝ), df2Sq (vecMulVec u u) v = (u ⬝ᵥ v) ^ 2 := fun u v => by
    simp only [df2Sq, vecMulVec_mulVec]
    rw [op_smul_eq_smul, dotProduct_smul, smul_eq_mul, dotProduct_comm v u]; ring
  rw [hv]
  ring

/-- Under the bound condition, the increment of round `s < m` on the state process is `Y_s φ - ∫ e_s φ`. -/
theorem zSeq_eqAd (hK : ∀ s ω, Kθ (θ s ω) = Kθ (θ 0 ω)) {ι : Type*} {m : ℕ} (M : ℝ)
    (φ : ι → Df2St d → (Fin d → ℝ) → ℝ) (c : ι) {s : ℕ} (hs : s < m)
    (hst : EvSI.stB M (sigAd n δ Kθ gθ ap θ ξ e s ω).2) :
    EvSI.zSeq m (fun c s => EvSI.aOf n δ Kθ gθ M s (φ c)) (fun c _ => EvSI.bOf n δ Kθ M (φ c))
        (sigAd n δ Kθ gθ ap θ ξ e) ξ e c s ω =
      (ctxW n δ Kθ ap (θ 0) ω).Y (pathWAd gθ θ ξ e ω) s * φ c (sigAd n δ Kθ gθ ap θ ξ e s ω).2 (ξ s ω) -
        ∫ z, EvSI.eR n δ (Kθ (θ 0 ω)) (gθ s (θ s ω)) (sigAd n δ Kθ gθ ap θ ξ e s ω).2 z *
          φ c (sigAd n δ Kθ gθ ap θ ξ e s ω).2 z ∂(EvSI.gam d) := by
  rw [EvSI.zSeq_of_lt _ _ _ _ _ _ hs]
  unfold EvSI.incr
  rw [EvSI.mean_aOf n δ Kθ gθ M s (φ c) _ hst, Y_eqAd n δ Kθ gθ ap θ ξ e ω s hK]
  simp only [fF_sigAd n δ Kθ gθ ap θ ξ e ω s hK]
  unfold EvSI.aOf EvSI.bOf
  simp only [hst, ↓reduceIte, fF_sigAd n δ Kθ gθ ap θ ξ e ω s hK]
  ring

end path

end EvAd

end AdversarialBco.Poly
