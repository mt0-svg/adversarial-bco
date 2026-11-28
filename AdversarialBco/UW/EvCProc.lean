/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.UW.EvIface
public import AdversarialBco.Poly.Df2EvAdMeasV

@[expose] public section

/-!
# The weighted epoch on setting (E) as a process

The process of Theorem U's `Df2EvAdMeasV.lean` for the weighted epoch of Theorem UW (UW/Defs.lean, `modeEW`,
`pathW`), at any parameter record `p` (the table T4U is `parW d n ρ.u`). On an instance of `UWOnSetE` the context at
`ω` is `ctxP p n Kθ apθ θ ψ ω = ⟨p, n, Kθ (θ 0 ω), fun s => apθ (ψ s ω)⟩` (`ctxE` at `p = parW d n ρ.u`, by `rfl`),
the unweighted path is `pathP gθ θ ξ e ω`, and the events read the weighted path `pathW (ctxP ..) b0 y0 (pathP ..)`.

* `roundOfEW`: round `s` of the weighted epoch as a function of the parameter, the advice, the mode, the draw and the
  noise; `measurable_roundOfEW` under `Df2EpochMeasV` (the observation `obsW` is continuous);
* `measurable_modeEW`: the mode of the weighted epoch before round `s ≤ m` is measurable in `𝒢 s`;
* `sigE s = (θ s, st_s)`, the state process of the weighted epoch (`st_s` the state of Theorem U's learner on
  `pathW`, `mode_pathW`), measurable in `𝒢 s` for `s ≤ m` (`measurable_sigE`);
* `Y_sigE`: in a round in mode `run`, the observation on `pathW` is `obsW b0 y0 ξ_s (fFE + fPE e_s)` at
  `(sigE s, ξ_s)`, so it is a function of the state process, the draw and the noise of the round;
* the directions of the events (c), (d), (e): `phiLE`, `phiHE`, with `ghat_dotE` and `shh_sqE` on any context.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped Matrix

namespace AdversarialBco.UW

open AdversarialBco.Poly AdversarialBco.Poly.ApMeas AdversarialBco.Poly.Layer2

variable {d : ℕ}

/-! ## The functions of a round at a parameter record -/

section Round

variable (p : Df2OPar) (n : ℕ) (b0 y0 : ℝ) {Θ : Type} {V : Type} (Kθ : Θ → Set (E d)) (gθ : ℕ → Θ → E d → ℝ)
  (apθ : V → ApFun d)

/-- The point `X = μ + (1 - λ) A z` of a state. -/
noncomputable def xOfE (st : Df2St d) (z : Fin d → ℝ) : Fin d → ℝ := st.mu + (1 - p.lam) • (st.A *ᵥ z)

/-- The extension of round `s` at the point of a state, the body and the loss read at the parameter `x.1.1`. -/
noncomputable def fFE (s : ℕ) (x : (Θ × Df2St d) × (Fin d → ℝ)) : ℝ :=
  df2Ext p (Kθ x.1.1) (gθ s x.1.1) (WithLp.toLp 2 (xOfE p x.1.2 x.2))

/-- The gauge factor `pip` at the point of a state. -/
noncomputable def fPE (x : (Θ × Df2St d) × (Fin d → ℝ)) : ℝ :=
  df2Pip p (Kθ x.1.1) (WithLp.toLp 2 (xOfE p x.1.2 x.2))

/-- The unweighted value of round `s`, `e_s(X) + pip(X) e`. -/
noncomputable def yOfE (s : ℕ) (q : Θ) (st : Df2St d) (z : Fin d → ℝ) (e : ℝ) : ℝ :=
  df2Ext p (Kθ q) (gθ s q) (WithLp.toLp 2 (xOfE p st z)) + df2Pip p (Kθ q) (WithLp.toLp 2 (xOfE p st z)) * e

/-- Round `s` of the weighted epoch at the parameter and the advice. -/
noncomputable def roundOfEW (s : ℕ) (x : (Θ × V) × Df2Mode d × (Fin d → ℝ) × ℝ) : Df2Mode d :=
  (df2RoundEW ⟨p, n, Kθ x.1.1, fun _ => apθ x.1.2⟩ b0 y0 (apθ x.1.2) (gθ s x.1.1) x.2.2.2 x.2.2.1 x.2.1).2

theorem roundOfEW_eq (s : ℕ) (x : (Θ × V) × Df2Mode d × (Fin d → ℝ) × ℝ) :
    roundOfEW p n b0 y0 Kθ gθ apθ s x =
      if x.2.1.code.1 = 0 then .off else if x.2.1.code.1 = 1 then .guard else
        df2NextAP (apθ x.1.2) p n (df2KepsOf (Kθ x.1.1) p.eps) x.2.1.code.2 x.2.2.1
          (x.2.1.code.2.A *ᵥ x.2.2.1) (obsW b0 y0 x.2.2.1 (yOfE p Kθ gθ s x.1.1 x.2.1.code.2 x.2.2.1 x.2.2.2)) := by
  obtain ⟨⟨q, v⟩, M, ξ, e⟩ := x
  cases M with
  | off => rfl
  | guard => rfl
  | run st =>
    simp only [Df2Mode.code, show ((2 : Fin 3) = 0) ↔ False by decide, show ((2 : Fin 3) = 1) ↔ False by decide,
      ite_false]
    show df2NextAP (apθ v) p n _ st ξ _ _ = df2NextAP (apθ v) p n _ st ξ _ _
    congr 2
    simp only [yOfE, xOfE, df2Ext, WithLp.toLp_smul]
    ring

theorem measurable_xOfE : Measurable fun x : Df2St d × (Fin d → ℝ) => xOfE p x.1 x.2 := by
  unfold xOfE
  have hA : Measurable fun x : Df2St d × (Fin d → ℝ) => (x.1.A, x.2) :=
    (ApMeas.measurable_st_A.comp measurable_fst).prodMk measurable_snd
  have hmv : Measurable fun y : Matrix (Fin d) (Fin d) ℝ × (Fin d → ℝ) => y.1 *ᵥ y.2 :=
    (Continuous.matrix_mulVec continuous_fst continuous_snd).measurable
  have h2 : Measurable fun x : Df2St d × (Fin d → ℝ) => x.1.A *ᵥ x.2 := hmv.comp hA
  exact (ApMeas.measurable_st_mu.comp measurable_fst).add (h2.const_smul (1 - p.lam))

/-- The observation with sure ranges is continuous in the draw and the value. -/
theorem continuous_obsW : Continuous fun x : (Fin d → ℝ) × ℝ => obsW b0 y0 x.1 x.2 := by
  have h1 : Continuous fun x : (Fin d → ℝ) × ℝ => wgt b0 (x.1 ⬝ᵥ x.1) := by
    unfold wgt
    exact continuous_const.min (continuous_const.max
      (continuous_const.sub (continuous_fst.dotProduct continuous_fst)))
  have h2 : Continuous fun x : (Fin d → ℝ) × ℝ => clipW y0 x.2 := by
    unfold clipW
    exact continuous_const.max (continuous_const.min continuous_snd)
  unfold obsW
  exact h1.mul h2

theorem measurable_obsW_uncurry : Measurable (Function.uncurry (obsW (d := d) b0 y0)) :=
  (continuous_obsW b0 y0).measurable

variable {p n Kθ gθ apθ}

theorem measurable_yOfE [MeasurableSpace Θ] [MeasurableSpace V] {m : ℕ}
    (hmeas : Df2EpochMeasV p n m Kθ gθ apθ) {s : ℕ} (hs : s < m) :
    Measurable fun x : Θ × Df2St d × (Fin d → ℝ) × ℝ => yOfE p Kθ gθ s x.1 x.2.1 x.2.2.1 x.2.2.2 := by
  have hX : Measurable fun x : Θ × Df2St d × (Fin d → ℝ) × ℝ =>
      (WithLp.toLp 2 (xOfE p x.2.1 x.2.2.1) : E d) :=
    (WithLp.measurable_toLp 2 _).comp ((measurable_xOfE p).comp
      ((measurable_fst.comp measurable_snd).prodMk (measurable_fst.comp (measurable_snd.comp measurable_snd))))
  have hext := (hmeas.2.1 s hs).comp (measurable_fst.prodMk hX)
  have hg := hmeas.1.comp (measurable_fst.prodMk hX)
  have hpip : Measurable fun x : Θ × Df2St d × (Fin d → ℝ) × ℝ =>
      df2Pip p (Kθ x.1) (WithLp.toLp 2 (xOfE p x.2.1 x.2.2.1)) := by
    unfold df2Pip
    exact measurable_const.max (hg.div_const _)
  exact hext.add (hpip.mul (measurable_snd.comp (measurable_snd.comp measurable_snd)))

theorem measurable_roundOfEW [MeasurableSpace Θ] [MeasurableSpace V] {m : ℕ}
    (hmeas : Df2EpochMeasV p n m Kθ gθ apθ) {s : ℕ} (hs : s < m) :
    Measurable (roundOfEW p n b0 y0 Kθ gθ apθ s) := by
  have heq : roundOfEW p n b0 y0 Kθ gθ apθ s = fun x =>
      if x.2.1.code.1 = 0 then .off else if x.2.1.code.1 = 1 then .guard else
        df2NextAP (apθ x.1.2) p n (df2KepsOf (Kθ x.1.1) p.eps) x.2.1.code.2 x.2.2.1
          (x.2.1.code.2.A *ᵥ x.2.2.1) (obsW b0 y0 x.2.2.1 (yOfE p Kθ gθ s x.1.1 x.2.1.code.2 x.2.2.1 x.2.2.2)) :=
    funext fun x => roundOfEW_eq p n b0 y0 Kθ gθ apθ s x
  rw [heq]
  have hcode : Measurable fun x : (Θ × V) × Df2Mode d × (Fin d → ℝ) × ℝ => x.2.1.code :=
    ApMeas.measurable_mode_code.comp (measurable_fst.comp measurable_snd)
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
      yOfE p Kθ gθ s x.1.1 x.2.1.code.2 x.2.2.1 x.2.2.2 := by
    have h := (measurable_yOfE hmeas hs).comp hin1
    exact h
  have hW : Measurable fun x : (Θ × V) × Df2Mode d × (Fin d → ℝ) × ℝ =>
      obsW b0 y0 x.2.2.1 (yOfE p Kθ gθ s x.1.1 x.2.1.code.2 x.2.2.1 x.2.2.2) := by
    have h := (measurable_obsW_uncurry (d := d) b0 y0).comp (hξ.prodMk hY)
    exact h
  have hin2 : Measurable fun x : (Θ × V) × Df2Mode d × (Fin d → ℝ) × ℝ =>
      (x.1, x.2.1.code.2, x.2.2.1, obsW b0 y0 x.2.2.1 (yOfE p Kθ gθ s x.1.1 x.2.1.code.2 x.2.2.1 x.2.2.2)) :=
    measurable_fst.prodMk (hst.prodMk (hξ.prodMk hW))
  have hN := hmeas.2.2.comp hin2
  have h := EvGY.measurable_ite_code htag hN
  exact h

end Round

/-! ## The process on `Ω` -/

section Proc

variable (p : Df2OPar) (n : ℕ) (b0 y0 : ℝ) {Θ : Type} {V : Type} (Kθ : Θ → Set (E d)) (gθ : ℕ → Θ → E d → ℝ)
  (apθ : V → ApFun d) {Ω : Type}

/-- The context of the epoch at `ω`: the record `p`, the body at `θ 0 ω`, the routine `apθ (ψ s ω)` in round `s`. -/
noncomputable def ctxP (θ : ℕ → Ω → Θ) (ψ : ℕ → Ω → V) (ω : Ω) : Df2Ctx d :=
  ⟨p, n, Kθ (θ 0 ω), fun s => apθ (ψ s ω)⟩

/-- The unweighted path of the epoch at `ω`. -/
def pathP (θ : ℕ → Ω → Θ) (ξ : ℕ → Ω → Fin d → ℝ) (e : ℕ → Ω → ℝ) (ω : Ω) : Df2Path d :=
  ⟨fun s => gθ s (θ s ω), fun s => e s ω, fun s => ξ s ω⟩

variable (θ : ℕ → Ω → Θ) (ψ : ℕ → Ω → V) (ξ : ℕ → Ω → Fin d → ℝ) (e : ℕ → Ω → ℝ)

theorem modeEW_succ (hK : ∀ s ω, Kθ (θ s ω) = Kθ (θ 0 ω)) (ω : Ω) (s : ℕ) :
    modeEW (ctxP p n Kθ apθ θ ψ ω) b0 y0 (pathP gθ θ ξ e ω) (s + 1) =
      roundOfEW p n b0 y0 Kθ gθ apθ s
        ((θ s ω, ψ s ω), modeEW (ctxP p n Kθ apθ θ ψ ω) b0 y0 (pathP gθ θ ξ e ω) s, ξ s ω, e s ω) := by
  show (df2RoundEW (ctxP p n Kθ apθ θ ψ ω) b0 y0 (apθ (ψ s ω)) (gθ s (θ s ω)) (e s ω) (ξ s ω) _).2 =
    (df2RoundEW ⟨p, n, Kθ (θ s ω), fun _ => apθ (ψ s ω)⟩ b0 y0 (apθ (ψ s ω)) (gθ s (θ s ω)) (e s ω) (ξ s ω) _).2
  rw [hK s ω]
  rfl

/-- The mode of the weighted epoch before round `s ≤ m` is measurable in `𝒢 s`. -/
theorem measurable_modeEW [MeasurableSpace Θ] [MeasurableSpace V] [m0 : MeasurableSpace Ω] {m : ℕ}
    (hmeas : Df2EpochMeasV p n m Kθ gθ apθ) (𝒢 : Filtration ℕ m0) (hK : ∀ s ω, Kθ (θ s ω) = Kθ (θ 0 ω))
    (hθ : ∀ s, Measurable[𝒢 s] (θ s)) (hψ : ∀ s, Measurable[𝒢 (s + 1)] (ψ s))
    (hξ : ∀ s, Measurable[𝒢 (s + 1)] (ξ s)) (he : ∀ s, Measurable[𝒢 (s + 1)] (e s)) :
    ∀ s ≤ m, Measurable[𝒢 s] fun ω => modeEW (ctxP p n Kθ apθ θ ψ ω) b0 y0 (pathP gθ θ ξ e ω) s := by
  intro s hs
  induction s with
  | zero => exact (measurable_const : Measurable[𝒢 0] fun _ : Ω => Df2Mode.run (df2Init p d))
  | succ s ih =>
    have hθ' : Measurable[𝒢 (s + 1)] (θ s) := (hθ s).mono (𝒢.mono (Nat.le_succ s)) le_rfl
    have hm' : Measurable[𝒢 (s + 1)] fun ω => modeEW (ctxP p n Kθ apθ θ ψ ω) b0 y0 (pathP gθ θ ξ e ω) s :=
      (ih (by omega)).mono (𝒢.mono (Nat.le_succ s)) le_rfl
    have htup : Measurable[𝒢 (s + 1)] fun ω =>
        ((θ s ω, ψ s ω), modeEW (ctxP p n Kθ apθ θ ψ ω) b0 y0 (pathP gθ θ ξ e ω) s, ξ s ω, e s ω) :=
      (hθ'.prodMk (hψ s)).prodMk (hm'.prodMk ((hξ s).prodMk (he s)))
    have h := (measurable_roundOfEW b0 y0 (m := m) (s := s) hmeas (by omega)).comp htup
    simp only [Function.comp_def] at h
    simpa only [modeEW_succ p n b0 y0 Kθ gθ apθ θ ψ ξ e hK] using h

/-- The state of the weighted epoch before round `s`: the state of Theorem U's learner on `pathW`. -/
theorem st_pathW_eq (ω : Ω) (s : ℕ) :
    (ctxP p n Kθ apθ θ ψ ω).st (pathW (ctxP p n Kθ apθ θ ψ ω) b0 y0 (pathP gθ θ ξ e ω)) s =
      (modeEW (ctxP p n Kθ apθ θ ψ ω) b0 y0 (pathP gθ θ ξ e ω) s).stOr (df2Init p d) := by
  show ((ctxP p n Kθ apθ θ ψ ω).mode (pathW (ctxP p n Kθ apθ θ ψ ω) b0 y0 (pathP gθ θ ξ e ω)) s).stOr
    (df2Init p d) = _
  rw [mode_pathW]

/-- The state process of the weighted epoch, `sigE s = (θ s, st_s)`. -/
noncomputable def sigE (s : ℕ) (ω : Ω) : Θ × Df2St d :=
  (θ s ω, (ctxP p n Kθ apθ θ ψ ω).st (pathW (ctxP p n Kθ apθ θ ψ ω) b0 y0 (pathP gθ θ ξ e ω)) s)

/-- The state process is measurable in `𝒢 s` for `s ≤ m`. -/
theorem measurable_sigE [MeasurableSpace Θ] [MeasurableSpace V] [m0 : MeasurableSpace Ω] {m : ℕ}
    (hmeas : Df2EpochMeasV p n m Kθ gθ apθ) (𝒢 : Filtration ℕ m0) (hK : ∀ s ω, Kθ (θ s ω) = Kθ (θ 0 ω))
    (hθ : ∀ s, Measurable[𝒢 s] (θ s)) (hψ : ∀ s, Measurable[𝒢 (s + 1)] (ψ s))
    (hξ : ∀ s, Measurable[𝒢 (s + 1)] (ξ s)) (he : ∀ s, Measurable[𝒢 (s + 1)] (e s)) {s : ℕ} (hs : s ≤ m) :
    Measurable[𝒢 s] (sigE p n b0 y0 Kθ gθ apθ θ ψ ξ e s) := by
  have hst : Measurable[𝒢 s] fun ω =>
      (ctxP p n Kθ apθ θ ψ ω).st (pathW (ctxP p n Kθ apθ θ ψ ω) b0 y0 (pathP gθ θ ξ e ω)) s := by
    have h := (EvSI.measurable_stOr (df2Init p d)).comp
      (measurable_modeEW p n b0 y0 Kθ gθ apθ θ ψ ξ e hmeas 𝒢 hK hθ hψ hξ he s hs)
    simp only [Function.comp_def] at h
    simpa only [st_pathW_eq] using h
  exact (hθ s).prodMk hst

/-- The extension coefficient on the state process is the extension of the context at its state. -/
theorem fFE_sigE (hK : ∀ s ω, Kθ (θ s ω) = Kθ (θ 0 ω)) (ω : Ω) (s : ℕ) (z : Fin d → ℝ) :
    fFE p Kθ gθ s (sigE p n b0 y0 Kθ gθ apθ θ ψ ξ e s ω, z) =
      df2Ext p (Kθ (θ 0 ω)) (gθ s (θ s ω)) (WithLp.toLp 2 (xOfE p
        ((ctxP p n Kθ apθ θ ψ ω).st (pathW (ctxP p n Kθ apθ θ ψ ω) b0 y0 (pathP gθ θ ξ e ω)) s) z)) := by
  simp only [fFE, sigE, hK s ω]

/-- The gauge coefficient on the state process is the gauge factor of the context at its state. -/
theorem fPE_sigE (hK : ∀ s ω, Kθ (θ s ω) = Kθ (θ 0 ω)) (ω : Ω) (s : ℕ) (z : Fin d → ℝ) :
    fPE p Kθ (sigE p n b0 y0 Kθ gθ apθ θ ψ ξ e s ω, z) =
      df2Pip p (Kθ (θ 0 ω)) (WithLp.toLp 2 (xOfE p
        ((ctxP p n Kθ apθ θ ψ ω).st (pathW (ctxP p n Kθ apθ θ ψ ω) b0 y0 (pathP gθ θ ξ e ω)) s) z)) := by
  simp only [fPE, sigE, hK s ω]

/-- **The observation on the weighted path** in a round in mode `run`: `Y^w_s = obsW b0 y0 ξ_s (fFE + fPE e_s)` at
`(sigE s, ξ_s)`. -/
theorem Y_sigE (hK : ∀ s ω, Kθ (θ s ω) = Kθ (θ 0 ω)) (ω : Ω) (s : ℕ) (st : Df2St d)
    (hrun : (ctxP p n Kθ apθ θ ψ ω).mode (pathW (ctxP p n Kθ apθ θ ψ ω) b0 y0 (pathP gθ θ ξ e ω)) s = .run st) :
    (ctxP p n Kθ apθ θ ψ ω).Y (pathW (ctxP p n Kθ apθ θ ψ ω) b0 y0 (pathP gθ θ ξ e ω)) s =
      obsW b0 y0 (ξ s ω) (fFE p Kθ gθ s (sigE p n b0 y0 Kθ gθ apθ θ ψ ξ e s ω, ξ s ω) +
        fPE p Kθ (sigE p n b0 y0 Kθ gθ apθ θ ψ ξ e s ω, ξ s ω) * e s ω) := by
  rw [mode_pathW] at hrun
  rw [Y_pathW _ b0 y0 _ s st hrun, fFE_sigE p n b0 y0 Kθ gθ apθ θ ψ ξ e hK, fPE_sigE p n b0 y0 Kθ gθ apθ θ ψ ξ e hK]
  congr 1
  simp only [Df2Ctx.pip, Df2Ctx.play, Df2Ctx.X, Df2Ctx.w, xOfE, df2Ext, ctxP, pathP, pathW, WithLp.toLp_smul]
  ring

end Proc

/-! ## The directions of the events (c), (d), (e) on any context -/

/-- The direction of event (c) at the point `y`: `⟨P A z, y - μ⟩/(1 - λ)`, so that `⟨ĝ, y - μ⟩ = Y phiLE`. -/
noncomputable def phiLE (p : Df2OPar) (y : Fin d → ℝ) (st : Df2St d) (z : Fin d → ℝ) : ℝ :=
  EvSI.lin st (y - st.mu) z / (1 - p.lam)

/-- The Hessian direction along `h st`: `λ κ₀ (⟨P A z, h⟩² - hᵀ P h)`, so that `hᵀ ŝ'' h = Y phiHE`. -/
noncomputable def phiHE (p : Df2OPar) (h : Df2St d → Fin d → ℝ) (st : Df2St d) (z : Fin d → ℝ) : ℝ :=
  p.lam * p.k0 * (EvSI.lin st (h st) z ^ 2 - df2Sq st.P (h st))

theorem ghat_dotE (c : Df2Ctx d) (π : Df2Path d) (s : ℕ) (y : Fin d → ℝ) :
    c.ghat π s ⬝ᵥ (y - (c.st π s).mu) = c.Y π s * phiLE c.p y (c.st π s) (π.xi s) := by
  simp only [Df2Ctx.ghat, Df2Ctx.u, Df2Ctx.w, phiLE, EvSI.lin, smul_dotProduct, smul_eq_mul]
  ring

theorem shh_sqE (c : Df2Ctx d) (π : Df2Path d) (s : ℕ) (hf : Df2St d → Fin d → ℝ) :
    df2Sq (c.shh π s) (hf (c.st π s)) = c.Y π s * phiHE c.p hf (c.st π s) (π.xi s) := by
  simp only [Df2Ctx.shh, sq_smul, sq_sub, phiHE, EvSI.lin, Df2Ctx.u, Df2Ctx.w]
  have hv : ∀ (u v : Fin d → ℝ), df2Sq (vecMulVec u u) v = (u ⬝ᵥ v) ^ 2 := fun u v => by
    simp only [df2Sq, vecMulVec_mulVec]
    rw [op_smul_eq_smul, dotProduct_smul, smul_eq_mul, dotProduct_comm v u]; ring
  rw [hv]
  ring

end AdversarialBco.UW
