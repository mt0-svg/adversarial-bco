/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.UW.Interfaces

@[expose] public section

/-!
# The reference P° of Theorem UW is adapted, and Step 2 of SHADOW

The port of Bit/ShadowMeas.lean (`cRoundA_measL`) and of Unified/WorldShadow.lean (`RunW.mode_meas`, `shR_meas`,
`zeta_meas`, `adv_meas`, `coupStepPropW_holds`) to the weighted round `cRoundW` of UW/Defs.lean. The weight and the
clip enter the round only through the observation passed to the round map, and `obsW` is continuous, so every
measurability step carries over.

* `cRoundW_run`, `cRoundW_measL`: the weighted round is measurable jointly in the position, the loss parameter, the
  advice, the mode, the draw, the noise and the dither;
* `modeU_meas` (Lemma W-MEAS for P° of Theorem UW), `shRU_meas`, `zetaU_meas`, `advU_meas`;
* `coupStepPropUW : CoupStepPropUW` (Step 2 of SHADOW with `modeU`).

`modeU_meas` reads only `1 ≤ d` of the regime: the gauge of `kTh n δc K q` and the region of the round map read the
radius `R`, which no level and no scale change (`parW_R`).
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped Matrix

namespace AdversarialBco.UW

open AdversarialBco.RealRAM AdversarialBco.Poly AdversarialBco.Poly.Layer2 AdversarialBco.Bit.Cpl
open AdversarialBco.Poly.ApMeas
open AdversarialBco.Unified.World
open AdversarialBco.Poly.Conj1 (fL measurable_fL)

attribute [local fun_prop] ApMeas.measurable_st_first ApMeas.measurable_st_mu ApMeas.measurable_st_P
  ApMeas.measurable_st_S ApMeas.measurable_st_A ApMeas.measurable_st_b ApMeas.measurable_st_k ApMeas.measurable_st_G
  ApMeas.measurable_st_l ApMeas.measurable_st_ctr ApMeas.measurable_st_r measurable_oNorm

variable {d : ℕ}

/-! ## The radius -/

/-- `1 ≤ R = 134 d (log(2d + 2))^{1/2}` for `d ≥ 1`, at every level. -/
theorem one_le_R_of (n : ℕ) (δ : ℝ) (hd : 1 ≤ d) : 1 ≤ (df2oPar d n δ).R := by
  have hd' : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have h_exp_lt : Real.exp 1 < 2 * (d : ℝ) + 2 := by
    have h : Real.exp 1 < 3 := Real.exp_one_lt_three
    have h3 : (3 : ℝ) ≤ 2 * (d : ℝ) + 2 := by nlinarith
    linarith
  have h_log_one_le : 1 ≤ Real.log (2 * (d : ℝ) + 2) := by
    calc
      1 = Real.log (Real.exp 1) := by rw [Real.log_exp 1]
      _ ≤ Real.log (2 * (d : ℝ) + 2) := Real.log_le_log (Real.exp_pos 1) (le_of_lt h_exp_lt)
  have h_sqrt_one_le : 1 ≤ Real.sqrt (Real.log (2 * (d : ℝ) + 2)) := (Real.one_le_sqrt).mpr h_log_one_le
  show 1 ≤ 134 * (d : ℝ) * Real.sqrt (Real.log (2 * d + 2))
  nlinarith

theorem inv_R_le_of (n : ℕ) (δ : ℝ) (hd : 1 ≤ d) : 1 / (df2oPar d n δ).R ≤ df2Mw d := inv_R_le_df2Mw d hd

/-! ## The weighted round -/

/-- `X` of the weighted round at T4U. -/
noncomputable def cXW (n : ℕ) (ρ : RefW) (st : Df2St d) (ξ : Fin d → ℝ) : Fin d → ℝ :=
  st.mu + (1 - (parW d n ρ.u).lam) • (st.A *ᵥ ξ)

/-- `pip(X)` for the gauge of `kTh n δc K q`. -/
noncomputable def cPtW (n : ℕ) (ρ : RefW) (K : Set (E d)) (q : PgSp d) (st : Df2St d) (ξ : Fin d → ℝ) : ℝ :=
  max 1 (gauge (kTh n ρ.δc K q) (WithLp.toLp 2 (cXW n ρ st ξ)) / (1 - (parW d n ρ.u).eps))

/-- The point played from the state `st`. -/
noncomputable def cPointW (n : ℕ) (ρ : RefW) (K : Set (E d)) (q : PgSp d) (st : Df2St d) (ξ : Fin d → ℝ) : E d :=
  pgMu q + pgOp q (WithLp.toLp 2 ((cPtW n ρ K q st ξ)⁻¹ • cXW n ρ st ξ))

open Classical in
theorem cRoundW_run (n : ℕ) (ρ : RefW) (K : Set (E d)) (q : PgSp d) (ap : ApFun d) (ft : E d → ℝ) (nt : ℝ)
    (ξ : Fin d → ℝ) (ζ : ℝ) (st : Df2St d) : cRoundW n ρ K q ap ft nt ξ ζ (.run st) =
      if cPointW n ρ K q st ξ ∈ K then (cPointW n ρ K q st ξ, df2NextAP ap (parW d n ρ.u) n
        (df2KepsOf (df2Kp K q (parW d n ρ.u).R) (parW d n ρ.u).eps) st ξ (st.A *ᵥ ξ)
        (obsW ρ.b0 ρ.y0 ξ (cPtW n ρ K q st ξ * (ft (cPointW n ρ K q st ξ) + nt + ζ) / 2 +
          2 * (cPtW n ρ K q st ξ - 1) / (parW d n ρ.u).eps)))
      else (0, .off) := rfl

theorem obsW_continuous (b0 y0 : ℝ) : Continuous fun x : (Fin d → ℝ) × ℝ => obsW b0 y0 x.1 x.2 := by
  unfold obsW wgt clipW
  have hdot : Continuous fun x : (Fin d → ℝ) × ℝ => x.1 ⬝ᵥ x.1 := by
    simp only [dotProduct]
    fun_prop
  exact (continuous_const.min (continuous_const.max (continuous_const.sub hdot))).mul
    (continuous_const.max (continuous_const.min continuous_snd))

set_option maxHeartbeats 1000000 in
/-- The weighted round is measurable jointly in the position, the loss parameter, the advice, the mode, the draw,
the noise and the dither. -/
theorem cRoundW_measL {n : ℕ} {ρ : RefW} {K : Set (E d)} (hKc : IsClosed K) (hKconv : Convex ℝ K)
    (hR : 1 ≤ (df2oPar d n ρ.δc).R) (hmw : 1 / (df2oPar d n ρ.δc).R ≤ df2Mw d)
    {Λ : Type} [MeasurableSpace Λ] {ft : Λ → E d → ℝ} (hft : Measurable fun p : Λ × E d => ft p.1 p.2) :
    Measurable fun x : (PgSp d × Λ × Adv d) × Df2Mode d × (Fin d → ℝ) × ℝ × ℝ =>
      cRoundW n ρ K x.1.1 (apAdv x.1.2.2) (ft x.1.2.1) x.2.2.2.1 x.2.2.1 x.2.2.2.2 x.2.1 := by
  classical
  refine measurable_mode_split (fun x : (PgSp d × Λ × Adv d) × Df2Mode d × (Fin d → ℝ) × ℝ × ℝ =>
    cRoundW n ρ K x.1.1 (apAdv x.1.2.2) (ft x.1.2.1) x.2.2.2.1 x.2.2.1 x.2.2.2.2 x.2.1) ?_ ?_ ?_
  · simp only [cRoundW, df2RoundGaW]
    exact measurable_const
  · simp only [cRoundW, df2RoundGaW]
    have hc : Measurable fun x : (PgSp d × Λ × Adv d) × (Fin d → ℝ) × ℝ × ℝ => pgMu x.1.1 + pgOp x.1.1 0 := by
      have h := (pg_continuous d).2.2.measurable.comp ((measurable_fst.comp measurable_fst).prodMk
        (measurable_const : Measurable fun _ : (PgSp d × Λ × Adv d) × (Fin d → ℝ) × ℝ × ℝ => (0 : E d)))
      rw [Function.comp_def] at h
      exact h
    exact Measurable.ite (hc hKc.measurableSet) (hc.prodMk measurable_const) measurable_const
  · simp only [cRoundW_run]
    have hX : Measurable fun x : (PgSp d × Λ × Adv d) × Df2St d × (Fin d → ℝ) × ℝ × ℝ =>
        cXW n ρ x.2.1 x.2.2.1 := by
      unfold cXW; fun_prop
    have hgauge := gauge_kTh_meas (n := n) (δ := ρ.δc) hKc hKconv PgMeas.pgGoodMeas hR hmw
    have hq : Measurable fun x : (PgSp d × Λ × Adv d) × Df2St d × (Fin d → ℝ) × ℝ × ℝ => x.1.1 :=
      measurable_fst.comp measurable_fst
    have hpt : Measurable fun x : (PgSp d × Λ × Adv d) × Df2St d × (Fin d → ℝ) × ℝ × ℝ =>
        cPtW n ρ K x.1.1 x.2.1 x.2.2.1 :=
      measurable_const.max ((hgauge.comp (hq.prodMk
        ((PiLp.continuous_toLp 2 _).measurable.comp hX))).div_const _)
    have hx : Measurable fun x : (PgSp d × Λ × Adv d) × Df2St d × (Fin d → ℝ) × ℝ × ℝ =>
        cPointW n ρ K x.1.1 x.2.1 x.2.2.1 :=
      (pg_continuous d).2.2.measurable.comp (hq.prodMk
        ((PiLp.continuous_toLp 2 _).measurable.comp (hpt.inv.smul hX)))
    have hfx : Measurable fun x : (PgSp d × Λ × Adv d) × Df2St d × (Fin d → ℝ) × ℝ × ℝ =>
        ft x.1.2.1 (cPointW n ρ K x.1.1 x.2.1 x.2.2.1) := by
      have h := hft.comp ((measurable_fst.comp (measurable_snd.comp measurable_fst)).prodMk hx)
      rw [Function.comp_def] at h
      exact h
    have hY0 : Measurable fun x : (PgSp d × Λ × Adv d) × Df2St d × (Fin d → ℝ) × ℝ × ℝ =>
        cPtW n ρ K x.1.1 x.2.1 x.2.2.1 * (ft x.1.2.1 (cPointW n ρ K x.1.1 x.2.1 x.2.2.1) + x.2.2.2.1 + x.2.2.2.2) /
          2 + 2 * (cPtW n ρ K x.1.1 x.2.1 x.2.2.1 - 1) / (parW d n ρ.u).eps := by
      fun_prop
    have hξ : Measurable fun x : (PgSp d × Λ × Adv d) × Df2St d × (Fin d → ℝ) × ℝ × ℝ => x.2.2.1 :=
      measurable_fst.comp (measurable_snd.comp measurable_snd)
    have hY : Measurable fun x : (PgSp d × Λ × Adv d) × Df2St d × (Fin d → ℝ) × ℝ × ℝ =>
        obsW ρ.b0 ρ.y0 x.2.2.1 (cPtW n ρ K x.1.1 x.2.1 x.2.2.1 *
          (ft x.1.2.1 (cPointW n ρ K x.1.1 x.2.1 x.2.2.1) + x.2.2.2.1 + x.2.2.2.2) / 2 +
            2 * (cPtW n ρ K x.1.1 x.2.1 x.2.2.1 - 1) / (parW d n ρ.u).eps) := by
      have h := (obsW_continuous (d := d) ρ.b0 ρ.y0).measurable.comp (hξ.prodMk hY0)
      rw [Function.comp_def] at h
      exact h
    have hN := nextAdv_measurable (parW d n ρ.u) n
      (fun Ps => df2KepsOf (df2Kp K Ps (parW d n ρ.u).R) (parW d n ρ.u).eps) (keps_graph K hKc _ _)
    have hnext := hN.comp ((hq.prodMk (measurable_snd.comp (measurable_snd.comp measurable_fst))).prodMk
      ((measurable_fst.comp measurable_snd).prodMk (hξ.prodMk hY)))
    rw [Function.comp_def] at hnext
    exact Measurable.ite (hx hKc.measurableSet) (hx.prodMk hnext) measurable_const

/-! ## Lemma W-MEAS for P° of Theorem UW -/

section Meas

variable {n : ℕ} {K : Set (E d)} {Ω : Type} [m0 : MeasurableSpace Ω] {W : CWorld d Ω} (B : RunW d n K W)
  (ρ : RefW)

/-- The shift of round `t` on P°'s run is known at `F*_t`, given the mode before round `t` is known at `𝓕 t`. -/
theorem shRU_meas (hB : BLMeasW B) {t : ℕ} (hmode : Measurable[W.𝓕 t] fun ω => modeU B ρ t ω) :
    Measurable[W.Fσ t] (shRU B ρ t) :=
  (hB.sh t).comp (RunW.pairMode_meas (hmode.mono (RunW.𝓕_le_Fσ t) le_rfl))

/-- P°'s dither of round `t` is known after round `t`. -/
theorem zetaU_meas (hW : WorldLawOK W) (hB : BLMeasW B) (hC : CoupLaw B.Coup) {t : ℕ}
    (hmode : Measurable[W.𝓕 t] fun ω => modeU B ρ t ω) :
    Measurable[W.𝓕 (t + 1)] fun ω => B.zeta t ω (modeU B ρ t ω) := by
  have hs := (shRU_meas B ρ hB hmode).mono (hW.Fσ_le t) le_rfl
  exact hC.meas.comp (hs.fst.prodMk (hs.snd.prodMk (hW.meas_zz t)))

/-- P°'s advice of round `t` is known after round `t`. -/
theorem advU_meas (hB : BLMeasW B) {t : ℕ} (hmode : Measurable[W.𝓕 t] fun ω => modeU B ρ t ω) :
    Measurable[W.𝓕 (t + 1)] fun ω => B.adv t ω (modeU B ρ t ω) :=
  (hB.adv t).comp (RunW.pairMode_meas (hmode.mono (W.𝓕.mono (Nat.le_succ t)) le_rfl))

/-- **Lemma W-MEAS** for P° of Theorem UW: its mode before round `t` is known before round `t`. -/
theorem modeU_meas (hW : WorldLawOK W) (hd : 1 ≤ d) (hKc : IsClosed K) (hKconv : Convex ℝ K)
    (hpos : Measurable[W.𝓕 0] B.pos) (hB : BLMeasW B) (hC : CoupLaw B.Coup) :
    ∀ t, Measurable[W.𝓕 t] fun ω => modeU B ρ t ω := by
  have hR := one_le_R_of n ρ.δc hd
  have hmw := inv_R_le_of n ρ.δc hd
  intro t
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    have hpos' : Measurable[W.𝓕 (t + 1)] B.pos := hpos.mono (W.𝓕.mono (Nat.zero_le _)) le_rfl
    have hm' : Measurable[W.𝓕 (t + 1)] fun ω => modeU B ρ t ω := ih.mono (W.𝓕.mono (Nat.le_succ t)) le_rfl
    have hrest : Measurable[W.𝓕 (t + 1)] fun ω =>
        (modeU B ρ t ω, W.xi t ω, W.nz t ω, B.zeta t ω (modeU B ρ t ω)) :=
      hm'.prodMk ((hW.meas_xi t).prodMk ((hW.meas_nz t).prodMk (zetaU_meas B ρ hW hB hC ih)))
    by_cases ht : t < n
    · have hft := measurable_fL (K := K) (L := B.F.L) (t := t) (fun l => (B.F.adm t ht l).1) (B.F.meas t ht)
      have hround := cRoundW_measL (n := n) (ρ := ρ) hKc hKconv hR hmw hft
      have hlam : Measurable[W.𝓕 (t + 1)] (B.F.lam t) :=
        (B.F.lam_meas t ht).mono (W.𝓕.mono (Nat.le_succ t)) le_rfl
      have htup : Measurable[W.𝓕 (t + 1)] fun ω =>
          ((B.pos ω, B.F.lam t ω, B.adv t ω (modeU B ρ t ω)),
            modeU B ρ t ω, W.xi t ω, W.nz t ω, B.zeta t ω (modeU B ρ t ω)) :=
        (hpos'.prodMk (hlam.prodMk (advU_meas B ρ hB ih))).prodMk hrest
      have h := measurable_snd.comp (hround.comp htup)
      convert h using 1
      funext ω
      simp only [Function.comp_def, modeU, RunW.lossR, ht, ↓reduceIte]
    · have hft : Measurable fun p : Unit × E d => (fun (_ : Unit) (_ : E d) => (0 : ℝ)) p.1 p.2 := measurable_const
      have hround := cRoundW_measL (n := n) (ρ := ρ) (ft := fun (_ : Unit) (_ : E d) => (0 : ℝ)) hKc hKconv hR hmw
        hft
      have htup : Measurable[W.𝓕 (t + 1)] fun ω =>
          ((B.pos ω, (), B.adv t ω (modeU B ρ t ω)),
            modeU B ρ t ω, W.xi t ω, W.nz t ω, B.zeta t ω (modeU B ρ t ω)) :=
        (hpos'.prodMk (measurable_const.prodMk (advU_meas B ρ hB ih))).prodMk hrest
      have h := measurable_snd.comp (hround.comp htup)
      convert h using 1
      funext ω
      simp only [Function.comp_def, modeU, RunW.lossR, ht, ↓reduceIte]
      rfl

end Meas

/-! ## Step 2 of SHADOW -/

/-- **Step 2 of SHADOW** for P° of Theorem UW. -/
theorem coupStepPropUW : CoupStepPropUW := by
  intro d n ρ K Ω _ W B κ0 κ1 hreg hKc hKconv hW hpos hC hTV hB hκ0 hκ1 t
  have := hW.prob
  have hmode := modeU_meas B ρ hW hreg.hd hKc hKconv hpos hB hC t
  have hX : Measurable[W.Fσ t] fun ω => (shRU B ρ t ω, W.nz t ω) :=
    (shRU_meas B ρ hB hmode).prodMk (Measurable.of_comap_le le_sup_right : Measurable[W.Fσ t] (W.nz t))
  have hFle := hW.Fσ_le_m0 t
  have hZ : Measurable (W.zz t) := (hW.meas_zz t).mono (W.𝓕.le (t + 1)) le_rfl
  set D : Set (((ℝ × ℝ) × ℝ) × (Fin 3 → ℝ)) := {p | B.Coup p.1.1.1 p.1.1.2 p.2 ≠ p.1.1.1 + p.1.1.2 * p.2 0 / 2}
  set Bs : Set ((ℝ × ℝ) × ℝ) := {x | 0 < x.1.2 ∧ tvB x.1.1 x.1.2 ≤ κ0 + κ1 * |x.2|}
  have hD : MeasurableSet D := by
    have hc := hC.meas.comp (show Measurable fun p : ((ℝ × ℝ) × ℝ) × (Fin 3 → ℝ) => (p.1.1.1, p.1.1.2, p.2) by
      fun_prop)
    exact (measurableSet_eq_fun hc (by fun_prop)).compl
  have hBs : MeasurableSet Bs := by
    have h1 : Measurable fun x : (ℝ × ℝ) × ℝ => tvB x.1.1 x.1.2 := tvB_measurable.comp measurable_fst
    have h2 : Measurable fun x : (ℝ × ℝ) × ℝ => κ0 + κ1 * |x.2| := by fun_prop
    exact (measurableSet_lt (f := fun _ : (ℝ × ℝ) × ℝ => (0 : ℝ)) (g := fun x => x.1.2) measurable_const
      (by fun_prop)).inter (measurableSet_le h1 h2)
  have hcore := step2_core (W.Fσ t) W.μ hFle (fun ω => (shRU B ρ t ω, W.nz t ω)) hX (W.zz t) hZ
    (hW.z_indep t) D hD Bs hBs (fun x => κ0 + κ1 * |x.2|) (by fun_prop) (by
      rintro ⟨⟨m, r⟩, e⟩ ⟨hr, hb⟩
      rw [hW.z_law t]
      exact (hTV m r hr).trans (ENNReal.ofReal_le_ofReal hb))
  have hnm : Measurable (W.nz t) := (hW.meas_nz t).mono (W.𝓕.le _) le_rfl
  have hint := lintegral_affine_abs W.μ (W.nz t) hnm (hW.noise_abs_lintegral t) κ0 κ1 hκ0 hκ1
  refine le_trans (le_of_eq ?_) (hcore.trans hint)
  rfl

end AdversarialBco.UW
