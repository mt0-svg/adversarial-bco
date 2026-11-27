/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.ShadowAdv
public import AdversarialBco.Poly.Df2ApMeasProof
public import AdversarialBco.Poly.PgMeasProof

@[expose] public section

/-!
# The reference P° is adapted to the coupled filtration

* `cIdx_mem_idxC_succ`: the coordinates of round `t` on the coupled layout are known after round `t`;
* `nextAdv_measurable`: the round map after the observation with the checked advice routine is measurable jointly
  in the position, the advice, the state, the draw and the observation (through `meas_apAdv`);
* `cRoundA_run`: the round of P° in mode `run`; `cRoundA_measL`: the round of P° is measurable jointly in the
  position, the loss parameter, the advice, the mode, the draw, the noise and the dither (with the routine `apAdv v`).

The measurability of P°'s mode and dither is in Unified/WorldShadow.lean (`mode_meas`, `zeta_meas`).
-/

open MeasureTheory Matrix

namespace AdversarialBco.Bit.Cpl

open AdversarialBco.RealRAM AdversarialBco.Poly AdversarialBco.Poly.Layer2 AdversarialBco.Poly.ApMeas
open AdversarialBco.Poly.Conj1 (fL measurable_fL)

variable {d : ℕ}

attribute [local fun_prop] ApMeas.measurable_st_first ApMeas.measurable_st_mu ApMeas.measurable_st_P
  ApMeas.measurable_st_S ApMeas.measurable_st_A ApMeas.measurable_st_b ApMeas.measurable_st_k ApMeas.measurable_st_G
  ApMeas.measurable_st_l ApMeas.measurable_st_ctr ApMeas.measurable_st_r measurable_oNorm

/-! ## The coordinates of the coupled layout -/

theorem cIdx_mem_idxC_succ {t c : ℕ} (hc : c < d + 5) : cIdx d t c ∈ idxC d (t + 1) := by
  refine Or.inr ?_
  show 2 * (t * (d + 5) + c) < 2 * ((t + 1) * (d + 5))
  nlinarith

/-! ## The round map with the checked advice -/

set_option maxHeartbeats 1000000 in
/-- The round map after the observation with the checked advice routine is measurable jointly in the position, the
advice, the state, the draw and the observation, for a family of regions with a measurable graph. -/
theorem nextAdv_measurable (p : Df2OPar) (n : ℕ) (Keps : PgSp d → Set (Fin d → ℝ))
    (hK : MeasurableSet {q : PgSp d × (Fin d → ℝ) | q.2 ∈ Keps q.1}) :
    Measurable fun x : (PgSp d × Adv d) × Df2St d × (Fin d → ℝ) × ℝ =>
      df2NextAP (apAdv x.1.2) p n (Keps x.1.1) x.2.1 x.2.2.1 (x.2.1.A *ᵥ x.2.2.1) x.2.2.2 := by
  simp only [nextE_eq]
  unfold nextE
  dsimp only
  refine Measurable.ite ?_ measurable_const ?_
  · refine mset_or (mset_le ?_ measurable_const) (mset_le ?_ measurable_const) <;> fun_prop
  refine Measurable.ite ?_ measurable_const ?_
  · refine mset_or (mset_lt measurable_const ?_) (mset_lt measurable_const ?_) <;> fun_prop
  refine Measurable.ite ?_ measurable_const ?_
  · refine mset_lt measurable_const ?_; fun_prop
  refine meas_optElim ?_ measurable_const ?_
  · refine meas_apAdv _ (by fun_prop) _ ?_ _ _ _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_
    · exact graphMeas_ite_bool (by fun_prop) (graphMeas_comp hK (by fun_prop))
        (graphMeas_sub (graphMeas_comp hK (by fun_prop)) (by fun_prop) _)
    all_goals fun_prop
  refine Measurable.ite ?_ measurable_const ?_
  · refine mset_le ?_ measurable_const; fun_prop
  refine Measurable.ite ?_ measurable_const ?_
  · refine mset_lt measurable_const ?_; fun_prop
  refine meas_optElim ?_ measurable_const ?_
  · refine meas_apAdv _ (by fun_prop) _ ?_ _ _ _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_
    · exact graphMeas_sub (graphMeas_comp hK (by fun_prop)) (by fun_prop) _
    all_goals fun_prop
  exact meas_run (meas_st_mk measurable_const (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
    (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) measurable_const)

open Classical in
theorem cRoundA_run (n : ℕ) (δ : ℝ) (K : Set (E d)) (q : PgSp d) (ap : ApFun d) (ft : E d → ℝ) (nt : ℝ)
    (ξ : Fin d → ℝ) (ζ : ℝ) (st : Df2St d) : cRoundA n δ K q ap ft nt ξ ζ (.run st) =
      if cPoint n δ K q st ξ ∈ K then (cPoint n δ K q st ξ, df2NextAP ap (df2oPar d n δ) n
        (df2KepsOf (df2Kp K q (df2oPar d n δ).R) (df2oPar d n δ).eps) st ξ (st.A *ᵥ ξ)
        (cPt n δ K q st ξ * (ft (cPoint n δ K q st ξ) + nt + ζ) / 2 + 2 * (cPt n δ K q st ξ - 1) / (df2oPar d n δ).eps))
      else (0, .off) := rfl

set_option maxHeartbeats 1000000 in
/-- The round of P° is measurable jointly in the position, the loss parameter, the advice, the mode, the draw, the
noise and the dither. -/
theorem cRoundA_measL {n : ℕ} {δ : ℝ} {K : Set (E d)} (hKc : IsClosed K) (hKconv : Convex ℝ K)
    (hR : 1 ≤ (df2oPar d n δ).R) (hmw : 1 / (df2oPar d n δ).R ≤ df2Mw d)
    {Λ : Type} [MeasurableSpace Λ] {ft : Λ → E d → ℝ} (hft : Measurable fun p : Λ × E d => ft p.1 p.2) :
    Measurable fun x : (PgSp d × Λ × Adv d) × Df2Mode d × (Fin d → ℝ) × ℝ × ℝ =>
      cRoundA n δ K x.1.1 (apAdv x.1.2.2) (ft x.1.2.1) x.2.2.2.1 x.2.2.1 x.2.2.2.2 x.2.1 := by
  classical
  refine measurable_mode_split (fun x : (PgSp d × Λ × Adv d) × Df2Mode d × (Fin d → ℝ) × ℝ × ℝ =>
    cRoundA n δ K x.1.1 (apAdv x.1.2.2) (ft x.1.2.1) x.2.2.2.1 x.2.2.1 x.2.2.2.2 x.2.1) ?_ ?_ ?_
  · simp only [cRoundA, df2RoundGa]
    exact measurable_const
  · simp only [cRoundA, df2RoundGa]
    have hc : Measurable fun x : (PgSp d × Λ × Adv d) × (Fin d → ℝ) × ℝ × ℝ => pgMu x.1.1 + pgOp x.1.1 0 := by
      have h := (pg_continuous d).2.2.measurable.comp ((measurable_fst.comp measurable_fst).prodMk
        (measurable_const : Measurable fun _ : (PgSp d × Λ × Adv d) × (Fin d → ℝ) × ℝ × ℝ => (0 : E d)))
      rw [Function.comp_def] at h
      exact h
    exact Measurable.ite (hc hKc.measurableSet) (hc.prodMk measurable_const) measurable_const
  · simp only [cRoundA_run]
    have hX : Measurable fun x : (PgSp d × Λ × Adv d) × Df2St d × (Fin d → ℝ) × ℝ × ℝ => cX n δ x.2.1 x.2.2.1 := by
      unfold cX; fun_prop
    have hgauge := gauge_kTh_meas (n := n) (δ := δ) hKc hKconv PgMeas.pgGoodMeas hR hmw
    have hq : Measurable fun x : (PgSp d × Λ × Adv d) × Df2St d × (Fin d → ℝ) × ℝ × ℝ => x.1.1 :=
      measurable_fst.comp measurable_fst
    have hpt : Measurable fun x : (PgSp d × Λ × Adv d) × Df2St d × (Fin d → ℝ) × ℝ × ℝ =>
        cPt n δ K x.1.1 x.2.1 x.2.2.1 :=
      measurable_const.max ((hgauge.comp (hq.prodMk
        ((PiLp.continuous_toLp 2 _).measurable.comp hX))).div_const _)
    have hx : Measurable fun x : (PgSp d × Λ × Adv d) × Df2St d × (Fin d → ℝ) × ℝ × ℝ =>
        cPoint n δ K x.1.1 x.2.1 x.2.2.1 :=
      (pg_continuous d).2.2.measurable.comp (hq.prodMk
        ((PiLp.continuous_toLp 2 _).measurable.comp (hpt.inv.smul hX)))
    have hfx : Measurable fun x : (PgSp d × Λ × Adv d) × Df2St d × (Fin d → ℝ) × ℝ × ℝ =>
        ft x.1.2.1 (cPoint n δ K x.1.1 x.2.1 x.2.2.1) := by
      have h := hft.comp ((measurable_fst.comp (measurable_snd.comp measurable_fst)).prodMk hx)
      rw [Function.comp_def] at h
      exact h
    have hY : Measurable fun x : (PgSp d × Λ × Adv d) × Df2St d × (Fin d → ℝ) × ℝ × ℝ =>
        cPt n δ K x.1.1 x.2.1 x.2.2.1 * (ft x.1.2.1 (cPoint n δ K x.1.1 x.2.1 x.2.2.1) + x.2.2.2.1 + x.2.2.2.2) / 2 +
          2 * (cPt n δ K x.1.1 x.2.1 x.2.2.1 - 1) / (df2oPar d n δ).eps := by
      fun_prop
    have hN := nextAdv_measurable (df2oPar d n δ) n
      (fun Ps => df2KepsOf (df2Kp K Ps (df2oPar d n δ).R) (df2oPar d n δ).eps) (keps_graph K hKc _ _)
    have hnext := hN.comp ((hq.prodMk (measurable_snd.comp (measurable_snd.comp measurable_fst))).prodMk
      ((measurable_fst.comp measurable_snd).prodMk
        ((measurable_fst.comp (measurable_snd.comp measurable_snd)).prodMk hY)))
    rw [Function.comp_def] at hnext
    exact Measurable.ite (hx hKc.measurableSet) (hx.prodMk hnext) measurable_const

end AdversarialBco.Bit.Cpl
