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

* the coordinates of the coupled layout: `ξc d t`, `ξg d t`, `zc d t` and the noise `ε_t` are known after round `t`
  (`meas_ξc`, `meas_ξg`, `meas_zc`, `meas_noise_c`), and `Fσ d t ≤ cσ d (t + 1)` (`Fσ_le`);
* `nextAdv_measurable`: the round map after the observation with the checked advice routine is measurable jointly
  in the position, the advice, the state, the draw and the observation (through `meas_apAdv`);
* `cRoundA_measL`: the round of P° is measurable jointly in the position, the loss parameter, the advice, the mode,
  the draw, the noise and the dither (with the routine `apAdv v`);
* `mode_meas` (Lemma W-MEAS): P°'s mode before round `t` is measurable in `cσ d t`, and `zeta_meas`: its dither of
  round `t` in `cσ d (t + 1)`.
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

theorem gσ_le_cσ {t i : ℕ} (hi : i ∈ idxC d t) : gσ i ≤ cσ d t :=
  (le_iSup₂ (f := fun i (_ : i ∈ idxC d t) => gσ i) i hi).trans le_sup_left

theorem cIdx_mem_idxC_succ {t c : ℕ} (hc : c < d + 5) : cIdx d t c ∈ idxC d (t + 1) := by
  refine Or.inr ?_
  show 2 * (t * (d + 5) + c) < 2 * ((t + 1) * (d + 5))
  nlinarith

theorem meas_coord_c {t i : ℕ} (hi : i ∈ idxC d t) : Measurable[cσ d t] fun ω : WΩ => ω.1 i :=
  meas_coord i (gσ_le_cσ hi)

theorem meas_ξc (t : ℕ) : Measurable[cσ d (t + 1)] (ξc d t) :=
  measurable_pi_of fun c => meas_coord_c (cIdx_mem_idxC_succ (by omega))

theorem meas_ξg (t : ℕ) : Measurable[cσ d (t + 1)] (ξg d t) :=
  measurable_pi_of fun c => meas_coord_c (cIdx_mem_idxC_succ (by omega))

theorem meas_zc (t : ℕ) : Measurable[cσ d (t + 1)] (zc d t) := by
  refine measurable_pi_of fun k => ?_
  fin_cases k
  · exact meas_coord_c (cIdx_mem_idxC_succ (by omega))
  · exact meas_coord_c (cIdx_mem_idxC_succ (by omega))
  · exact meas_coord_c (cIdx_mem_idxC_succ (by omega))

theorem meas_noise_c (t : ℕ) : Measurable[cσ d (t + 1)] fun ω : WΩ => ω.2 t :=
  (meas_noise (t + 1) t (Nat.lt_succ_self t)).mono le_sup_right le_rfl

theorem Fσ_le (t : ℕ) : Fσ d t ≤ cσ d (t + 1) :=
  sup_le (sup_le ((cσ d).mono (Nat.le_succ t)) (meas_ξg t).comap_le) (meas_noise_c t).comap_le

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

/-! ## Lemma W-MEAS -/

section Run

variable {n : ℕ} {K : Set (E d)} (B : Run d n K) (δ : ℝ)

theorem pair_meas {m : MeasurableSpace WΩ} {t : ℕ} (hmode : Measurable[m] fun ω => B.mode δ t ω) :
    @Measurable WΩ (WΩ × Df2Mode d) m (m.prod inferInstance) fun ω => (ω, B.mode δ t ω) :=
  Measurable.prodMk (@measurable_id WΩ m) hmode

theorem cσ_le_Fσ (t : ℕ) : cσ d t ≤ Fσ d t := le_sup_left.trans le_sup_left

/-- The shift of round `t` on P°'s run is known at `F_t`, given the mode before round `t` is known at `cσ d t`. -/
theorem shR_meas (hB : BLMeas B) {t : ℕ} (hmode : Measurable[cσ d t] fun ω => B.mode δ t ω) :
    Measurable[Fσ d t] (B.shR δ t) :=
  (hB.sh t).comp (pair_meas B δ (hmode.mono (cσ_le_Fσ t) le_rfl))

/-- P°'s dither of round `t` is known after round `t`. -/
theorem zeta_meas (hB : BLMeas B) (hC : CoupLaw B.Coup) {t : ℕ}
    (hmode : Measurable[cσ d t] fun ω => B.mode δ t ω) :
    Measurable[cσ d (t + 1)] fun ω => B.zeta t ω (B.mode δ t ω) := by
  have hs := (shR_meas B δ hB hmode).mono (Fσ_le t) le_rfl
  exact hC.meas.comp (hs.fst.prodMk (hs.snd.prodMk (meas_zc t)))

/-- P°'s advice of round `t` is known after round `t`. -/
theorem adv_meas (hB : BLMeas B) {t : ℕ} (hmode : Measurable[cσ d t] fun ω => B.mode δ t ω) :
    Measurable[cσ d (t + 1)] fun ω => B.adv t ω (B.mode δ t ω) :=
  (hB.adv t).comp (pair_meas B δ (hmode.mono ((cσ d).mono (Nat.le_succ t)) le_rfl))

/-- Lemma W-MEAS: P°'s mode before round `t` is known before round `t`. -/
theorem mode_meas (hreg : Regime d n δ) (hKc : IsClosed K) (hKconv : Convex ℝ K) (hpos : Measurable[cσ d 0] B.pos)
    (hB : BLMeas B) (hC : CoupLaw B.Coup) : ∀ t, Measurable[cσ d t] fun ω => B.mode δ t ω := by
  obtain ⟨hd, hn, hδ0, hδ1, heps⟩ := hreg
  have H := rowHyp_of d n δ hd hn hδ0 hδ1 heps
  have hR := row_one_le_R _ d n H
  have hmw : 1 / (df2oPar d n δ).R ≤ df2Mw d := by rw [H.R]; exact inv_R_le_df2Mw d hd
  intro t
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    have hpos' : Measurable[cσ d (t + 1)] B.pos := hpos.mono ((cσ d).mono (Nat.zero_le _)) le_rfl
    have hm' : Measurable[cσ d (t + 1)] fun ω => B.mode δ t ω := ih.mono ((cσ d).mono (Nat.le_succ t)) le_rfl
    have hrest : Measurable[cσ d (t + 1)] fun ω =>
        (B.mode δ t ω, ξc d t ω, ω.2 t, B.zeta t ω (B.mode δ t ω)) :=
      hm'.prodMk ((meas_ξc t).prodMk ((meas_noise_c t).prodMk (zeta_meas B δ hB hC ih)))
    by_cases ht : t < n
    · have hft := measurable_fL (K := K) (L := B.F.L) (t := t) (fun l => (B.F.adm t ht l).1) (B.F.meas t ht)
      have hround := cRoundA_measL (n := n) (δ := δ) hKc hKconv hR hmw hft
      have hlam : Measurable[cσ d (t + 1)] (B.F.lam t) :=
        (B.F.lam_meas t ht).mono ((cσ d).mono (Nat.le_succ t)) le_rfl
      have htup : Measurable[cσ d (t + 1)] fun ω =>
          ((B.pos ω, B.F.lam t ω, B.adv t ω (B.mode δ t ω)),
            B.mode δ t ω, ξc d t ω, ω.2 t, B.zeta t ω (B.mode δ t ω)) :=
        (hpos'.prodMk (hlam.prodMk (adv_meas B δ hB ih))).prodMk hrest
      have h := measurable_snd.comp (hround.comp htup)
      convert h using 1
      funext ω
      simp only [Function.comp_def, Run.mode, Run.lossR, ht, ↓reduceIte]
    · have hft : Measurable fun p : Unit × E d => (fun (_ : Unit) (_ : E d) => (0 : ℝ)) p.1 p.2 := measurable_const
      have hround := cRoundA_measL (n := n) (δ := δ) (ft := fun (_ : Unit) (_ : E d) => (0 : ℝ)) hKc hKconv hR hmw hft
      have htup : Measurable[cσ d (t + 1)] fun ω =>
          ((B.pos ω, (), B.adv t ω (B.mode δ t ω)),
            B.mode δ t ω, ξc d t ω, ω.2 t, B.zeta t ω (B.mode δ t ω)) :=
        (hpos'.prodMk (measurable_const.prodMk (adv_meas B δ hB ih))).prodMk hrest
      have h := measurable_snd.comp (hround.comp htup)
      convert h using 1
      funext ω
      simp only [Function.comp_def, Run.mode, Run.lossR, ht, ↓reduceIte]
      rfl

end Run

end AdversarialBco.Bit.Cpl
