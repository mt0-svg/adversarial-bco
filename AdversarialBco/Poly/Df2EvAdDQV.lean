/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.Df2EvAdMeasV
public import AdversarialBco.Poly.Df2EvSIDQV

@[expose] public section

/-!
# The budget of DQ with an adapted parameter and an advice per round

`EvAd.df2EvDQPropAdV_holds : Df2EvDQPropAdV`, DF Lemma DQ on `Df2OnSetEAdV`: Lemma U on the state process `sigAdV`,
the increments of the path from `zSeq_eqAdV` and `shh_sqAdV`, and the path-level facts (`mean_HV`, `dq_varV`,
`dq_rangeV`, `dq_disc_pathV`, `dq_arith`).

The routine of round `s` is `apθ (ψ s ω)` (Df2SetEAdV.lean); no increment reads it, so the proof runs on the context
`ctxWV` with the process lemmas of Df2EvAdMeasV.lean.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal NNReal Matrix

namespace AdversarialBco.Poly.EvAd

open EvSI Layer2

/-! ## The budget of DQ -/

/-- DF Lemma DQ on setting (E) with an adapted parameter: `μ(G ∩ ¬DQ) ≤ δ_e/8`. -/
theorem df2EvDQPropAdV_holds : Df2EvDQPropAdV := by
  intro d n m δ hd hn hm1 hmn hδ0 hδ1 heps Θ _ V _ Kθ gθ apθ hbody hadm hap hmeas Ω m0 μ hμ 𝒢 θ ψ ξ e hθ hψ hK hE
  classical
  have rows := df2RowsHold d n δ hd hn hδ0 hδ1 heps
  have hde0 : 0 < (df2oPar d n δ).δe := rows.pos_de
  have hde1 : (df2oPar d n δ).δe < 1 := rows.de_lt
  have he0 : 0 < (df2oPar d n δ).eps := rows.pos_eps
  have hl0 : 0 < (df2oPar d n δ).lam := rows.pos_lam
  have hl1 : (df2oPar d n δ).lam < 1 := by have := rows.lam_le; linarith
  have hk0 : 0 ≤ (df2oPar d n δ).k0 := by rw [k0_def]; positivity
  have hR1 : 1 ≤ (df2oPar d n δ).R := rows.one_le_R
  have hRD := RD_pos hd hn rows
  have hM0 := M0_nonneg (df2oPar d n δ)
  obtain ⟨C, hCball, -, hCnet, hCcard⟩ := existsNet d (df2oPar d n δ).R ((df2oPar d n δ).δe ^ 4) (by linarith)
    (by positivity)
  have hU := lemmaU_setE (d := d) μ 𝒢 C m n hmn (sigAdV n δ Kθ gθ apθ θ ψ ξ e) ξ e
    (fun s hs => measurable_sigAdV n δ Kθ gθ apθ hmeas 𝒢 θ ψ hK ξ e hθ hψ hE.xi_meas hE.e_meas hs.le)
    hE.xi_meas hE.xi_law hE.xi_indep hE.e_meas hE.e_int hE.e_mean hE.e_exp
    (fun c s => aOf n δ Kθ gθ (M0 (df2oPar d n δ)) s (phiH n δ (fun st => WithLp.ofLp c - st.mu)))
    (fun c _ => bOf n δ Kθ (M0 (df2oPar d n δ)) (phiH n δ (fun st => WithLp.ofLp c - st.mu)))
    (fun c s hs => measurable_aOf n δ Kθ gθ apNone hmeas.none hs _ _
      (measurable_phiH n δ _ (measurable_const.sub ApMeas.measurable_st_mu)))
    (fun c s _ => measurable_bOf n δ Kθ gθ apNone hmeas.none _ _
      (measurable_phiH n δ _ (measurable_const.sub ApMeas.measurable_st_mu)))
    (fun c => kF d n δ (M0 (df2oPar d n δ)) * KphiH d n δ (M0 (df2oPar d n δ)) (WithLp.ofLp c)) 3
    (fun c => mul_nonneg (kF_nonneg n δ _ he0) (KphiH_nonneg hl0.le hk0 _))
    (fun c s hs x => (aOf_bOf_le n δ Kθ gθ hbody hadm he0 heps hl0.le hl1.le hM0 hs _ _
      (KphiH_nonneg hl0.le hk0 _) (fun st hst z => phiH_growth hM0 hl0.le hk0 _ hst z) x).1)
    (fun c s hs x => (aOf_bOf_le n δ Kθ gθ hbody hadm he0 heps hl0.le hl1.le hM0 hs _ _
      (KphiH_nonneg hl0.le hk0 _) (fun st hst z => phiH_growth hM0 hl0.le hk0 _ hst z) x).2)
    (RD d n δ)⁻¹ ((df2oPar d n δ).δe / 8) (inv_pos.2 hRD) (by positivity) (by linarith)
    (fun _ _ _ => VD d n δ) (fun _ _ _ => RD d n δ)
  refine le_trans (measure_mono ?_) (hU.trans (le_of_eq (by congr 1; ring)))
  intro ω hω
  rw [Set.mem_ofPred_eq] at hω
  obtain ⟨hG, hDQ⟩ := hω
  have H : DetBase (df2CtxAtF d n δ (Kθ (θ 0 ω)) (fun s => apθ (ψ s ω))) δ ⟨fun s => gθ s (θ s ω), fun s => e s ω, fun s => ξ s ω⟩ m :=
    EvGY.detBaseV SIF.df2SIFacts_holds hd hn hδ0 hδ1 heps hm1 hmn (hbody (θ 0 ω)) (fun s => hap (ψ s ω)) (admAd Kθ gθ hadm θ hK ω)
  unfold Df2Ctx.EvDQ at hDQ
  push Not at hDQ
  obtain ⟨t, ht, y, hyR, hyS, hlt⟩ := hDQ
  -- the point of the net
  have hyball : (WithLp.toLp 2 y : E d) ∈ Metric.closedBall 0 (df2oPar d n δ).R := by
    rw [mem_closedBall_zero_iff, norm_toLp]; exact hyR
  have hyR2 : y ⬝ᵥ y ≤ (df2oPar d n δ).R ^ 2 := by
    have h1 : Real.sqrt (y ⬝ᵥ y) ≤ (df2oPar d n δ).R := hyR
    rw [← Real.sq_sqrt (dot_self_nonneg' y)]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
  obtain ⟨c, hcC, hdist⟩ := hCnet _ hyball
  set c' : Fin d → ℝ := WithLp.ofLp c with hc'
  have hyc : Real.sqrt ((y - c') ⬝ᵥ (y - c')) ≤ (df2oPar d n δ).δe ^ 4 := by
    rw [← norm_toLp, WithLp.toLp_sub, hc', WithLp.toLp_ofLp, ← dist_eq_norm]; exact hdist
  have hc8 : (c' - y) ⬝ᵥ (c' - y) ≤ (df2oPar d n δ).δe ^ 8 := by
    have e1 : (c' - y) ⬝ᵥ (c' - y) = (y - c') ⬝ᵥ (y - c') := by
      rw [← neg_sub y c', neg_dotProduct, dotProduct_neg, neg_neg]
    rw [e1, ← Real.sq_sqrt (dot_self_nonneg' (y - c')), show (8 : ℕ) = 4 * 2 from rfl, pow_mul]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hyc 2
  have hcR : c' ⬝ᵥ c' ≤ (df2oPar d n δ).R ^ 2 := by
    have h1 : Real.sqrt (c' ⬝ᵥ c') ≤ (df2oPar d n δ).R := by
      rw [← norm_toLp, hc', WithLp.toLp_ofLp]; exact mem_closedBall_zero_iff.1 (hCball hcC)
    rw [← Real.sq_sqrt (dot_self_nonneg' c')]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
  have htau := EvGY.tau_lt (df2CtxAtF d n δ (Kθ (θ 0 ω)) (fun s => apθ (ψ s ω))) ⟨fun s => gθ s (θ s ω), fun s => e s ω, fun s => ξ s ω⟩ hm1
  have htm : t < m := lt_of_le_of_lt ht htau
  -- each increment at `c` up to `t`
  have hinc : ∀ s ≤ t, zSeq m
      (fun c s => aOf n δ Kθ gθ (M0 (df2oPar d n δ)) s (phiH n δ (fun st => WithLp.ofLp c - st.mu)))
      (fun c _ => bOf n δ Kθ (M0 (df2oPar d n δ)) (phiH n δ (fun st => WithLp.ofLp c - st.mu)))
      (sigAdV n δ Kθ gθ apθ θ ψ ξ e) ξ e c s ω =
      (df2CtxAtF d n δ (Kθ (θ 0 ω)) (fun s => apθ (ψ s ω))).Y ⟨fun s => gθ s (θ s ω), fun s => e s ω, fun s => ξ s ω⟩ s *
          phiH n δ (fun st => c' - st.mu)
            ((df2CtxAtF d n δ (Kθ (θ 0 ω)) (fun s => apθ (ψ s ω))).st ⟨fun s => gθ s (θ s ω), fun s => e s ω, fun s => ξ s ω⟩ s) (ξ s ω) -
        df2Sq ((df2CtxAtF d n δ (Kθ (θ 0 ω)) (fun s => apθ (ψ s ω))).sHess ⟨fun s => gθ s (θ s ω), fun s => e s ω, fun s => ξ s ω⟩ s)
          (c' - ((df2CtxAtF d n δ (Kθ (θ 0 ω)) (fun s => apθ (ψ s ω))).st ⟨fun s => gθ s (θ s ω), fun s => e s ω, fun s => ξ s ω⟩ s).mu) := by
    intro s hs
    have hs' := hs.trans ht
    have hst := stB_of H (H.stInv_le_tau s hs')
    rw [zSeq_eqAdV n δ Kθ gθ apθ θ ψ ξ e ω hK (M0 (df2oPar d n δ)) (fun c => phiH n δ (fun st => WithLp.ofLp c - st.mu)) c
      (lt_of_le_of_lt hs' htau) hst]
    have hm := mean_HV H hs' (fun st => c' - st.mu)
    exact congrArg (fun r => _ - r) hm
  rw [Set.mem_ofPred_eq]
  refine ⟨c, hcC, t, htm, VD_nonneg d n δ, by rw [inv_mul_cancel₀ hRD.ne'], ?_, ?_, ?_⟩
  · -- the variance
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun s hs => ?_)) (dq_varV H ht hyS hc8)
    have hs' := (Nat.lt_succ_iff.1 (Finset.mem_range.1 hs)).trans ht
    have hst := stB_of H (H.stInv_le_tau s hs')
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    refine (sq_aOf_bOf_eq Kθ gθ _ s _ (sigAdV n δ Kθ gθ apθ θ ψ ξ e s ω, z) hst).trans ?_
    rw [fF_sigAdV n δ Kθ gθ apθ θ ψ ξ e ω s hK z, fP_sigAdV n δ Kθ gθ apθ θ ψ ξ e ω s hK z]
    rfl
  · -- the range
    intro s hs
    rw [hinc s hs]
    exact dq_rangeV H hG (hs.trans ht) (lq_qV H ht hyS hc8 hs)
  · -- the deviation
    have hsum : ∑ s ∈ Finset.range (t + 1), zSeq m
        (fun c s => aOf n δ Kθ gθ (M0 (df2oPar d n δ)) s (phiH n δ (fun st => WithLp.ofLp c - st.mu)))
        (fun c _ => bOf n δ Kθ (M0 (df2oPar d n δ)) (phiH n δ (fun st => WithLp.ofLp c - st.mu)))
        (sigAdV n δ Kθ gθ apθ θ ψ ξ e) ξ e c s ω =
        (df2CtxAtF d n δ (Kθ (θ 0 ω)) (fun s => apθ (ψ s ω))).GG ⟨fun s => gθ s (θ s ω), fun s => e s ω, fun s => ξ s ω⟩ t c' := by
      unfold Df2Ctx.GG
      refine Finset.sum_congr rfl fun s hs => ?_
      rw [hinc s (Nat.lt_succ_iff.1 (Finset.mem_range.1 hs)), df2Sq_sub]
      have hg := shh_sqAdV n δ Kθ gθ apθ θ ψ ξ e ω s (fun st => c' - st.mu)
      exact congrArg (fun r => r - _) hg.symm
    rw [hsum]
    have hdisc := dq_disc_pathV H hG ht hyR2 hcR hyc
    have ha := dq_arith hd hn rows C.card (by
      obtain ⟨c0, hc0⟩ : C.Nonempty := ⟨c, hcC⟩
      exact_mod_cast Finset.card_pos.2 ⟨c0, hc0⟩) hCcard
    have hab := abs_sub_abs_le_abs_sub
      ((df2CtxAtF d n δ (Kθ (θ 0 ω)) (fun s => apθ (ψ s ω))).GG ⟨fun s => gθ s (θ s ω), fun s => e s ω, fun s => ξ s ω⟩ t y)
      ((df2CtxAtF d n δ (Kθ (θ 0 ω)) (fun s => apθ (ψ s ω))).GG ⟨fun s => gθ s (θ s ω), fun s => e s ω, fun s => ξ s ω⟩ t c')
    have hlt' : df2Bn (df2oPar d n δ) d n / ((df2oPar d n δ).Le * (df2oPar d n δ).lam ^ 2) <
        |(df2CtxAtF d n δ (Kθ (θ 0 ω)) (fun s => apθ (ψ s ω))).GG ⟨fun s => gθ s (θ s ω), fun s => e s ω, fun s => ξ s ω⟩ t y| := hlt
    show _ < _
    linarith

end AdversarialBco.Poly.EvAd
