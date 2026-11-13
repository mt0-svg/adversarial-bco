/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.Df2EvAdMeasV
public import AdversarialBco.Poly.Df2EvSILQV

@[expose] public section

/-!
# The budget of LQ with an adapted parameter and an advice per round

`EvAd.df2EvLQPropAdV_holds : Df2EvLQPropAdV`, Lemma LQ on `Df2OnSetEAdV`: Lemma U on the state process
`sigAdV s = (θ s, st_s)`, measurable in `𝒢 s` (`measurable_sigAdV`); the increments are those of the path of the
losses `gθ s (θ s ω)` on the body at `θ 0 ω` (`zSeq_eqAdV`), with the path-level facts (`mean_LV`, `lq_varV`,
`lq_rangeV`, `lq_disc_pathV`, `lq_arith`).

The routine of round `s` is `apθ (ψ s ω)` (Df2SetEAdV.lean); no increment reads it, so the proof runs on the context
`ctxWV` with the process lemmas of Df2EvAdMeasV.lean.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal NNReal Matrix

namespace AdversarialBco.Poly.EvAd

open EvSI Layer2

/-! ## The budget of LQ -/

/-- SI Lemma LQ on setting (E) with an adapted parameter: `μ(G ∩ ¬LQ) ≤ δ_e/21`. -/
theorem df2EvLQPropAdV_holds : Df2EvLQPropAdV := by
  intro d n m δ hd hn hm1 hmn hδ0 hδ1 heps Θ _ V _ Kθ gθ apθ hbody hadm hap hmeas Ω m0 μ hμ 𝒢 θ ψ ξ e hθ hψ hK hE
  classical
  have rows := df2RowsHold d n δ hd hn hδ0 hδ1 heps
  have hde0 : 0 < (df2oPar d n δ).δe := rows.pos_de
  have hde1 : (df2oPar d n δ).δe < 1 := rows.de_lt
  have he0 : 0 < (df2oPar d n δ).eps := rows.pos_eps
  have hl0 : 0 < (df2oPar d n δ).lam := rows.pos_lam
  have hl1 : (df2oPar d n δ).lam < 1 := by have := rows.lam_le; linarith
  have hR1 : 1 ≤ (df2oPar d n δ).R := rows.one_le_R
  have hRL := RL_pos hd hn rows
  have hM0 := M0_nonneg (df2oPar d n δ)
  obtain ⟨C, hCball, -, hCnet, hCcard⟩ := existsNet d (df2oPar d n δ).R ((df2oPar d n δ).δe ^ 4) (by linarith)
    (by positivity)
  have hU := lemmaU_setE (d := d) μ 𝒢 C m n hmn (sigAdV n δ Kθ gθ apθ θ ψ ξ e) ξ e
    (fun s hs => measurable_sigAdV n δ Kθ gθ apθ hmeas 𝒢 θ ψ hK ξ e hθ hψ hE.xi_meas hE.e_meas hs.le)
    hE.xi_meas hE.xi_law hE.xi_indep hE.e_meas hE.e_int hE.e_mean hE.e_exp
    (fun c s => aOf n δ Kθ gθ (M0 (df2oPar d n δ)) s (phiL n δ (WithLp.ofLp c)))
    (fun c _ => bOf n δ Kθ (M0 (df2oPar d n δ)) (phiL n δ (WithLp.ofLp c)))
    (fun c s hs => measurable_aOf n δ Kθ gθ apNone hmeas.none hs _ _ (measurable_phiL n δ _))
    (fun c s _ => measurable_bOf n δ Kθ gθ apNone hmeas.none _ _ (measurable_phiL n δ _))
    (fun c => kF d n δ (M0 (df2oPar d n δ)) * KphiL d n δ (M0 (df2oPar d n δ)) (WithLp.ofLp c)) 3
    (fun c => mul_nonneg (kF_nonneg n δ _ he0) (KphiL_nonneg hM0 hl1 _))
    (fun c s hs x => (aOf_bOf_le n δ Kθ gθ hbody hadm he0 heps hl0.le hl1.le hM0 hs _ _
      (KphiL_nonneg hM0 hl1 _) (fun st hst z => phiL_growth hM0 hl1 _ hst z) x).1)
    (fun c s hs x => (aOf_bOf_le n δ Kθ gθ hbody hadm he0 heps hl0.le hl1.le hM0 hs _ _
      (KphiL_nonneg hM0 hl1 _) (fun st hst z => phiL_growth hM0 hl1 _ hst z) x).2)
    (RL d n δ)⁻¹ ((df2oPar d n δ).δe / 21) (inv_pos.2 hRL) (by positivity) (by linarith)
    (fun _ _ _ => VL d n δ) (fun _ _ _ => RL d n δ)
  refine le_trans (measure_mono ?_) (hU.trans (le_of_eq (by congr 1; ring)))
  intro ω hω
  rw [Set.mem_ofPred_eq] at hω
  obtain ⟨hG, hLQ⟩ := hω
  have H : DetBase (df2CtxAtF d n δ (Kθ (θ 0 ω)) (fun s => apθ (ψ s ω))) δ ⟨fun s => gθ s (θ s ω), fun s => e s ω, fun s => ξ s ω⟩ m :=
    EvGY.detBaseV SIF.df2SIFacts_holds hd hn hδ0 hδ1 heps hm1 hmn (hbody (θ 0 ω)) (fun s => hap (ψ s ω)) (admAd Kθ gθ hadm θ hK ω)
  unfold Df2Ctx.EvLQ at hLQ
  push Not at hLQ
  obtain ⟨t, ht, y, hyR, hyS, hlt⟩ := hLQ
  -- the point of the net
  have hyball : (WithLp.toLp 2 y : E d) ∈ Metric.closedBall 0 (df2oPar d n δ).R := by
    rw [mem_closedBall_zero_iff, norm_toLp]; exact hyR
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
  have hinc : ∀ s ≤ t, zSeq m (fun c s => aOf n δ Kθ gθ (M0 (df2oPar d n δ)) s (phiL n δ (WithLp.ofLp c)))
      (fun c _ => bOf n δ Kθ (M0 (df2oPar d n δ)) (phiL n δ (WithLp.ofLp c))) (sigAdV n δ Kθ gθ apθ θ ψ ξ e) ξ e c s ω =
      (df2CtxAtF d n δ (Kθ (θ 0 ω)) (fun s => apθ (ψ s ω))).Y ⟨fun s => gθ s (θ s ω), fun s => e s ω, fun s => ξ s ω⟩ s *
          phiL n δ c' ((df2CtxAtF d n δ (Kθ (θ 0 ω)) (fun s => apθ (ψ s ω))).st ⟨fun s => gθ s (θ s ω), fun s => e s ω, fun s => ξ s ω⟩ s)
            (ξ s ω) -
        (df2CtxAtF d n δ (Kθ (θ 0 ω)) (fun s => apθ (ψ s ω))).sGrad ⟨fun s => gθ s (θ s ω), fun s => e s ω, fun s => ξ s ω⟩ s ⬝ᵥ
          (c' - ((df2CtxAtF d n δ (Kθ (θ 0 ω)) (fun s => apθ (ψ s ω))).st ⟨fun s => gθ s (θ s ω), fun s => e s ω, fun s => ξ s ω⟩ s).mu) := by
    intro s hs
    have hs' := hs.trans ht
    have hst := stB_of H (H.stInv_le_tau s hs')
    rw [zSeq_eqAdV n δ Kθ gθ apθ θ ψ ξ e ω hK (M0 (df2oPar d n δ)) (fun c => phiL n δ (WithLp.ofLp c)) c
      (lt_of_le_of_lt hs' htau) hst]
    have hm := mean_LV H hs' c'
    exact congrArg (fun r => _ - r) hm
  rw [Set.mem_ofPred_eq]
  refine ⟨c, hcC, t, htm, VL_nonneg hd hn rows, by rw [inv_mul_cancel₀ hRL.ne'], ?_, ?_, ?_⟩
  · -- the variance
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun s hs => ?_)) (lq_varV H ht hyS hc8)
    have hs' := (Nat.lt_succ_iff.1 (Finset.mem_range.1 hs)).trans ht
    have hst := stB_of H (H.stInv_le_tau s hs')
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    refine (sq_aOf_bOf_eq Kθ gθ _ s _ (sigAdV n δ Kθ gθ apθ θ ψ ξ e s ω, z) hst).trans ?_
    rw [fF_sigAdV n δ Kθ gθ apθ θ ψ ξ e ω s hK z, fP_sigAdV n δ Kθ gθ apθ θ ψ ξ e ω s hK z]
    rfl
  · -- the range
    intro s hs
    rw [hinc s hs]
    exact lq_rangeV H hG (hs.trans ht) hcR (lq_qV H ht hyS hc8 hs)
  · -- the deviation
    have hsum : ∑ s ∈ Finset.range (t + 1), zSeq m
        (fun c s => aOf n δ Kθ gθ (M0 (df2oPar d n δ)) s (phiL n δ (WithLp.ofLp c)))
        (fun c _ => bOf n δ Kθ (M0 (df2oPar d n δ)) (phiL n δ (WithLp.ofLp c))) (sigAdV n δ Kθ gθ apθ θ ψ ξ e) ξ e c s ω =
        ∑ s ∈ Finset.range (t + 1),
          ((df2CtxAtF d n δ (Kθ (θ 0 ω)) (fun s => apθ (ψ s ω))).ghat ⟨fun s => gθ s (θ s ω), fun s => e s ω, fun s => ξ s ω⟩ s -
            (df2CtxAtF d n δ (Kθ (θ 0 ω)) (fun s => apθ (ψ s ω))).sGrad ⟨fun s => gθ s (θ s ω), fun s => e s ω, fun s => ξ s ω⟩ s) ⬝ᵥ
          (c' - ((df2CtxAtF d n δ (Kθ (θ 0 ω)) (fun s => apθ (ψ s ω))).st ⟨fun s => gθ s (θ s ω), fun s => e s ω, fun s => ξ s ω⟩ s).mu) := by
      refine Finset.sum_congr rfl fun s hs => ?_
      rw [hinc s (Nat.lt_succ_iff.1 (Finset.mem_range.1 hs)), sub_dotProduct]
      have hg := ghat_dotAdV n δ Kθ gθ apθ θ ψ ξ e ω s c'
      exact congrArg (fun r => r - _) hg.symm
    rw [hsum]
    have hdisc := lq_disc_pathV H hG ht hyc
    have ha := lq_arith hd hn rows C.card (by
      obtain ⟨c0, hc0⟩ : C.Nonempty := ⟨c, hcC⟩
      exact_mod_cast Finset.card_pos.2 ⟨c0, hc0⟩) hCcard
    have hab := abs_sub_abs_le_abs_sub
      (∑ s ∈ Finset.range (t + 1),
          ((df2CtxAtF d n δ (Kθ (θ 0 ω)) (fun s => apθ (ψ s ω))).ghat ⟨fun s => gθ s (θ s ω), fun s => e s ω, fun s => ξ s ω⟩ s -
            (df2CtxAtF d n δ (Kθ (θ 0 ω)) (fun s => apθ (ψ s ω))).sGrad ⟨fun s => gθ s (θ s ω), fun s => e s ω, fun s => ξ s ω⟩ s) ⬝ᵥ
          (y - ((df2CtxAtF d n δ (Kθ (θ 0 ω)) (fun s => apθ (ψ s ω))).st ⟨fun s => gθ s (θ s ω), fun s => e s ω, fun s => ξ s ω⟩ s).mu))
      (∑ s ∈ Finset.range (t + 1),
          ((df2CtxAtF d n δ (Kθ (θ 0 ω)) (fun s => apθ (ψ s ω))).ghat ⟨fun s => gθ s (θ s ω), fun s => e s ω, fun s => ξ s ω⟩ s -
            (df2CtxAtF d n δ (Kθ (θ 0 ω)) (fun s => apθ (ψ s ω))).sGrad ⟨fun s => gθ s (θ s ω), fun s => e s ω, fun s => ξ s ω⟩ s) ⬝ᵥ
          (c' - ((df2CtxAtF d n δ (Kθ (θ 0 ω)) (fun s => apθ (ψ s ω))).st ⟨fun s => gθ s (θ s ω), fun s => e s ω, fun s => ξ s ω⟩ s).mu))
    have hlt' : df2B1 (df2oPar d n δ) d n < |∑ s ∈ Finset.range (t + 1),
          ((df2CtxAtF d n δ (Kθ (θ 0 ω)) (fun s => apθ (ψ s ω))).ghat ⟨fun s => gθ s (θ s ω), fun s => e s ω, fun s => ξ s ω⟩ s -
            (df2CtxAtF d n δ (Kθ (θ 0 ω)) (fun s => apθ (ψ s ω))).sGrad ⟨fun s => gθ s (θ s ω), fun s => e s ω, fun s => ξ s ω⟩ s) ⬝ᵥ
          (y - ((df2CtxAtF d n δ (Kθ (θ 0 ω)) (fun s => apθ (ψ s ω))).st ⟨fun s => gθ s (θ s ω), fun s => e s ω, fun s => ξ s ω⟩ s).mu)| :=
      hlt
    show _ < _
    linarith

end AdversarialBco.Poly.EvAd
