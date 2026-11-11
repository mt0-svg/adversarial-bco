/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.Df2EvAdMeas
public import AdversarialBco.Poly.Df2EvSILQ

@[expose] public section

/-!
# The budget of LQ with an adapted parameter

`EvAd.df2EvLQPropAd_holds : Df2EvLQPropAd`, the proof of `EvSI.df2EvLQProp_holds` (Df2EvSILQ.lean) on
`Df2OnSetEAd`: Lemma U on the state process `sigAd s = (θ s, st_s)`, measurable in `𝒢 s` (`measurable_sigAd`); the
increments are those of the path of the losses `gθ s (θ s ω)` on the body at `θ 0 ω` (`zSeq_eqAd`), and the path-level
facts (`mean_L`, `lq_var`, `lq_range`, `lq_disc_path`, `lq_arith`) are used as they are.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal NNReal Matrix

namespace AdversarialBco.Poly.EvAd

open EvSI Layer2

/-! ## The budget of LQ -/

/-- Lemma LQ on setting (E) with an adapted parameter: `μ(G ∩ ¬LQ) ≤ δ_e/21`. -/
theorem df2EvLQPropAd_holds : Df2EvLQPropAd := by
  intro d n m δ hd hn hm1 hmn hδ0 hδ1 heps Θ _ Kθ gθ ap hbody hadm hap hmeas Ω m0 μ hμ 𝒢 θ ξ e hθ hK hE
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
  have hU := lemmaU_setE (d := d) μ 𝒢 C m n hmn (sigAd n δ Kθ gθ ap θ ξ e) ξ e
    (fun s hs => measurable_sigAd n δ Kθ gθ ap hmeas 𝒢 θ hK ξ e hθ hE.xi_meas hE.e_meas hs.le)
    hE.xi_meas hE.xi_law hE.xi_indep hE.e_meas hE.e_int hE.e_mean hE.e_exp
    (fun c s => aOf n δ Kθ gθ (M0 (df2oPar d n δ)) s (phiL n δ (WithLp.ofLp c)))
    (fun c _ => bOf n δ Kθ (M0 (df2oPar d n δ)) (phiL n δ (WithLp.ofLp c)))
    (fun c s hs => measurable_aOf n δ Kθ gθ ap hmeas hs _ _ (measurable_phiL n δ _))
    (fun c s _ => measurable_bOf n δ Kθ gθ ap hmeas _ _ (measurable_phiL n δ _))
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
  have H : DetBase (df2CtxAt d n δ (Kθ (θ 0 ω)) ap) δ ⟨fun s => gθ s (θ s ω), fun s => e s ω, fun s => ξ s ω⟩ m :=
    EvGY.detBase SIF.df2SIFacts_holds hd hn hδ0 hδ1 heps hm1 hmn (hbody (θ 0 ω)) hap (admAd Kθ gθ hadm θ hK ω)
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
  have htau := EvGY.tau_lt (df2CtxAt d n δ (Kθ (θ 0 ω)) ap) ⟨fun s => gθ s (θ s ω), fun s => e s ω, fun s => ξ s ω⟩ hm1
  have htm : t < m := lt_of_le_of_lt ht htau
  -- each increment at `c` up to `t`
  have hinc : ∀ s ≤ t, zSeq m (fun c s => aOf n δ Kθ gθ (M0 (df2oPar d n δ)) s (phiL n δ (WithLp.ofLp c)))
      (fun c _ => bOf n δ Kθ (M0 (df2oPar d n δ)) (phiL n δ (WithLp.ofLp c))) (sigAd n δ Kθ gθ ap θ ξ e) ξ e c s ω =
      (df2CtxAt d n δ (Kθ (θ 0 ω)) ap).Y ⟨fun s => gθ s (θ s ω), fun s => e s ω, fun s => ξ s ω⟩ s *
          phiL n δ c' ((df2CtxAt d n δ (Kθ (θ 0 ω)) ap).st ⟨fun s => gθ s (θ s ω), fun s => e s ω, fun s => ξ s ω⟩ s)
            (ξ s ω) -
        (df2CtxAt d n δ (Kθ (θ 0 ω)) ap).sGrad ⟨fun s => gθ s (θ s ω), fun s => e s ω, fun s => ξ s ω⟩ s ⬝ᵥ
          (c' - ((df2CtxAt d n δ (Kθ (θ 0 ω)) ap).st ⟨fun s => gθ s (θ s ω), fun s => e s ω, fun s => ξ s ω⟩ s).mu) := by
    intro s hs
    have hs' := hs.trans ht
    have hst := stB_of H (H.stInv_le_tau s hs')
    rw [zSeq_eqAd n δ Kθ gθ ap θ ξ e ω hK (M0 (df2oPar d n δ)) (fun c => phiL n δ (WithLp.ofLp c)) c
      (lt_of_le_of_lt hs' htau) hst]
    have hm := mean_L H hs' c'
    exact congrArg (fun r => _ - r) hm
  rw [Set.mem_ofPred_eq]
  refine ⟨c, hcC, t, htm, VL_nonneg hd hn rows, by rw [inv_mul_cancel₀ hRL.ne'], ?_, ?_, ?_⟩
  · -- the variance
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun s hs => ?_)) (lq_var H ht hyS hc8)
    have hs' := (Nat.lt_succ_iff.1 (Finset.mem_range.1 hs)).trans ht
    have hst := stB_of H (H.stInv_le_tau s hs')
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    refine (sq_aOf_bOf_eq Kθ gθ _ s _ (sigAd n δ Kθ gθ ap θ ξ e s ω, z) hst).trans ?_
    rw [fF_sigAd n δ Kθ gθ ap θ ξ e ω s hK z, fP_sigAd n δ Kθ gθ ap θ ξ e ω s hK z]
    rfl
  · -- the range
    intro s hs
    rw [hinc s hs]
    exact lq_range H hG (hs.trans ht) hcR (lq_q H ht hyS hc8 hs)
  · -- the deviation
    have hsum : ∑ s ∈ Finset.range (t + 1), zSeq m
        (fun c s => aOf n δ Kθ gθ (M0 (df2oPar d n δ)) s (phiL n δ (WithLp.ofLp c)))
        (fun c _ => bOf n δ Kθ (M0 (df2oPar d n δ)) (phiL n δ (WithLp.ofLp c))) (sigAd n δ Kθ gθ ap θ ξ e) ξ e c s ω =
        ∑ s ∈ Finset.range (t + 1),
          ((df2CtxAt d n δ (Kθ (θ 0 ω)) ap).ghat ⟨fun s => gθ s (θ s ω), fun s => e s ω, fun s => ξ s ω⟩ s -
            (df2CtxAt d n δ (Kθ (θ 0 ω)) ap).sGrad ⟨fun s => gθ s (θ s ω), fun s => e s ω, fun s => ξ s ω⟩ s) ⬝ᵥ
          (c' - ((df2CtxAt d n δ (Kθ (θ 0 ω)) ap).st ⟨fun s => gθ s (θ s ω), fun s => e s ω, fun s => ξ s ω⟩ s).mu) := by
      refine Finset.sum_congr rfl fun s hs => ?_
      rw [hinc s (Nat.lt_succ_iff.1 (Finset.mem_range.1 hs)), sub_dotProduct]
      have hg := ghat_dotAd n δ Kθ gθ ap θ ξ e ω s c'
      exact congrArg (fun r => r - _) hg.symm
    rw [hsum]
    have hdisc := lq_disc_path H hG ht hyc
    have ha := lq_arith hd hn rows C.card (by
      obtain ⟨c0, hc0⟩ : C.Nonempty := ⟨c, hcC⟩
      exact_mod_cast Finset.card_pos.2 ⟨c0, hc0⟩) hCcard
    have hab := abs_sub_abs_le_abs_sub
      (∑ s ∈ Finset.range (t + 1),
          ((df2CtxAt d n δ (Kθ (θ 0 ω)) ap).ghat ⟨fun s => gθ s (θ s ω), fun s => e s ω, fun s => ξ s ω⟩ s -
            (df2CtxAt d n δ (Kθ (θ 0 ω)) ap).sGrad ⟨fun s => gθ s (θ s ω), fun s => e s ω, fun s => ξ s ω⟩ s) ⬝ᵥ
          (y - ((df2CtxAt d n δ (Kθ (θ 0 ω)) ap).st ⟨fun s => gθ s (θ s ω), fun s => e s ω, fun s => ξ s ω⟩ s).mu))
      (∑ s ∈ Finset.range (t + 1),
          ((df2CtxAt d n δ (Kθ (θ 0 ω)) ap).ghat ⟨fun s => gθ s (θ s ω), fun s => e s ω, fun s => ξ s ω⟩ s -
            (df2CtxAt d n δ (Kθ (θ 0 ω)) ap).sGrad ⟨fun s => gθ s (θ s ω), fun s => e s ω, fun s => ξ s ω⟩ s) ⬝ᵥ
          (c' - ((df2CtxAt d n δ (Kθ (θ 0 ω)) ap).st ⟨fun s => gθ s (θ s ω), fun s => e s ω, fun s => ξ s ω⟩ s).mu))
    have hlt' : df2B1 (df2oPar d n δ) d n < |∑ s ∈ Finset.range (t + 1),
          ((df2CtxAt d n δ (Kθ (θ 0 ω)) ap).ghat ⟨fun s => gθ s (θ s ω), fun s => e s ω, fun s => ξ s ω⟩ s -
            (df2CtxAt d n δ (Kθ (θ 0 ω)) ap).sGrad ⟨fun s => gθ s (θ s ω), fun s => e s ω, fun s => ξ s ω⟩ s) ⬝ᵥ
          (y - ((df2CtxAt d n δ (Kθ (θ 0 ω)) ap).st ⟨fun s => gθ s (θ s ω), fun s => e s ω, fun s => ξ s ω⟩ s).mu)| :=
      hlt
    show _ < _
    linarith

end AdversarialBco.Poly.EvAd
