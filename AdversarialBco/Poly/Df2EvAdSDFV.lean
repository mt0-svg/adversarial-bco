/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.Df2EvAdMeasV
public import AdversarialBco.Poly.Df2EvSISDFV

@[expose] public section

/-!
# The budget of S-DF with an adapted parameter and an advice per round

`EvAd.df2EvSDFPropAdV_of : Df2SIFacts → Df2EvSDFPropAdV` and `EvAd.df2EvSDFPropAdV_holds`, Lemma S-DF on
`Df2OnSetEAdV`: Lemma U on the state process `sigAdV` over the net of unit directions, the increments of the path
from `zSeq_pathAdV`, with the path-level facts and the arithmetic of Df2EvSISDF.lean.

The routine of round `s` is `apθ (ψ s ω)` (Df2SetEAdV.lean); no increment reads it, so the proof runs on the context
`ctxWV` with the process lemmas of Df2EvAdMeasV.lean.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal NNReal Matrix

namespace AdversarialBco.Poly.EvAd

open EvSI EvSI.SDF Layer2

variable {d : ℕ}

/-! ## The increments on the path -/

/-- Up to `τ`, the increment of the net point `c` is `cᵀ (ŝ''_s - s''_s(μ_s)) c`, adapted parameter. -/
theorem zSeq_pathAdV (n : ℕ) (δ : ℝ) {Θ : Type} (Kθ : Θ → Set (E d)) (gθ : ℕ → Θ → E d → ℝ) {V : Type} [MeasurableSpace V] (apθ : V → ApFun d)
    {Ω : Type} (θ : ℕ → Ω → Θ) (ψ : ℕ → Ω → V) (ξ : ℕ → Ω → Fin d → ℝ) (e : ℕ → Ω → ℝ) {m : ℕ} (ω : Ω)
    (hK : ∀ s ω, Kθ (θ s ω) = Kθ (θ 0 ω))
    (H : DetBase (EvGY.ctxWV n δ Kθ apθ (θ 0) ψ ω) δ (pathWAd gθ θ ξ e ω) m) (c : E d) {s : ℕ}
    (hs : s ≤ (EvGY.ctxWV n δ Kθ apθ (θ 0) ψ ω).tau (pathWAd gθ θ ξ e ω) m) :
    zSeq m (fun c s => aOf n δ Kθ gθ (M0 (df2oPar d n δ)) s (phiC n δ c))
        (fun c _ => bOf n δ Kθ (M0 (df2oPar d n δ)) (phiC n δ c)) (sigAdV n δ Kθ gθ apθ θ ψ ξ e) ξ e c s ω =
      df2Sq ((EvGY.ctxWV n δ Kθ apθ (θ 0) ψ ω).shh (pathWAd gθ θ ξ e ω) s) (WithLp.ofLp c) -
        df2Sq ((EvGY.ctxWV n δ Kθ apθ (θ 0) ψ ω).sHess (pathWAd gθ θ ξ e ω) s) (WithLp.ofLp c) := by
  have hI := H.stInv_le_tau s hs
  have hst : stB (M0 (df2oPar d n δ)) (sigAdV n δ Kθ gθ apθ θ ψ ξ e s ω).2 := stB_of H hI
  rw [zSeq_eqAdV n δ Kθ gθ apθ θ ψ ξ e ω hK (M0 (df2oPar d n δ)) (phiC n δ) c (H.le_tau_lt hs) hst]
  have h1 := shh_sqAdV n δ Kθ gθ apθ θ ψ ξ e ω s (fun _ => WithLp.ofLp c)
  have h2 := mean_HV H hs (fun _ => WithLp.ofLp c)
  rw [h1]
  congr 1

/-! ## The budget -/

/-- The budget of S-DF with an adapted parameter: on every instance, G holds and S-DF fails with probability at
most `δ_e/7`. -/
theorem df2EvSDFPropAdV_of (hSI : Df2SIFacts) : Df2EvSDFPropAdV := by
  intro d n m δ hd hn hm1 hmn hδ0 hδ1 heps Θ _ V _ Kθ gθ apθ hbody hadm hap hmeas Ω m0 μ hμ 𝒢 θ ψ ξ e hθ hψ hK hE
  have hrows : Df2Rows (df2oPar d n δ) d n := df2RowsHold d n δ hd hn hδ0 hδ1 heps
  set p := df2oPar d n δ with hp
  have hde : 0 < p.δe := hrows.pos_de
  have he0 : 0 < p.eps := hrows.pos_eps
  have hl0 : 0 < p.lam := hrows.pos_lam
  have hl2 : p.lam ≤ 1 / 2 := hrows.lam_le
  have hl1 : p.lam ≤ 1 := by linarith
  have hδ12 : p.δe ≤ 1 / 2 := by
    have h8 := hrows.c8
    rw [div_le_one he0] at h8
    linarith [hrows.eps_le]
  have hδ1' : p.δe / 7 ≤ 1 := by linarith
  set M := M0 p with hM
  have hM0 : 0 ≤ M := M0_nonneg p
  obtain ⟨C, hCb, -, hCn, hCc⟩ := existsNet d 1 (p.δe ^ 4) zero_le_one (by positivity)
  set Rc := rcS p d with hRc
  set Xv := xvS p d n with hXv
  set qf : E d → ℕ → Ω → ℝ := fun c t ω =>
    2 * df2Sq ((EvGY.ctxWV n δ Kθ apθ (θ 0) ψ ω).PBar (pathWAd gθ θ ξ e ω) t) (WithLp.ofLp c) with hqf
  have hU := lemmaU_setE μ 𝒢 C m n hmn (sigAdV n δ Kθ gθ apθ θ ψ ξ e) ξ e
    (fun s hs => measurable_sigAdV n δ Kθ gθ apθ hmeas 𝒢 θ ψ hK ξ e hθ hψ hE.xi_meas hE.e_meas hs.le)
    hE.xi_meas hE.xi_law hE.xi_indep hE.e_meas hE.e_int hE.e_mean hE.e_exp
    (fun c s => aOf n δ Kθ gθ M s (phiC n δ c)) (fun c _ => bOf n δ Kθ M (phiC n δ c))
    (fun c s hs => measurable_aOf n δ Kθ gθ apNone hmeas.none hs M (phiC n δ c)
      (measurable_phiH n δ _ measurable_const))
    (fun c s _ => measurable_bOf n δ Kθ gθ apNone hmeas.none M (phiC n δ c) (measurable_phiH n δ _ measurable_const))
    (fun c => kF d n δ M * kPhi p d M (WithLp.ofLp c)) 3
    (fun c => mul_nonneg (kF_nonneg n δ M he0) (kPhi_nonneg p d M _))
    (fun c s hs x => (aOf_bOf_le n δ Kθ gθ hbody hadm he0 heps hl0.le hl1 hM0 hs (phiC n δ c) _
      (kPhi_nonneg p d M _) (fun st hst z => phiH_le n δ M hM0 _ st hst z) x).1)
    (fun c s hs x => (aOf_bOf_le n δ Kθ gθ hbody hadm he0 heps hl0.le hl1 hM0 hs (phiC n δ c) _
      (kPhi_nonneg p d M _) (fun st hst z => phiH_le n δ M hM0 _ st hst z) x).2)
    (p.δe ^ 2)⁻¹ (p.δe / 7) (by positivity) (by positivity) hδ1'
    (fun c t ω => (p.lam * p.k0) ^ 2 * qf c t ω ^ 2 * Xv) (fun c t ω => Rc * qf c t ω + p.δe ^ 2)
  refine le_trans (measure_mono ?_) (hU.trans (le_of_eq (congrArg ENNReal.ofReal (by ring))))
  intro ω hω
  obtain ⟨hG, hS⟩ := hω
  have H : DetBase (EvGY.ctxWV n δ Kθ apθ (θ 0) ψ ω) δ (pathWAd gθ θ ξ e ω) m :=
    EvGY.detBaseV hSI hd hn hδ0 hδ1 heps hm1 hmn (hbody (θ 0 ω)) (fun s => hap (ψ s ω)) (admAd Kθ gθ hadm θ hK ω)
  set cω := EvGY.ctxWV n δ Kθ apθ (θ 0) ψ ω with hcω
  set πω := pathWAd gθ θ ξ e ω with hπω
  change cω.EvG πω m at hG
  change ¬ cω.EvSDF πω m at hS
  -- the parameters on the path
  have hx14 : 14 ≤ Real.log (1 / p.δe) := H.x_ge
  have hLe : p.Le = 36 * Real.log (1 / p.δe) := H.Le_eq
  have hsig : p.sig2 = 1 / (8 * p.Le) := H.sig2
  have hk0 : 0 ≤ p.k0 := H.k0_pos.le
  have hk0' : p.k0 ≤ 21 / 20 := hrows.k0_le
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnδ : (n : ℝ) * p.δe ≤ 1 := by
    have h := hrows.cnu
    rw [div_le_one (by positivity)] at h
    nlinarith
  have hRc0 : 0 ≤ Rc := rcS_nonneg H
  have hXv0 : 0 ≤ Xv := xvS_nonneg p d n
  have hlk : 0 ≤ p.lam * p.k0 := mul_nonneg hl0.le hk0
  have hRb := df2oPar_R_bound d n hd δ
  have hXvle : Xv ≤ 2305 * n * Real.log (1 / p.δe) ^ 2 :=
    xv_le d n p.δe p.R p.eps hd1 hn1 hde hrows.cx hRb.1.le hRb.2 he0 hrows.r14
  have hRcδ : Rc * p.δe ≤ 1 :=
    rc_le_inv d n _ p.δe p.lam p.k0 p.eps p.Le p.sig2 hd1 hn1 hx14 hLe hde hl0 hl2 hrows.r11 hk0 hk0' he0
      hrows.r14 hsig hnδ
  have hlX : p.lam * p.k0 * Real.sqrt Xv * p.δe ≤ 1 :=
    lkxv_le_inv d n _ p.δe p.lam p.k0 p.Le Xv hd1 hn1 hx14 hLe hde hl0 hrows.r11 hk0 hk0' hXv0 hXvle hnδ
  -- a failure of S-DF
  unfold Df2Ctx.EvSDF at hS
  push Not at hS
  obtain ⟨t, ht, v, hv⟩ := hS
  rw [Pn_sub_PBar H ht, sq_smul, abs_mul, abs_of_pos H.kap_pos] at hv
  have hkap : cω.p.kap = 1 / 4 := H.kap
  have heta : 0 < p.eta := hrows.pos_eta
  set Bn := df2Bn p d n with hBn
  have hLpos : 0 < p.Le := by have : 1 ≤ p.Le := H.one_le_Le; linarith
  have hBn0 : 0 ≤ Bn := by rw [hBn]; unfold df2Bn; positivity
  have hv' : 4 * Bn * df2Sq (cω.PBar πω t) v < |df2Sq (At cω πω t) v| := by
    have h1 : p.eta * (4 * Bn * df2Sq (cω.PBar πω t) v) < p.eta * |df2Sq (At cω πω t) v| := by
      have h2 : 4 * p.kap * p.eta * Bn * df2Sq (cω.PBar πω t) v <
          p.eta * p.kap * |df2Sq (At cω πω t) v| := hv
      have hk4 : p.kap = 1 / 4 := rfl
      rw [hk4] at h2
      linarith
    exact lt_of_mul_lt_mul_left h1 heta.le
  -- the unit direction
  have hvv : v ⬝ᵥ v ≠ 0 := by
    intro h0
    rw [dot_self_eq_zero h0] at hv'
    simp [df2Sq] at hv'
  set r := Real.sqrt (v ⬝ᵥ v) with hr
  have hr0 : 0 < r := Real.sqrt_pos.2 (lt_of_le_of_ne (dot_self_nonneg' v) (Ne.symm hvv))
  set u := r⁻¹ • v with hu
  have huu : u ⬝ᵥ u = 1 := by
    rw [hu, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc, ← sq,
      ← Real.sq_sqrt (dot_self_nonneg' v), ← hr, inv_pow, inv_mul_cancel₀ (by positivity)]
  have hAu : 4 * Bn * df2Sq (cω.PBar πω t) u < |df2Sq (At cω πω t) u| := by
    rw [hu, sq_smul_arg, sq_smul_arg, abs_mul, abs_of_nonneg (sq_nonneg _)]
    have : 0 < r⁻¹ ^ 2 := by positivity
    nlinarith
  -- the net point
  have huB : (WithLp.toLp 2 u : E d) ∈ Metric.closedBall (0 : E d) 1 := by
    rw [Metric.mem_closedBall, dist_zero_right, norm_toLp, huu, Real.sqrt_one]
  obtain ⟨c, hc, hdc⟩ := hCn _ huB
  set vc := WithLp.ofLp c with hvc
  have hcv : c = WithLp.toLp 2 vc := (WithLp.toLp_ofLp 2 c).symm
  have hvc1 : vc ⬝ᵥ vc ≤ 1 := by
    have h := hCb hc
    rw [Metric.mem_closedBall, dist_zero_right, hcv, norm_toLp] at h
    have h0 := dot_self_nonneg' vc
    rw [← Real.sqrt_one] at h
    exact (Real.sqrt_le_sqrt_iff zero_le_one).1 h
  have hdu : Real.sqrt ((u - vc) ⬝ᵥ (u - vc)) ≤ p.δe ^ 4 := by
    rw [hcv, dist_eq_norm, ← WithLp.toLp_sub, norm_toLp] at hdc
    exact hdc
  have hsu : Real.sqrt ((u + vc) ⬝ᵥ (u + vc)) ≤ 2 := by
    have h := (oNorm_tri u vc 0 ∅ fun _ => 0).1
    have h1 : Real.sqrt (u ⬝ᵥ u) = 1 := by rw [huu, Real.sqrt_one]
    have h2 : Real.sqrt (vc ⬝ᵥ vc) ≤ 1 := by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hvc1
    linarith
  have hdu0 := Real.sqrt_nonneg ((u - vc) ⬝ᵥ (u - vc))
  have hsu0 := Real.sqrt_nonneg ((u + vc) ⬝ᵥ (u + vc))
  have hτm := H.le_tau_lt ht
  set q := qf c t ω with hq
  have hqe : q = 2 * df2Sq (cω.PBar πω t) vc := rfl
  have hq0 : 0 ≤ q := by rw [hqe]; linarith [sq_nonneg_of_psd (H.PBar_psd ht) vc]
  have hqδ : q * p.δe ≤ 1 := by
    have h := PBar_quad_upper H ht vc
    have h' : 2 * df2Sq (cω.PBar πω t) vc ≤ p.δe⁻¹ * (vc ⬝ᵥ vc) := h
    rw [hqe]
    calc 2 * df2Sq (cω.PBar πω t) vc * p.δe ≤ p.δe⁻¹ * (vc ⬝ᵥ vc) * p.δe :=
          mul_le_mul_of_nonneg_right h' hde.le
      _ = vc ⬝ᵥ vc := by field_simp
      _ ≤ 1 := hvc1
  -- the sum of the increments
  have hZ : ∀ s ≤ t, zSeq m (fun c s => aOf n δ Kθ gθ M s (phiC n δ c))
      (fun c _ => bOf n δ Kθ M (phiC n δ c)) (sigAdV n δ Kθ gθ apθ θ ψ ξ e) ξ e c s ω =
      df2Sq (cω.shh πω s) vc - df2Sq (cω.sHess πω s) vc := fun s hs =>
    zSeq_pathAdV n δ Kθ gθ apθ θ ψ ξ e ω hK H c (hs.trans ht)
  refine ⟨c, hc, t, hτm, ?_, ?_, ?_, ?_, ?_⟩
  · exact mul_nonneg (by positivity) hXv0
  · show 1 ≤ (p.δe ^ 2)⁻¹ * (Rc * q + p.δe ^ 2)
    rw [mul_add, inv_mul_cancel₀ (by positivity)]
    have : 0 ≤ (p.δe ^ 2)⁻¹ * (Rc * q) := by positivity
    linarith
  · show ∑ s ∈ Finset.range (t + 1), ∫ z, (aOf n δ Kθ gθ M s (phiC n δ c) (sigAdV n δ Kθ gθ apθ θ ψ ξ e s ω, z) ^ 2 +
        bOf n δ Kθ M (phiC n δ c) (sigAdV n δ Kθ gθ apθ θ ψ ξ e s ω, z) ^ 2) ∂(gam d) ≤ (p.lam * p.k0) ^ 2 * q ^ 2 * Xv
    refine le_trans (Finset.sum_le_sum fun s hs => ?_) (vsum_phiH_leV H ht vc)
    have hst : s ≤ cω.tau πω m := (Nat.lt_succ_iff.1 (Finset.mem_range.1 hs)).trans ht
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => by positivity)
      (integrable_yR_phiHV H hst vc) (Filter.Eventually.of_forall fun z => ?_)
    refine (sq_aOf_bOf_le n δ Kθ gθ M s (phiC n δ c) (sigAdV n δ Kθ gθ apθ θ ψ ξ e s ω, z)).trans (le_of_eq ?_)
    rw [fF_sigAdV n δ Kθ gθ apθ θ ψ ξ e ω s hK z, fP_sigAdV n δ Kθ gθ apθ θ ψ ξ e ω s hK z]
    rfl
  · intro s hs
    rw [hZ s hs]
    show |df2Sq (cω.shh πω s) vc - df2Sq (cω.sHess πω s) vc| ≤ Rc * q + p.δe ^ 2
    have h1 := round_le H hG (hs.trans ht) vc
    have h2 := P_quad_le H hs ht vc
    have h3 : |df2Sq (cω.shh πω s) vc - df2Sq (cω.sHess πω s) vc| ≤
        |df2Sq (cω.shh πω s) vc| + |df2Sq (cω.sHess πω s) vc| := abs_sub _ _
    have h4 : Rc * df2Sq (cω.st πω s).P vc ≤ Rc * q := mul_le_mul_of_nonneg_left (by rw [hqe]; exact h2) hRc0
    have h1' : |df2Sq (cω.shh πω s) vc| + |df2Sq (cω.sHess πω s) vc| ≤ Rc * df2Sq (cω.st πω s).P vc := h1
    calc _ ≤ _ := h3
      _ ≤ _ := h1'
      _ ≤ Rc * q := h4
      _ ≤ Rc * q + p.δe ^ 2 := le_add_of_nonneg_right (sq_nonneg _)
  · have hsum : ∑ s ∈ Finset.range (t + 1), zSeq m (fun c s => aOf n δ Kθ gθ M s (phiC n δ c))
        (fun c _ => bOf n δ Kθ M (phiC n δ c)) (sigAdV n δ Kθ gθ apθ θ ψ ξ e) ξ e c s ω = df2Sq (At cω πω t) vc := by
      rw [At, sq_sum]
      refine Finset.sum_congr rfl fun s hs => ?_
      rw [hZ s (Nat.lt_succ_iff.1 (Finset.mem_range.1 hs)), sq_sub]
    rw [hsum]
    set l := Real.log (4 * ((n : ℝ) * (C.card : ℝ)) * max ((p.δe ^ 2)⁻¹ * (Rc * q + p.δe ^ 2))
      ((p.δe ^ 2)⁻¹ * Real.sqrt ((p.lam * p.k0) ^ 2 * q ^ 2 * Xv)) / (p.δe / 7)) with hl
    have hC0 : (1 : ℝ) ≤ C.card := by exact_mod_cast Finset.card_pos.2 ⟨c, hc⟩
    obtain ⟨hlg0, hlg⟩ := log_level_le d hd p.δe n C.card Rc q (p.lam * p.k0) Xv hde hx14 hn1 hnδ hC0 hCc hRc0
      hRcδ hq0 hqδ hlk hXv0 hlX
    have hV := vcoef_le d n _ p.lam p.k0 p.eps p.Le Xv l hd1 hn1 hx14 hLe hl0 hk0 hk0' he0 hXv0 hXvle hlg0 hlg
    have hR := rcoef_le d n _ p.lam p.k0 p.eps p.Le p.sig2 l hd1 hn1 hx14 hLe hl0 hl2 hk0 hk0' he0 hsig hlg0 hlg
    have hsm := small_le d n _ p.δe p.lam p.k0 p.eps p.Le p.sig2 l hd1 hn1 hx14 hLe hde hδ12 hl0 hl2 hk0 hk0'
      he0 hsig hrows.c2dl hnδ hlg0 hlg
    have hKA : 0 ≤ (n : ℝ) * Rc / p.δe := by positivity
    have hA : |df2Sq (At cω πω t) u - df2Sq (At cω πω t) vc| ≤ 2 * n * Rc * p.δe ^ 3 := by
      have h := quad_sub_le (At cω πω t) (At_symm H ht) ((n : ℝ) * Rc / p.δe) (fun w => At_quad_le H hG ht w) u vc
      calc _ ≤ (n : ℝ) * Rc / p.δe * (Real.sqrt ((u - vc) ⬝ᵥ (u - vc)) * Real.sqrt ((u + vc) ⬝ᵥ (u + vc))) := h
        _ ≤ (n : ℝ) * Rc / p.δe * (p.δe ^ 4 * 2) := by gcongr
        _ = 2 * n * Rc * p.δe ^ 3 := by field_simp
    have hqq : |2 * df2Sq (cω.PBar πω t) u - q| ≤ 2 * p.δe ^ 3 := by
      have hK : ∀ w, |df2Sq (cω.PBar πω t) w| ≤ p.δe⁻¹ / 2 * (w ⬝ᵥ w) := fun w => by
        rw [abs_of_nonneg (sq_nonneg_of_psd (H.PBar_psd ht) w)]
        have h : 2 * df2Sq (cω.PBar πω t) w ≤ p.δe⁻¹ * (w ⬝ᵥ w) := PBar_quad_upper H ht w
        linarith
      have h := quad_sub_le (cω.PBar πω t) (PBar_symm H ht) (p.δe⁻¹ / 2) hK u vc
      rw [hqe, ← mul_sub, abs_mul, abs_two]
      have hK0 : 0 ≤ p.δe⁻¹ / 2 := by positivity
      calc 2 * |df2Sq (cω.PBar πω t) u - df2Sq (cω.PBar πω t) vc|
          ≤ 2 * (p.δe⁻¹ / 2 * (Real.sqrt ((u - vc) ⬝ᵥ (u - vc)) * Real.sqrt ((u + vc) ⬝ᵥ (u + vc)))) := by gcongr
        _ ≤ 2 * (p.δe⁻¹ / 2 * (p.δe ^ 4 * 2)) := by gcongr
        _ = 2 * p.δe ^ 3 := by field_simp
    have hqu : 4 * p.δe ≤ 2 * df2Sq (cω.PBar πω t) u := by
      have h : 2 * p.δe * (u ⬝ᵥ u) ≤ df2Sq (cω.PBar πω t) u := PBar_quad_lower H ht u
      rw [huu] at h
      linarith
    have hAu' : 2 * Bn * (2 * df2Sq (cω.PBar πω t) u) < |df2Sq (At cω πω t) u| := by linarith [hAu]
    exact sdf_final Bn Rc Xv (p.lam * p.k0) q (2 * df2Sq (cω.PBar πω t) u) (df2Sq (At cω πω t) u)
      (df2Sq (At cω πω t) vc) l p.δe (2 * p.δe ^ 3) (2 * n * Rc * p.δe ^ 3) hBn0 hlk hq0 hXv0 hlg0 hAu' hA hqq hqu
      hV hR hsm

/-- The budget S-DF with an adapted parameter holds. -/
theorem df2EvSDFPropAdV_holds : Df2EvSDFPropAdV :=
  df2EvSDFPropAdV_of SIF.df2SIFacts_holds

end AdversarialBco.Poly.EvAd
