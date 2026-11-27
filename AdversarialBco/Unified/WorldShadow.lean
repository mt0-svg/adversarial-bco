/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.WorldExt

@[expose] public section

/-!
# The reference P° on an abstract coupled world

The reference analysis of the bit chain (Bit/ShadowMeas.lean, Bit/ShadowSetE.lean, Bit/ShadowAz.lean and
Bit/ShadowStep2.lean) on a world `W : CWorld d Ω` with `WorldLawOK W` in place of the world `WΩ` under
`gaussStream ⊗ ν`: the laws and the independences of the coordinates are the fields of `WorldLawOK`, and the noise
facts (`eRef_mean`, `eRef_exp`, `E |ε_t| ≤ 1`) come from (W2).

* `WorldLawOK.meas_xi`, `meas_xg`, `meas_zz`, `meas_nz`, `Fσ_le`, `HC_le_Fσ`: the coordinates of round `t` are known
  after round `t`;
* `RunW.mode_meas` (Lemma W-MEAS), `RunW.zeta_meas`, `RunW.adv_meas`, `RunW.shR_meas`;
* `RunW.setE_ref` (Proposition W-SETE): `Df2SetE d W.μ W.𝓕 W.xi e°` with `e°_t = (ε_t + ζ*_t)/2`;
* `RunW.waz` (Proposition W-AZ): `Case` without the Azuma event has probability at most `δe/7`;
* `coupStepPropW_holds : CoupStepPropW` (Step 2 of SHADOW).
-/

open MeasureTheory ProbabilityTheory Matrix

namespace AdversarialBco.Unified.World

open AdversarialBco.RealRAM AdversarialBco.Poly AdversarialBco.Poly.Layer2 AdversarialBco.Bit.Cpl
open AdversarialBco.Poly.Conj1 (fL measurable_fL)

variable {d : ℕ}

/-! ## The coordinates of round `t` -/

namespace WorldLawOK

variable {Ω : Type} [m0 : MeasurableSpace Ω] {W : CWorld d Ω}

theorem meas_xi (hW : WorldLawOK W) (t : ℕ) : Measurable[W.𝓕 (t + 1)] (W.xi t) :=
  measurable_pi_of fun c => hW.g_adapt (t + 1) (cIdx d t c) (cIdx_mem_idxC_succ (by omega))

theorem meas_xg (hW : WorldLawOK W) (t : ℕ) : Measurable[W.𝓕 (t + 1)] (W.xg t) :=
  measurable_pi_of fun c => hW.g_adapt (t + 1) (cIdx d t c) (cIdx_mem_idxC_succ (by omega))

theorem meas_zz (hW : WorldLawOK W) (t : ℕ) : Measurable[W.𝓕 (t + 1)] (W.zz t) := by
  refine measurable_pi_of fun k => ?_
  fin_cases k
  · exact hW.g_adapt (t + 1) (cIdx d t (d + 1)) (cIdx_mem_idxC_succ (by omega))
  · exact hW.g_adapt (t + 1) (cIdx d t (d + 3)) (cIdx_mem_idxC_succ (by omega))
  · exact hW.g_adapt (t + 1) (cIdx d t (d + 4)) (cIdx_mem_idxC_succ (by omega))

theorem meas_nz (hW : WorldLawOK W) (t : ℕ) : Measurable[W.𝓕 (t + 1)] (W.nz t) :=
  hW.e_adapt (t + 1) t (Nat.lt_succ_self t)

theorem Fσ_le (hW : WorldLawOK W) (t : ℕ) : W.Fσ t ≤ W.𝓕 (t + 1) :=
  sup_le (sup_le (W.𝓕.mono (Nat.le_succ t)) (hW.meas_xg t).comap_le) (hW.meas_nz t).comap_le

theorem Fσ_le_m0 (hW : WorldLawOK W) (t : ℕ) : W.Fσ t ≤ m0 := (hW.Fσ_le t).trans (W.𝓕.le (t + 1))

theorem HC_le_Fσ (t : ℕ) : W.HC t ≤ W.Fσ t := by
  refine sup_le (le_sup_left.trans le_sup_left) ?_
  have hg : Measurable[W.Fσ t] (W.xg t) := Measurable.of_comap_le (le_sup_right.trans le_sup_left)
  exact (measurable_pi_of fun c => (measurable_pi_apply (Fin.castSucc c)).comp hg).comap_le

theorem HC_le_m0 (hW : WorldLawOK W) (t : ℕ) : W.HC t ≤ m0 := (HC_le_Fσ t).trans (hW.Fσ_le_m0 t)

/-- `E |ε_t| ≤ 1`, from (W2): `|x| ≤ exp(x²)/2` and `E exp(ε_t²) = E E[exp(ε_t²) | H_t] ≤ 2`. -/
theorem noise_abs_lintegral (hW : WorldLawOK W) (t : ℕ) : ∫⁻ ω, ENNReal.ofReal |W.nz t ω| ∂W.μ ≤ 1 := by
  have := hW.prob
  have hle := hW.HC_le_m0 t
  have hpt : ∀ x : ℝ, |x| ≤ Real.exp (x ^ 2) / 2 := by
    intro x
    have h1 : 2 * |x| ≤ |x| ^ 2 + 1 := by nlinarith [sq_nonneg (|x| - 1)]
    have h2 : |x| ^ 2 + 1 ≤ Real.exp (x ^ 2) := by simpa [sq_abs] using Real.add_one_le_exp (x ^ 2)
    linarith
  have hexp : ∫ ω, Real.exp (W.nz t ω ^ 2) ∂W.μ ≤ 2 := by
    calc ∫ ω, Real.exp (W.nz t ω ^ 2) ∂W.μ = ∫ ω, (W.μ[fun ω => Real.exp (W.nz t ω ^ 2) | W.HC t]) ω ∂W.μ := by
          rw [integral_condExp hle]
      _ ≤ ∫ _ω, (2 : ℝ) ∂W.μ := integral_mono_ae integrable_condExp (integrable_const _) (hW.e_exp t)
      _ = 2 := by simp
  calc ∫⁻ ω, ENNReal.ofReal |W.nz t ω| ∂W.μ ≤ ∫⁻ ω, ENNReal.ofReal (Real.exp (W.nz t ω ^ 2) / 2) ∂W.μ :=
        lintegral_mono fun ω => ENNReal.ofReal_le_ofReal (hpt _)
    _ = ENNReal.ofReal (∫ ω, Real.exp (W.nz t ω ^ 2) / 2 ∂W.μ) := by
        rw [ofReal_integral_eq_lintegral_ofReal ((hW.e_int t).div_const 2)
          (Filter.Eventually.of_forall fun ω => by positivity)]
    _ ≤ ENNReal.ofReal (2 / 2) := by
        rw [integral_div]
        exact ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right hexp (by norm_num))
    _ = 1 := by norm_num

end WorldLawOK

/-! ## Lemma W-MEAS -/

namespace RunW

variable {n : ℕ} {K : Set (E d)} {Ω : Type} [m0 : MeasurableSpace Ω] {W : CWorld d Ω} (B : RunW d n K W) (δ : ℝ)

theorem pairMode_meas {X : Type} {m : MeasurableSpace X} {f : X → Df2Mode d} (hf : Measurable[m] f) :
    @Measurable X (X × Df2Mode d) m (m.prod inferInstance) fun x => (x, f x) :=
  Measurable.prodMk (@measurable_id X m) hf

theorem 𝓕_le_Fσ (t : ℕ) : W.𝓕 t ≤ W.Fσ t := le_sup_left.trans le_sup_left

/-- The shift of round `t` on P°'s run is known at `F*_t`, given the mode before round `t` is known at `𝓕 t`. -/
theorem shR_meas (hB : BLMeasW B) {t : ℕ} (hmode : Measurable[W.𝓕 t] fun ω => B.mode δ t ω) :
    Measurable[W.Fσ t] (B.shR δ t) :=
  (hB.sh t).comp (pairMode_meas (hmode.mono (𝓕_le_Fσ t) le_rfl))

/-- P°'s dither of round `t` is known after round `t`. -/
theorem zeta_meas (hW : WorldLawOK W) (hB : BLMeasW B) (hC : CoupLaw B.Coup) {t : ℕ}
    (hmode : Measurable[W.𝓕 t] fun ω => B.mode δ t ω) :
    Measurable[W.𝓕 (t + 1)] fun ω => B.zeta t ω (B.mode δ t ω) := by
  have hs := (shR_meas B δ hB hmode).mono (hW.Fσ_le t) le_rfl
  exact hC.meas.comp (hs.fst.prodMk (hs.snd.prodMk (hW.meas_zz t)))

/-- P°'s advice of round `t` is known after round `t`. -/
theorem adv_meas (hB : BLMeasW B) {t : ℕ} (hmode : Measurable[W.𝓕 t] fun ω => B.mode δ t ω) :
    Measurable[W.𝓕 (t + 1)] fun ω => B.adv t ω (B.mode δ t ω) :=
  (hB.adv t).comp (pairMode_meas (hmode.mono (W.𝓕.mono (Nat.le_succ t)) le_rfl))

/-- Lemma W-MEAS: P°'s mode before round `t` is known before round `t`. -/
theorem mode_meas (hW : WorldLawOK W) (hreg : Regime d n δ) (hKc : IsClosed K) (hKconv : Convex ℝ K)
    (hpos : Measurable[W.𝓕 0] B.pos) (hB : BLMeasW B) (hC : CoupLaw B.Coup) :
    ∀ t, Measurable[W.𝓕 t] fun ω => B.mode δ t ω := by
  obtain ⟨hd, hn, hδ0, hδ1, heps⟩ := hreg
  have H := rowHyp_of d n δ hd hn hδ0 hδ1 heps
  have hR := row_one_le_R _ d n H
  have hmw : 1 / (df2oPar d n δ).R ≤ df2Mw d := by rw [H.R]; exact inv_R_le_df2Mw d hd
  intro t
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    have hpos' : Measurable[W.𝓕 (t + 1)] B.pos := hpos.mono (W.𝓕.mono (Nat.zero_le _)) le_rfl
    have hm' : Measurable[W.𝓕 (t + 1)] fun ω => B.mode δ t ω := ih.mono (W.𝓕.mono (Nat.le_succ t)) le_rfl
    have hrest : Measurable[W.𝓕 (t + 1)] fun ω =>
        (B.mode δ t ω, W.xi t ω, W.nz t ω, B.zeta t ω (B.mode δ t ω)) :=
      hm'.prodMk ((hW.meas_xi t).prodMk ((hW.meas_nz t).prodMk (zeta_meas B δ hW hB hC ih)))
    by_cases ht : t < n
    · have hft := measurable_fL (K := K) (L := B.F.L) (t := t) (fun l => (B.F.adm t ht l).1) (B.F.meas t ht)
      have hround := cRoundA_measL (n := n) (δ := δ) hKc hKconv hR hmw hft
      have hlam : Measurable[W.𝓕 (t + 1)] (B.F.lam t) :=
        (B.F.lam_meas t ht).mono (W.𝓕.mono (Nat.le_succ t)) le_rfl
      have htup : Measurable[W.𝓕 (t + 1)] fun ω =>
          ((B.pos ω, B.F.lam t ω, B.adv t ω (B.mode δ t ω)),
            B.mode δ t ω, W.xi t ω, W.nz t ω, B.zeta t ω (B.mode δ t ω)) :=
        (hpos'.prodMk (hlam.prodMk (adv_meas B δ hB ih))).prodMk hrest
      have h := measurable_snd.comp (hround.comp htup)
      convert h using 1
      funext ω
      simp only [Function.comp_def, RunW.mode, RunW.lossR, ht, ↓reduceIte]
    · have hft : Measurable fun p : Unit × E d => (fun (_ : Unit) (_ : E d) => (0 : ℝ)) p.1 p.2 := measurable_const
      have hround := cRoundA_measL (n := n) (δ := δ) (ft := fun (_ : Unit) (_ : E d) => (0 : ℝ)) hKc hKconv hR hmw hft
      have htup : Measurable[W.𝓕 (t + 1)] fun ω =>
          ((B.pos ω, (), B.adv t ω (B.mode δ t ω)),
            B.mode δ t ω, W.xi t ω, W.nz t ω, B.zeta t ω (B.mode δ t ω)) :=
        (hpos'.prodMk (measurable_const.prodMk (adv_meas B δ hB ih))).prodMk hrest
      have h := measurable_snd.comp (hround.comp htup)
      convert h using 1
      funext ω
      simp only [Function.comp_def, RunW.mode, RunW.lossR, ht, ↓reduceIte]
      rfl

/-! ## Proposition W-SETE -/

/-- P°'s dither of round `t`. -/
noncomputable abbrev zs (t : ℕ) (ω : Ω) : ℝ := B.zeta t ω (B.mode δ t ω)

variable {B δ}

theorem zs_meas (hW : WorldLawOK W) (hB : BLMeasW B) (hC : CoupLaw B.Coup) {t : ℕ}
    (hmode : Measurable[W.𝓕 t] fun ω => B.mode δ t ω) : Measurable (B.zs δ t) :=
  (zeta_meas B δ hW hB hC hmode).mono (W.𝓕.le (t + 1)) le_rfl

/-- Lemma W-LAW (ii): the dither of round `t` has the law of `Z/2`. -/
theorem zs_law (hW : WorldLawOK W) (hB : BLMeasW B) (hC : CoupLaw B.Coup) {t : ℕ}
    (hmode : Measurable[W.𝓕 t] fun ω => B.mode δ t ω) :
    W.μ.map (B.zs δ t) = (gaussianReal 0 1).map (· / 2) := by
  have := hW.prob
  have hshR := shR_meas B δ hB hmode
  have hx : Measurable (B.shR δ t) := hshR.mono (hW.Fσ_le_m0 t) le_rfl
  have hz : Measurable (W.zz t) := (hW.meas_zz t).mono (W.𝓕.le (t + 1)) le_rfl
  have hind : IndepFun (B.shR δ t) (W.zz t) W.μ := by
    rw [IndepFun_iff_Indep]
    exact (indep_of_indep_of_le_right (hW.z_indep t) hshR.comap_le).symm
  have hmap := (indepFun_iff_map_prod_eq_prod_map_map hx.aemeasurable hz.aemeasurable).mp hind
  rw [hW.z_law t] at hmap
  have hΦ : Measurable fun p : (ℝ × ℝ) × (Fin 3 → ℝ) => B.Coup p.1.1 p.1.2 p.2 :=
    hC.meas.comp (f := fun p : (ℝ × ℝ) × (Fin 3 → ℝ) => (p.1.1, p.1.2, p.2)) (by fun_prop)
  rw [show B.zs δ t = (fun p : (ℝ × ℝ) × (Fin 3 → ℝ) => B.Coup p.1.1 p.1.2 p.2) ∘
    (fun ω => (B.shR δ t ω, W.zz t ω)) from rfl, ← Measure.map_map hΦ (hx.prodMk hz), hmap]
  exact map_prod_fiber _ _ _ hΦ _ fun x => hC.law x.1 x.2

theorem integrable_zs (hW : WorldLawOK W) (hB : BLMeasW B) (hC : CoupLaw B.Coup) {t : ℕ}
    (hmode : Measurable[W.𝓕 t] fun ω => B.mode δ t ω) {G : ℝ → ℝ} (hGm : Measurable G)
    (hG : Integrable (fun y => G (y / 2)) (gaussianReal 0 1)) : Integrable (fun ω => G (B.zs δ t ω)) W.μ := by
  have hγ : Integrable G ((gaussianReal 0 1).map (· / 2)) :=
    (integrable_map_measure (f := fun y : ℝ => y / 2) hGm.aestronglyMeasurable (by fun_prop)).mpr hG
  rw [← zs_law hW hB hC hmode] at hγ
  exact hγ.comp_measurable (zs_meas hW hB hC hmode)

/-- Lemma W-LAW (i) at `F*_t`. -/
theorem condExp_zs_F (hW : WorldLawOK W) (hB : BLMeasW B) (hC : CoupLaw B.Coup) {t : ℕ}
    (hmode : Measurable[W.𝓕 t] fun ω => B.mode δ t ω) {G : ℝ → ℝ} (hGm : Measurable G)
    (hint : Integrable (fun ω => G (B.zs δ t ω)) W.μ) :
    W.μ[fun ω => G (B.zs δ t ω) | W.Fσ t] =ᵐ[W.μ] fun _ => ∫ y, G (y / 2) ∂(gaussianReal 0 1) := by
  have := hW.prob
  have hz : Measurable (W.zz t) := (hW.meas_zz t).mono (W.𝓕.le (t + 1)) le_rfl
  have hΦ : Measurable fun p : (ℝ × ℝ) × (Fin 3 → ℝ) => G (B.Coup p.1.1 p.1.2 p.2) :=
    hGm.comp (hC.meas.comp (f := fun p : (ℝ × ℝ) × (Fin 3 → ℝ) => (p.1.1, p.1.2, p.2)) (by fun_prop))
  have h := lemmaFR Ω (ℝ × ℝ) (Fin 3 → ℝ) (W.Fσ t) W.μ (B.shR δ t) (W.zz t)
    (fun p => G (B.Coup p.1.1 p.1.2 p.2)) (hW.Fσ_le_m0 t) (shR_meas B δ hB hmode) hz (hW.z_indep t) hΦ hint
  rw [hW.z_law t] at h
  exact h.trans (Filter.Eventually.of_forall fun ω => by dsimp only; exact integral_coup hC hGm _ _)

/-- Lemma W-LAW (i) at `H_t`. -/
theorem condExp_zs_H (hW : WorldLawOK W) (hB : BLMeasW B) (hC : CoupLaw B.Coup) {t : ℕ}
    (hmode : Measurable[W.𝓕 t] fun ω => B.mode δ t ω) {G : ℝ → ℝ} (hGm : Measurable G)
    (hint : Integrable (fun ω => G (B.zs δ t ω)) W.μ) :
    W.μ[fun ω => G (B.zs δ t ω) | W.HC t] =ᵐ[W.μ] fun _ => ∫ y, G (y / 2) ∂(gaussianReal 0 1) := by
  have := hW.prob
  have h1 := condExp_condExp_of_le (μ := W.μ) (f := fun ω => G (B.zs δ t ω)) (WorldLawOK.HC_le_Fσ (W := W) t)
    (hW.Fσ_le_m0 t)
  have h2 := condExp_congr_ae (m := W.HC t) (condExp_zs_F hW hB hC hmode hGm hint)
  rw [condExp_const (hW.HC_le_m0 t)] at h2
  exact h1.symm.trans h2

theorem eRef_bound (t : ℕ) (ω : Ω) :
    Real.exp (B.eRef δ t ω ^ 2) ≤ (1 / 2 : ℝ) * (Real.exp (W.nz t ω ^ 2) + Real.exp (B.zs δ t ω ^ 2)) := by
  have := exp_sq_mid_le (W.nz t ω) (B.zs δ t ω)
  simp only [RunW.eRef] at this ⊢
  linarith

variable (hW : WorldLawOK W) (hB : BLMeasW B) (hC : CoupLaw B.Coup)
include hW hB hC

theorem eRef_meas {t : ℕ} (hmode : Measurable[W.𝓕 t] fun ω => B.mode δ t ω) :
    Measurable[W.𝓕 (t + 1)] (B.eRef δ t) :=
  ((hW.meas_nz t).add (zeta_meas B δ hW hB hC hmode)).div_const 2

theorem integrable_eRef_exp {t : ℕ} (hmode : Measurable[W.𝓕 t] fun ω => B.mode δ t ω) :
    Integrable (fun ω => Real.exp (B.eRef δ t ω ^ 2)) W.μ := by
  have hA := hW.e_int t
  have hB' := integrable_zs hW hB hC hmode (G := fun y => Real.exp (y ^ 2)) (by fun_prop) gauss_exp_quarter.1
  refine ((hA.add hB').const_mul (1 / 2)).mono' ?_ (Filter.Eventually.of_forall fun ω => ?_)
  · exact (Real.measurable_exp.comp (((eRef_meas hW hB hC hmode).mono (W.𝓕.le _) le_rfl).pow_const 2)).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact eRef_bound t ω

theorem eRef_mean {t : ℕ} (hmode : Measurable[W.𝓕 t] fun ω => B.mode δ t ω) :
    W.μ[B.eRef δ t | W.HC t] =ᵐ[W.μ] 0 := by
  have := hW.prob
  have he : B.eRef δ t = (1 / 2 : ℝ) • (W.nz t + fun ω => B.zs δ t ω) := by
    funext ω; simp only [RunW.eRef, Pi.smul_apply, Pi.add_apply, smul_eq_mul]; ring
  have hnm : Measurable (W.nz t) := (hW.meas_nz t).mono (W.𝓕.le _) le_rfl
  have hF : Integrable (W.nz t) W.μ := integrable_of_exp_sq hnm (hW.e_int t)
  have hG : Integrable (fun ω => B.zs δ t ω) W.μ :=
    integrable_zs hW hB hC hmode (G := id) measurable_id
      ((memLp_id_gaussianReal 1).integrable le_rfl |>.div_const 2)
  have h1 := hW.e_mean t
  have h2 := condExp_zs_H hW hB hC hmode (G := id) measurable_id hG
  have h0 : ∫ x, x / 2 ∂(gaussianReal 0 1) = 0 := by
    rw [integral_div, integral_id_gaussianReal, zero_div]
  simp only [id_eq] at h2
  rw [he]
  refine (condExp_smul _ _ _).trans ?_
  have hadd := condExp_add hF hG (W.HC t)
  filter_upwards [hadd, h1, h2] with ω hω h1ω h2ω
  simp only [Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at hω h1ω h2ω ⊢
  rw [hω, Pi.add_apply, h1ω, h2ω, h0]
  simp

theorem eRef_exp {t : ℕ} (hmode : Measurable[W.𝓕 t] fun ω => B.mode δ t ω) :
    W.μ[fun ω => Real.exp (B.eRef δ t ω ^ 2) | W.HC t] ≤ᵐ[W.μ] fun _ => 2 := by
  have hA := hW.e_int t
  have hB' := integrable_zs hW hB hC hmode (G := fun y => Real.exp (y ^ 2)) (by fun_prop) gauss_exp_quarter.1
  have hmono := condExp_mono (m := W.HC t) (integrable_eRef_exp hW hB hC hmode)
    ((hA.add hB').smul (1 / 2 : ℝ)) (Filter.Eventually.of_forall fun ω => by
      simpa only [Pi.smul_apply, Pi.add_apply, smul_eq_mul] using eRef_bound t ω)
  have hsm := condExp_smul (μ := W.μ) (1 / 2 : ℝ)
    ((fun ω => Real.exp (W.nz t ω ^ 2)) + fun ω => Real.exp (B.zs δ t ω ^ 2)) (W.HC t)
  have hadd := condExp_add hA hB' (W.HC t)
  have h1 := hW.e_exp t
  have h2 := condExp_zs_H hW hB hC hmode (G := fun y => Real.exp (y ^ 2)) (by fun_prop) hB'
  have h0 := gauss_exp_quarter.2
  filter_upwards [hmono, hsm, hadd, h1, h2] with ω hm hs ha h1ω h2ω
  have hm2 := hm.trans_eq hs
  simp only [Pi.smul_apply, smul_eq_mul] at hm2
  rw [ha] at hm2
  simp only [Pi.add_apply] at hm2
  rw [h2ω] at hm2
  linarith

/-- Proposition W-SETE: the coupled world with the draws `W.xi` and P°'s noise `e°` is an instance of setting (E). -/
theorem setE_ref (hreg : Regime d n δ) (hKc : IsClosed K) (hKconv : Convex ℝ K) (hpos : Measurable[W.𝓕 0] B.pos) :
    Df2SetE d W.μ W.𝓕 W.xi (fun t => B.eRef δ t) := by
  have hmode := mode_meas B δ hW hreg hKc hKconv hpos hB hC
  exact
  { xi_meas := hW.meas_xi
    xi_law := hW.xi_law
    xi_indep := hW.xi_indep
    e_meas := fun t => eRef_meas hW hB hC (hmode t)
    e_int := fun t => integrable_eRef_exp hW hB hC (hmode t)
    e_mean := fun t => eRef_mean hW hB hC (hmode t)
    e_exp := fun t => eRef_exp hW hB hC (hmode t) }

end RunW

/-! ## Proposition W-AZ -/

namespace RunW

variable {n : ℕ} {K : Set (E d)} {Ω : Type} [m0 : MeasurableSpace Ω] {W : CWorld d Ω} {B : RunW d n K W} {δ : ℝ}

theorem goodPos_of_case {ω : Ω} (hq : B.Case δ ω) : PropG.GoodPos K (df2oPar d n δ).R (B.pos ω) := by
  obtain ⟨h1, h2, h3, -⟩ := good_unpack hq
  exact ⟨h1, h2, h3⟩

section Case

variable (hKconv : Convex ℝ K) (hKc : IsClosed K) {ω : Ω} (hq : B.Case δ ω) (heps0 : 0 < (df2oPar d n δ).eps)
  (heps1 : (df2oPar d n δ).eps < 1)
include hKconv hKc hq heps0 heps1

/-- On `Case`, a round of P° from a mode other than `off` plays in the interior of `K` and does not switch off. -/
theorem cRoundA_good (ap : ApFun d) (ft : E d → ℝ) (nt : ℝ) (ξ : Fin d → ℝ) (ζ : ℝ) {m : Df2Mode d}
    (hm : m ≠ .off) :
    (cRoundA n δ K (B.pos ω) ap ft nt ξ ζ m).1 ∈ interior K ∧ (cRoundA n δ K (B.pos ω) ap ft nt ξ ζ m).2 ≠ .off := by
  unfold cRoundA
  rw [kTh_good hq]
  exact PropG.round_good _ n hKconv hKc (goodPos_of_case hq) heps0 heps1 _ (fun _ => le_rfl) ap ft nt ξ ζ hm

theorem mode_ne_off : ∀ t, B.mode δ t ω ≠ .off
  | 0 => nofun
  | t + 1 => (cRoundA_good hKconv hKc hq heps0 heps1 _ _ _ _ _ (mode_ne_off t)).2

theorem refPlay_interior (t : ℕ) : B.refPlay δ t ω ∈ interior K :=
  (cRoundA_good hKconv hKc hq heps0 heps1 _ _ _ _ _ (mode_ne_off hKconv hKc hq heps0 heps1 t)).1

end Case

/-- The play of P° in round `t` is the play of the round with the routine `apAdv (0, 0)`, the loss `fL`, no noise
and no dither. -/
theorem refPlay_eq (t : ℕ) (ω : Ω) : B.refPlay δ t ω =
    (cRoundA n δ K (B.pos ω) (apAdv (0, 0)) (fL K B.F.L t (B.F.lam t ω)) 0 (W.xi t ω) 0 (B.mode δ t ω)).1 := by
  unfold refPlay cRoundA
  rw [roundGa_fst_ap _ _ _ _ _ _ (apAdv (0, 0)),
    roundGa_fst _ _ _ _ _ _ _ (fL K B.F.L t (B.F.lam t ω)) _ 0 _ _ 0]

/-- Proposition W-AZ: on a coupled world, `Case` without the Azuma event has probability at most `δe/7`. -/
theorem waz (hW : WorldLawOK W) (hreg : Regime d n δ) (hKc : IsClosed K) (hKconv : Convex ℝ K)
    (hpos : Measurable[W.𝓕 0] B.pos) (hB : BLMeasW B) (hC : CoupLaw B.Coup) :
    W.μ {ω | B.Case δ ω ∧ ¬ B.Az δ ω} ≤ ENNReal.ofReal ((df2oPar d n δ).δe / 7) := by
  classical
  have hmode := mode_meas B δ hW hreg hKc hKconv hpos hB hC
  obtain ⟨hd, hn, hδ0, hδ1, heps⟩ := hreg
  have H := rowHyp_of d n δ hd hn hδ0 hδ1 heps
  have hR := row_one_le_R _ d n H
  have hmw : 1 / (df2oPar d n δ).R ≤ df2Mw d := by rw [H.R]; exact inv_R_le_df2Mw d hd
  have heps0 := eps_pos_of_rows H
  have heps1 : (df2oPar d n δ).eps < 1 := by linarith
  have := hW.prob
  set μ := W.μ with hμ
  set ℱ := W.𝓕 with hℱ
  set Z : ℕ → Ω → ℝ := fun t ω => B.lossR t ω (B.refPlay δ t ω) with hZ
  set x : ℕ → Ω → (PgSp d × B.F.Λ) × Df2Mode d := fun t ω => ((B.pos ω, B.F.lam t ω), B.mode δ t ω) with hxdef
  set F : ℕ → ((PgSp d × B.F.Λ) × Df2Mode d) × (Fin d → ℝ) → ℝ :=
    fun t p => fL K B.F.L t p.1.1.2
      (cRoundA n δ K p.1.1.1 (apAdv (0, 0)) (fL K B.F.L t p.1.1.2) 0 p.2 0 p.1.2).1 with hFdef
  have hFm : ∀ t < n, Measurable (F t) := by
    intro t ht
    have hfL := measurable_fL (K := K) (L := B.F.L) (t := t) (fun l => (B.F.adm t ht l).1) (B.F.meas t ht)
    have hR' := cRoundA_measL (n := n) (δ := δ) hKc hKconv hR hmw hfL
    have harg : Measurable fun p : ((PgSp d × B.F.Λ) × Df2Mode d) × (Fin d → ℝ) =>
        (((p.1.1.1, p.1.1.2, ((0, 0) : Adv d)), p.1.2, p.2, (0 : ℝ), (0 : ℝ)) :
          (PgSp d × B.F.Λ × Adv d) × Df2Mode d × (Fin d → ℝ) × ℝ × ℝ) := by
      fun_prop
    have hpt := measurable_fst.comp (hR'.comp harg)
    have hl : Measurable fun p : ((PgSp d × B.F.Λ) × Df2Mode d) × (Fin d → ℝ) => p.1.1.2 := by fun_prop
    have h := hfL.comp (hl.prodMk hpt)
    exact h
  have hZF : ∀ t < n, Z t = fun ω => F t (x t ω, W.xi t ω) := by
    intro t ht
    funext ω
    simp only [hZ, hFdef, hxdef, lossR, ht, ↓reduceIte]
    rw [refPlay_eq]
  have hZpast : ∀ t, ¬ t < n → Z t = fun _ => 0 := by
    intro t ht
    funext ω
    simp [hZ, lossR, ht]
  have hx : ∀ t < n, Measurable[ℱ t] (x t) := fun t ht =>
    ((hpos.mono (ℱ.mono (Nat.zero_le t)) le_rfl).prodMk (B.F.lam_meas t ht)).prodMk (hmode t)
  have hZm : ∀ t, StronglyMeasurable[ℱ (t + 1)] (Z t) := by
    intro t
    by_cases ht : t < n
    · have hm : Measurable[ℱ (t + 1)] (Z t) := by
        rw [hZF t ht]
        exact (hFm t ht).comp (((hx t ht).mono (ℱ.mono (Nat.le_succ t)) le_rfl).prodMk (hW.meas_xi t))
      exact hm.stronglyMeasurable
    · rw [hZpast t ht]
      exact stronglyMeasurable_const
  have hZ01 : ∀ t, ∀ᵐ ω ∂μ, Z t ω ∈ Set.Icc (0 : ℝ) 1 := fun t => Filter.Eventually.of_forall fun ω => by
    by_cases ht : t < n
    · simp only [hZ, lossR, ht, ↓reduceIte]
      exact fL_mem (B.F.adm t ht _) _
    · rw [hZpast t ht]
      exact ⟨le_rfl, zero_le_one⟩
  have hAz := df2AzumaEvent μ ℱ Z hZm hZ01 n (df2oPar d n δ).δe H.de_pos
  have hFR : ∀ t < n, μ[Z t | ℱ t] =ᵐ[μ] fun ω => ∫ z, F t (x t ω, z) ∂gaussK d := by
    intro t ht
    have hξ : Measurable (W.xi t) := (hW.meas_xi t).mono (ℱ.le _) le_rfl
    have hint : Integrable (fun ω => F t (x t ω, W.xi t ω)) μ := by
      refine (integrable_const (1 : ℝ)).mono'
        ((hFm t ht).comp (((hx t ht).mono (ℱ.le t) le_rfl).prodMk hξ)).aestronglyMeasurable
        (Filter.Eventually.of_forall fun ω => ?_)
      have h01 := fL_mem (B.F.adm t ht (B.F.lam t ω))
        (cRoundA n δ K (B.pos ω) (apAdv (0, 0)) (fL K B.F.L t (B.F.lam t ω)) 0 (W.xi t ω) 0 (B.mode δ t ω)).1
      rw [Real.norm_eq_abs, abs_of_nonneg h01.1]
      exact h01.2
    have h := lemmaFR Ω ((PgSp d × B.F.Λ) × Df2Mode d) (Fin d → ℝ) (ℱ t) μ (x t) (W.xi t) (F t) (ℱ.le t)
      (hx t ht) hξ (hW.xi_indep t) (hFm t ht) hint
    rw [hW.xi_law t] at h
    rw [hZF t ht]
    exact h
  have hmean : ∀ ω, B.Case δ ω → ∀ t < n, ∫ z, F t (x t ω, z) ∂gaussK d = B.mean δ t ω := by
    intro ω hcase t ht
    unfold mean
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    have hm := mode_ne_off hKconv hKc hcase heps0 heps1 t
    have hin := (cRoundA_good hKconv hKc hcase heps0 heps1 (apAdv (0, 0)) (fL K B.F.L t (B.F.lam t ω)) 0 z 0
      hm).1
    simp only [hFdef, hxdef]
    rw [fL_interior hin]
    unfold cRoundA
    rw [roundGa_fst_ap _ _ _ _ _ _ apCall, roundGa_fst _ _ _ _ _ _ _ (B.lossR t ω) _ 0 _ _ 0]
    rfl
  have hZcase : ∀ ω, B.Case δ ω → ∀ t < n, Z t ω = B.loss ω t (B.refPlay δ t ω) := by
    intro ω hcase t ht
    simp only [hZ, lossR, ht, ↓reduceIte]
    exact fL_interior (refPlay_interior hKconv hKc hcase heps0 heps1 t)
  have hall : ∀ᵐ ω ∂μ, ∀ t, t < n → μ[Z t | ℱ t] ω = ∫ z, F t (x t ω, z) ∂gaussK d := by
    refine ae_all_iff.mpr fun t => ?_
    by_cases ht : t < n
    · exact (hFR t ht).mono fun ω h _ => h
    · exact Filter.Eventually.of_forall fun ω h => absurd h ht
  refine (measure_mono_ae ?_).trans hAz
  filter_upwards [hall] with ω hω hmem
  obtain ⟨hcase, hnot⟩ := hmem
  show ∑ t ∈ Finset.range n, μ[Z t | ℱ t] ω + Real.sqrt (2 * n * Real.log (7 / (df2oPar d n δ).δe)) <
    ∑ t ∈ Finset.range n, Z t ω
  rw [Finset.sum_congr rfl fun t ht => (hω t (Finset.mem_range.mp ht)).trans
      (hmean ω hcase t (Finset.mem_range.mp ht)),
    Finset.sum_congr rfl fun t ht => hZcase ω hcase t (Finset.mem_range.mp ht)]
  unfold Az at hnot
  exact lt_of_not_ge hnot

end RunW

/-! ## Step 2 of SHADOW -/

/-- Step 2 of SHADOW on an abstract coupled world. -/
theorem coupStepPropW_holds : CoupStepPropW := by
  intro d n δ K Ω _ W B κ0 κ1 hreg hKc hKconv hW hpos hC hTV hB hκ0 hκ1 t
  have := hW.prob
  have hmode := RunW.mode_meas B δ hW hreg hKc hKconv hpos hB hC t
  have hX : Measurable[W.Fσ t] fun ω => (B.shR δ t ω, W.nz t ω) :=
    (RunW.shR_meas B δ hB hmode).prodMk (Measurable.of_comap_le le_sup_right : Measurable[W.Fσ t] (W.nz t))
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
  have hcore := step2_core (W.Fσ t) W.μ hFle (fun ω => (B.shR δ t ω, W.nz t ω)) hX (W.zz t) hZ
    (hW.z_indep t) D hD Bs hBs (fun x => κ0 + κ1 * |x.2|) (by fun_prop) (by
      rintro ⟨⟨m, r⟩, e⟩ ⟨hr, hb⟩
      rw [hW.z_law t]
      exact (hTV m r hr).trans (ENNReal.ofReal_le_ofReal hb))
  have hnm : Measurable (W.nz t) := (hW.meas_nz t).mono (W.𝓕.le _) le_rfl
  have hint := lintegral_affine_abs W.μ (W.nz t) hnm (hW.noise_abs_lintegral t) κ0 κ1 hκ0 hκ1
  refine le_trans (le_of_eq ?_) (hcore.trans hint)
  rfl

end AdversarialBco.Unified.World
