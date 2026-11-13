/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.ShadowMeas
public import AdversarialBco.Poly.Df2Layer2Proof
public import AdversarialBco.Poly.Df2LawProof

@[expose] public section

/-!
# Proposition W-SETE: setting (E) for the noise of P°

* `zc_law`, `zc_indep`: the coupling coordinates of round `t` are three standard Gaussians, independent of `F_t`;
* `ξc_law`, `ξc_indep`: the draw of round `t` is standard Gaussian and independent of `cσ d t`;
* `zs_law` (Lemma W-LAW (ii)): P°'s dither `ζ*_t` has the law of `Z/2`, `Z` standard Gaussian, from (O2-L) and the
  independence of the coupling coordinates from the shift (`map_prod_fiber`);
* `condExp_zs_F`, `condExp_zs_H` (Lemma W-LAW (i)): given `F_t`, or given `H_t = cσ d t ⊔ σ(ξ_t)`, the conditional
  expectation of `G(ζ*_t)` is the constant `∫ G(y/2) dγ(y)` (Lemma FR, then the tower property);
* `setE_ref` (Proposition W-SETE): `Df2SetE d μ* (cσ d) (ξc d) e°` with `e°_t = (ε_t + ζ*_t)/2`.
-/

open MeasureTheory ProbabilityTheory

namespace AdversarialBco.Bit.Cpl

open AdversarialBco.RealRAM AdversarialBco.Poly AdversarialBco.Poly.Layer2

variable {d : ℕ}

/-! ## The coordinates of round `t` -/

/-- The indices of the coupling coordinates of round `t`. -/
def zIdx (d t : ℕ) : Fin 3 → ℕ := ![cIdx d t (d + 1), cIdx d t (d + 3), cIdx d t (d + 4)]

theorem zc_eq (t : ℕ) : zc d t = fun ω : WΩ => fun k => ω.1 (zIdx d t k) := by
  funext ω k
  fin_cases k <;> rfl

theorem zIdx_inj (t : ℕ) : Function.Injective (zIdx d t) := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all [zIdx, cIdx]

theorem cIdx_not_mem_idxC (t c : ℕ) : cIdx d t c ∉ idxC d t := by
  rintro (h | h)
  · simp [cIdx, Nat.mul_mod_right] at h
  · simp only [cIdx, Set.mem_ofPred_eq] at h
    omega

theorem zIdx_ne_cIdx (t : ℕ) (k : Fin 3) {c : ℕ} (hc : c ≤ d) : zIdx d t k ≠ cIdx d t c := by
  fin_cases k <;> simp [zIdx, cIdx] <;> omega

theorem xiIdx_inj (t : ℕ) : Function.Injective fun c : Fin d => cIdx d t c := by
  intro a b h
  simp only [cIdx] at h
  exact Fin.ext (by omega)

theorem zc_law (ν : Measure (ℕ → ℝ)) [IsProbabilityMeasure ν] (t : ℕ) : (μs ν).map (zc d t) = gaussK 3 := by
  rw [zc_eq, show (fun ω : WΩ => fun k => ω.1 (zIdx d t k)) = (fun x : ℕ → ℝ => fun k => x (zIdx d t k)) ∘ Prod.fst
    from rfl, ← Measure.map_map (by fun_prop) measurable_fst, map_fst_world, gaussStream,
    infinitePi_comp_inj _ _ (zIdx_inj t), Measure.infinitePi_eq_pi]

theorem ξc_law (ν : Measure (ℕ → ℝ)) [IsProbabilityMeasure ν] (t : ℕ) : (μs ν).map (ξc d t) = gaussK d := by
  rw [show ξc d t = (fun x : ℕ → ℝ => fun c : Fin d => x (cIdx d t c)) ∘ Prod.fst from rfl,
    ← Measure.map_map (by fun_prop) measurable_fst, map_fst_world, gaussStream,
    infinitePi_comp_inj _ _ (xiIdx_inj t), Measure.infinitePi_eq_pi]

theorem zc_indep (ν : Measure (ℕ → ℝ)) [IsProbabilityMeasure ν] (t : ℕ) :
    Indep (MeasurableSpace.comap (zc d t) inferInstance) (Fσ d t) (μs ν) := by
  set S : Set ℕ := Set.range (zIdx d t)
  have h := indep_world ν S Sᶜ disjoint_compl_right
  have hS : ∀ i ∈ S, gσ i ≤ ⨆ i ∈ S, gσ i := fun i hi => le_iSup₂ (f := fun i (_ : i ∈ S) => gσ i) i hi
  have hT : ∀ i ∉ S, gσ i ≤ (⨆ i ∈ Sᶜ, gσ i) ⊔ MeasurableSpace.comap Prod.snd inferInstance := fun i hi =>
    (le_iSup₂ (f := fun i (_ : i ∈ Sᶜ) => gσ i) i hi).trans le_sup_left
  refine indep_of_indep_of_le_right (indep_of_indep_of_le_left h ?_) ?_
  · rw [zc_eq]
    exact (measurable_pi_of fun k => meas_coord _ (hS _ ⟨k, rfl⟩)).comap_le
  · refine sup_le (sup_le (sup_le ?_ ?_) ?_) ?_
    · refine iSup₂_le fun i hi => hT i ?_
      rintro ⟨k, rfl⟩
      fin_cases k <;> exact cIdx_not_mem_idxC t _ hi
    · exact le_sup_of_le_right (MeasurableSpace.comap_mono (pastNoise_le _))
    · refine (measurable_pi_of fun c => meas_coord _ (hT _ ?_)).comap_le
      rintro ⟨k, hk⟩
      exact zIdx_ne_cIdx t k (Nat.lt_succ_iff.mp c.2) hk
    · refine le_sup_of_le_right ?_
      have : Measurable[MeasurableSpace.comap Prod.snd inferInstance] fun ω : WΩ => ω.2 t :=
        (measurable_pi_apply t).comp (Measurable.of_comap_le le_rfl)
      exact this.comap_le

theorem ξc_indep (ν : Measure (ℕ → ℝ)) [IsProbabilityMeasure ν] (t : ℕ) :
    Indep (MeasurableSpace.comap (ξc d t) inferInstance) (cσ d t) (μs ν) := by
  set S : Set ℕ := Set.range fun c : Fin d => cIdx d t c
  have h := indep_world ν S Sᶜ disjoint_compl_right
  refine indep_of_indep_of_le_right (indep_of_indep_of_le_left h ?_) ?_
  · exact (measurable_pi_of fun c => meas_coord _
      (le_iSup₂ (f := fun i (_ : i ∈ S) => gσ i) _ ⟨c, rfl⟩)).comap_le
  · refine sup_le (iSup₂_le fun i hi => (le_iSup₂ (f := fun i (_ : i ∈ Sᶜ) => gσ i) i ?_).trans le_sup_left)
      (le_sup_of_le_right (MeasurableSpace.comap_mono (pastNoise_le _)))
    rintro ⟨c, rfl⟩
    exact cIdx_not_mem_idxC t c hi

/-! ## The law of the dither (Lemma W-LAW) -/

/-- A map of a product whose fibres all carry the second factor to the same law has that law. -/
theorem map_prod_fiber {X Z Y : Type*} [MeasurableSpace X] [MeasurableSpace Z] [MeasurableSpace Y] (ρ : Measure X)
    [IsProbabilityMeasure ρ] (κ : Measure Z) [SFinite κ] (Φ : X × Z → Y) (hΦ : Measurable Φ) (lam : Measure Y)
    (h : ∀ x, κ.map (fun z => Φ (x, z)) = lam) : (ρ.prod κ).map Φ = lam := by
  ext A hA
  rw [Measure.map_apply hΦ hA, Measure.prod_apply (hΦ hA)]
  have hx : ∀ x, κ (Prod.mk x ⁻¹' (Φ ⁻¹' A)) = lam A := fun x => by
    have hm : Measurable fun z => Φ (x, z) := hΦ.comp (measurable_const.prodMk measurable_id)
    rw [← h x, Measure.map_apply hm hA]
    rfl
  simp_rw [hx]
  simp

theorem integral_coup {Coup : ℝ → ℝ → (Fin 3 → ℝ) → ℝ} (hC : CoupLaw Coup) {G : ℝ → ℝ} (hG : Measurable G)
    (m r : ℝ) : ∫ z, G (Coup m r z) ∂gaussK 3 = ∫ y, G (y / 2) ∂(gaussianReal 0 1) := by
  have hc : Measurable (Coup m r) :=
    hC.meas.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))
  rw [← integral_map hc.aemeasurable hG.aestronglyMeasurable, hC.law m r,
    integral_map (by fun_prop) hG.aestronglyMeasurable]

section Run

variable {n : ℕ} {K : Set (E d)} (B : Run d n K) (δ : ℝ) (ν : Measure (ℕ → ℝ)) [IsProbabilityMeasure ν]

/-- P°'s dither of round `t`. -/
noncomputable abbrev Run.zs (t : ℕ) (ω : WΩ) : ℝ := B.zeta t ω (B.mode δ t ω)

/-- `H_t`, the sigma-field of (E3) at round `t`: the past and the draw of round `t`. -/
abbrev HC (d t : ℕ) : MeasurableSpace WΩ := cσ d t ⊔ MeasurableSpace.comap (ξc d t) inferInstance

theorem Fσ_le_m0 (t : ℕ) : Fσ d t ≤ (inferInstance : MeasurableSpace WΩ) := (Fσ_le t).trans ((cσ d).le (t + 1))

theorem HC_le_Fσ (t : ℕ) : HC d t ≤ Fσ d t := by
  refine sup_le (le_sup_left.trans le_sup_left) ?_
  have hg : Measurable[Fσ d t] (ξg d t) := Measurable.of_comap_le (le_sup_right.trans le_sup_left)
  exact (measurable_pi_of fun c => (measurable_pi_apply (Fin.castSucc c)).comp hg).comap_le

theorem HC_le_noise (t : ℕ) : HC d t ≤ MeasurableSpace.comap Prod.fst inferInstance ⊔
    MeasurableSpace.comap Prod.snd (pastNoise t) := by
  have hfst : ∀ i, gσ i ≤ MeasurableSpace.comap (Prod.fst : WΩ → ℕ → ℝ) inferInstance := fun i =>
    MeasurableSpace.comap_mono (measurable_pi_apply i).comap_le
  refine sup_le (sup_le ((iSup₂_le fun i _ => hfst i).trans le_sup_left) le_sup_right) ?_
  refine le_sup_of_le_left ?_
  rw [show ξc d t = (fun x : ℕ → ℝ => fun c : Fin d => x (cIdx d t c)) ∘ Prod.fst from rfl,
    ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono (Measurable.comap_le (by fun_prop))

variable {B δ}

theorem zs_meas (hB : BLMeas B) (hC : CoupLaw B.Coup) {t : ℕ} (hmode : Measurable[cσ d t] fun ω => B.mode δ t ω) :
    Measurable (B.zs δ t) :=
  (zeta_meas B δ hB hC hmode).mono ((cσ d).le (t + 1)) le_rfl

/-- Lemma W-LAW (ii): the dither of round `t` has the law of `Z/2`. -/
theorem zs_law (hB : BLMeas B) (hC : CoupLaw B.Coup) {t : ℕ} (hmode : Measurable[cσ d t] fun ω => B.mode δ t ω) :
    (μs ν).map (B.zs δ t) = (gaussianReal 0 1).map (· / 2) := by
  have hshR := shR_meas B δ hB hmode
  have hx : Measurable (B.shR δ t) := hshR.mono (Fσ_le_m0 t) le_rfl
  have hz : Measurable (zc d t) := (meas_zc t).mono ((cσ d).le (t + 1)) le_rfl
  have hind : IndepFun (B.shR δ t) (zc d t) (μs ν) := by
    rw [IndepFun_iff_Indep]
    exact (indep_of_indep_of_le_right (zc_indep ν t) hshR.comap_le).symm
  have hmap := (indepFun_iff_map_prod_eq_prod_map_map hx.aemeasurable hz.aemeasurable).mp hind
  rw [zc_law ν t] at hmap
  have hΦ : Measurable fun p : (ℝ × ℝ) × (Fin 3 → ℝ) => B.Coup p.1.1 p.1.2 p.2 :=
    hC.meas.comp (f := fun p : (ℝ × ℝ) × (Fin 3 → ℝ) => (p.1.1, p.1.2, p.2)) (by fun_prop)
  rw [show B.zs δ t = (fun p : (ℝ × ℝ) × (Fin 3 → ℝ) => B.Coup p.1.1 p.1.2 p.2) ∘
    (fun ω => (B.shR δ t ω, zc d t ω)) from rfl, ← Measure.map_map hΦ (hx.prodMk hz), hmap]
  exact map_prod_fiber _ _ _ hΦ _ fun x => hC.law x.1 x.2

theorem integrable_zs (hB : BLMeas B) (hC : CoupLaw B.Coup) {t : ℕ}
    (hmode : Measurable[cσ d t] fun ω => B.mode δ t ω) {G : ℝ → ℝ} (hGm : Measurable G)
    (hG : Integrable (fun y => G (y / 2)) (gaussianReal 0 1)) : Integrable (fun ω => G (B.zs δ t ω)) (μs ν) := by
  have hγ : Integrable G ((gaussianReal 0 1).map (· / 2)) :=
    (integrable_map_measure (f := fun y : ℝ => y / 2) hGm.aestronglyMeasurable (by fun_prop)).mpr hG
  rw [← zs_law ν hB hC hmode] at hγ
  exact hγ.comp_measurable (zs_meas hB hC hmode)

/-- Lemma W-LAW (i) at `F_t`. -/
theorem condExp_zs_F (hB : BLMeas B) (hC : CoupLaw B.Coup) {t : ℕ}
    (hmode : Measurable[cσ d t] fun ω => B.mode δ t ω) {G : ℝ → ℝ} (hGm : Measurable G)
    (hint : Integrable (fun ω => G (B.zs δ t ω)) (μs ν)) :
    (μs ν)[fun ω => G (B.zs δ t ω) | Fσ d t] =ᵐ[μs ν] fun _ => ∫ y, G (y / 2) ∂(gaussianReal 0 1) := by
  have hz : Measurable (zc d t) := (meas_zc t).mono ((cσ d).le (t + 1)) le_rfl
  have hΦ : Measurable fun p : (ℝ × ℝ) × (Fin 3 → ℝ) => G (B.Coup p.1.1 p.1.2 p.2) :=
    hGm.comp (hC.meas.comp (f := fun p : (ℝ × ℝ) × (Fin 3 → ℝ) => (p.1.1, p.1.2, p.2)) (by fun_prop))
  have h := lemmaFR WΩ (ℝ × ℝ) (Fin 3 → ℝ) (Fσ d t) (μs ν) (B.shR δ t) (zc d t)
    (fun p => G (B.Coup p.1.1 p.1.2 p.2)) (Fσ_le_m0 t) (shR_meas B δ hB hmode) hz (zc_indep ν t) hΦ hint
  rw [zc_law ν t] at h
  exact h.trans (Filter.Eventually.of_forall fun ω => by dsimp only; exact integral_coup hC hGm _ _)

/-- Lemma W-LAW (i) at `H_t`. -/
theorem condExp_zs_H (hB : BLMeas B) (hC : CoupLaw B.Coup) {t : ℕ}
    (hmode : Measurable[cσ d t] fun ω => B.mode δ t ω) {G : ℝ → ℝ} (hGm : Measurable G)
    (hint : Integrable (fun ω => G (B.zs δ t ω)) (μs ν)) :
    (μs ν)[fun ω => G (B.zs δ t ω) | HC d t] =ᵐ[μs ν] fun _ => ∫ y, G (y / 2) ∂(gaussianReal 0 1) := by
  have h1 := condExp_condExp_of_le (μ := μs ν) (f := fun ω => G (B.zs δ t ω)) (HC_le_Fσ (d := d) t)
    (Fσ_le_m0 (d := d) t)
  have h2 := condExp_congr_ae (m := HC d t) (condExp_zs_F ν hB hC hmode hGm hint)
  rw [condExp_const ((HC_le_Fσ (d := d) t).trans (Fσ_le_m0 t))] at h2
  exact h1.symm.trans h2

/-! ## Setting (E) for P°'s noise (Proposition W-SETE) -/

theorem eRef_bound (t : ℕ) (ω : WΩ) :
    Real.exp (B.eRef δ t ω ^ 2) ≤ (1 / 2 : ℝ) * (Real.exp (ω.2 t ^ 2) + Real.exp (B.zs δ t ω ^ 2)) := by
  have := exp_sq_mid_le (ω.2 t) (B.zs δ t ω)
  simp only [Run.eRef] at this ⊢
  linarith

variable (hν : NoiseOK ν) (hB : BLMeas B) (hC : CoupLaw B.Coup)
include hν hB hC

omit [IsProbabilityMeasure ν] hν in
theorem eRef_meas {t : ℕ} (hmode : Measurable[cσ d t] fun ω => B.mode δ t ω) :
    Measurable[cσ d (t + 1)] (B.eRef δ t) :=
  ((meas_noise_c t).add (zeta_meas B δ hB hC hmode)).div_const 2

theorem integrable_eRef_exp {t : ℕ} (hmode : Measurable[cσ d t] fun ω => B.mode δ t ω) :
    Integrable (fun ω => Real.exp (B.eRef δ t ω ^ 2)) (μs ν) := by
  have hA := integrable_noise_exp ν hν t
  have hB' := integrable_zs ν hB hC hmode (G := fun y => Real.exp (y ^ 2)) (by fun_prop) gauss_exp_quarter.1
  refine ((hA.add hB').const_mul (1 / 2)).mono' ?_ (Filter.Eventually.of_forall fun ω => ?_)
  · exact (Real.measurable_exp.comp (((eRef_meas hB hC hmode).mono ((cσ d).le _) le_rfl).pow_const 2)).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact eRef_bound t ω

theorem eRef_mean {t : ℕ} (hmode : Measurable[cσ d t] fun ω => B.mode δ t ω) :
    (μs ν)[B.eRef δ t | HC d t] =ᵐ[μs ν] 0 := by
  have he : B.eRef δ t = (1 / 2 : ℝ) • ((fun ω : WΩ => ω.2 t) + fun ω => B.zs δ t ω) := by
    funext ω; simp only [Run.eRef, Pi.smul_apply, Pi.add_apply, smul_eq_mul]; ring
  have hF := integrable_noise_world ν _ (integrable_noise_lin ν hν t)
  have hG : Integrable (fun ω => B.zs δ t ω) (μs ν) :=
    integrable_zs ν hB hC hmode (G := id) measurable_id
      ((memLp_id_gaussianReal 1).integrable le_rfl |>.div_const 2)
  have h1 := condExp_snd_eq_zero lemmaNZProd (pastNoise t) gaussStream ν (pastNoise_le _) _ (HC_le_noise (d := d) t)
    (fun ε => ε t) (integrable_noise_lin ν hν t) (hν.2 t).2.1
  have h2 := condExp_zs_H ν hB hC hmode (G := id) measurable_id hG
  have h0 : ∫ x, x / 2 ∂(gaussianReal 0 1) = 0 := by
    rw [integral_div, integral_id_gaussianReal, zero_div]
  simp only [id_eq] at h2
  rw [he]
  refine (condExp_smul _ _ _).trans ?_
  have hadd := condExp_add hF hG (HC d t)
  filter_upwards [hadd, h1, h2] with ω hω h1ω h2ω
  simp only [Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at hω h1ω h2ω ⊢
  rw [hω, Pi.add_apply, h1ω, h2ω, h0]
  simp

theorem eRef_exp {t : ℕ} (hmode : Measurable[cσ d t] fun ω => B.mode δ t ω) :
    (μs ν)[fun ω => Real.exp (B.eRef δ t ω ^ 2) | HC d t] ≤ᵐ[μs ν] fun _ => 2 := by
  have hA := integrable_noise_exp ν hν t
  have hB' := integrable_zs ν hB hC hmode (G := fun y => Real.exp (y ^ 2)) (by fun_prop) gauss_exp_quarter.1
  have hmono := condExp_mono (m := HC d t) (integrable_eRef_exp ν hν hB hC hmode)
    ((hA.add hB').smul (1 / 2 : ℝ)) (Filter.Eventually.of_forall fun ω => by
      simpa only [Pi.smul_apply, Pi.add_apply, smul_eq_mul] using eRef_bound t ω)
  have hsm := condExp_smul (μ := μs ν) (1 / 2 : ℝ)
    ((fun ω : WΩ => Real.exp (ω.2 t ^ 2)) + fun ω => Real.exp (B.zs δ t ω ^ 2)) (HC d t)
  have hadd := condExp_add hA hB' (HC d t)
  have h1 := condExp_snd_le lemmaNZProd (pastNoise t) gaussStream ν (pastNoise_le _) _ (HC_le_noise (d := d) t)
    (fun ε => Real.exp (ε t ^ 2)) (hν.2 t).1 2 (hν.2 t).2.2
  have h2 := condExp_zs_H ν hB hC hmode (G := fun y => Real.exp (y ^ 2)) (by fun_prop) hB'
  have h0 := gauss_exp_quarter.2
  filter_upwards [hmono, hsm, hadd, h1, h2] with ω hm hs ha h1ω h2ω
  have hm2 := hm.trans_eq hs
  simp only [Pi.smul_apply, smul_eq_mul] at hm2
  rw [ha] at hm2
  simp only [Pi.add_apply] at hm2
  rw [h2ω] at hm2
  linarith

/-- Proposition W-SETE: the coupled world with the draws `ξc` and P°'s noise `e°` is an instance of setting (E). -/
theorem setE_ref (hreg : Regime d n δ) (hKc : IsClosed K) (hKconv : Convex ℝ K) (hpos : Measurable[cσ d 0] B.pos) :
    Df2SetE d (μs ν) (cσ d) (ξc d) (fun t => B.eRef δ t) := by
  have hmode := mode_meas B δ hreg hKc hKconv hpos hB hC
  exact
  { xi_meas := meas_ξc
    xi_law := ξc_law ν
    xi_indep := ξc_indep ν
    e_meas := fun t => eRef_meas hB hC (hmode t)
    e_int := fun t => integrable_eRef_exp ν hν hB hC (hmode t)
    e_mean := fun t => eRef_mean ν hν hB hC (hmode t)
    e_exp := fun t => eRef_exp ν hν hB hC (hmode t) }

end Run

end AdversarialBco.Bit.Cpl
