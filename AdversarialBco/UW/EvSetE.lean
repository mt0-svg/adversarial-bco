/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.UW.Coup
public import AdversarialBco.UW.EvIface
public import AdversarialBco.UW.EvPar

@[expose] public section

/-!
# W-SETE and the epoch bound for P° of Theorem UW

The port of Unified/WorldShadow.lean (Proposition W-SETE) and of Unified/WorldShadowRef.lean (`RunW.epoch_bound`) to
the reference of Theorem UW, whose mode is `modeU` (the weighted round `cRoundW`):

* `zsU_law`, `condExp_zsU_F`, `condExp_zsU_H`, `eRefU_mean`, `eRefU_exp`, `setE_refU` (Proposition W-SETE): the
  coupled world with the draws `W.xi` and P°'s noise `e°_t = (ε_t + ζ*_t)/2` is an instance of setting (E). The
  proofs read the mode only through its measurability (`modeU_meas`), so they are those of Theorem U;
* `ext_kTh_measW`, `epochMeasVU`: (L1) for the epoch of P° at T4U (the extension at `parW d n ρ.u` with the body and
  the losses of the instance at the level `δc`);
* `epoch_boundU`: the virtual epoch of P° started before round `a < n` is an instance of `UWOnSetE`, so every bound
  of UW/EvIface.lean holds for it on the whole world.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped Matrix

namespace AdversarialBco.UW

open AdversarialBco.RealRAM AdversarialBco.Poly AdversarialBco.Poly.Layer2 AdversarialBco.Bit.Cpl
open AdversarialBco.Unified.World
open AdversarialBco.Poly.Conj1 (fL measurable_fL)

variable {d : ℕ}

/-! ## Proposition W-SETE -/

section SetE

variable {n : ℕ} {K : Set (E d)} {Ω : Type} [m0 : MeasurableSpace Ω] {W : CWorld d Ω} (B : RunW d n K W)
  (ρ : RefW)

/-- P°'s dither of round `t`. -/
noncomputable abbrev zsU (t : ℕ) (ω : Ω) : ℝ := B.zeta t ω (modeU B ρ t ω)

variable {B ρ}

theorem zsU_meas (hW : WorldLawOK W) (hB : BLMeasW B) (hC : CoupLaw B.Coup) {t : ℕ}
    (hmode : Measurable[W.𝓕 t] fun ω => modeU B ρ t ω) : Measurable (zsU B ρ t) :=
  (zetaU_meas B ρ hW hB hC hmode).mono (W.𝓕.le (t + 1)) le_rfl

/-- Lemma W-LAW (ii): the dither of round `t` has the law of `Z/2`. -/
theorem zsU_law (hW : WorldLawOK W) (hB : BLMeasW B) (hC : CoupLaw B.Coup) {t : ℕ}
    (hmode : Measurable[W.𝓕 t] fun ω => modeU B ρ t ω) :
    W.μ.map (zsU B ρ t) = (gaussianReal 0 1).map (· / 2) := by
  have := hW.prob
  have hshR := shRU_meas B ρ hB hmode
  have hx : Measurable (shRU B ρ t) := hshR.mono (hW.Fσ_le_m0 t) le_rfl
  have hz : Measurable (W.zz t) := (hW.meas_zz t).mono (W.𝓕.le (t + 1)) le_rfl
  have hind : IndepFun (shRU B ρ t) (W.zz t) W.μ := by
    rw [IndepFun_iff_Indep]
    exact (indep_of_indep_of_le_right (hW.z_indep t) hshR.comap_le).symm
  have hmap := (indepFun_iff_map_prod_eq_prod_map_map hx.aemeasurable hz.aemeasurable).mp hind
  rw [hW.z_law t] at hmap
  have hΦ : Measurable fun p : (ℝ × ℝ) × (Fin 3 → ℝ) => B.Coup p.1.1 p.1.2 p.2 :=
    hC.meas.comp (f := fun p : (ℝ × ℝ) × (Fin 3 → ℝ) => (p.1.1, p.1.2, p.2)) (by fun_prop)
  rw [show zsU B ρ t = (fun p : (ℝ × ℝ) × (Fin 3 → ℝ) => B.Coup p.1.1 p.1.2 p.2) ∘
    (fun ω => (shRU B ρ t ω, W.zz t ω)) from rfl, ← Measure.map_map hΦ (hx.prodMk hz), hmap]
  exact map_prod_fiber _ _ _ hΦ _ fun x => hC.law x.1 x.2

theorem integrable_zsU (hW : WorldLawOK W) (hB : BLMeasW B) (hC : CoupLaw B.Coup) {t : ℕ}
    (hmode : Measurable[W.𝓕 t] fun ω => modeU B ρ t ω) {G : ℝ → ℝ} (hGm : Measurable G)
    (hG : Integrable (fun y => G (y / 2)) (gaussianReal 0 1)) : Integrable (fun ω => G (zsU B ρ t ω)) W.μ := by
  have hγ : Integrable G ((gaussianReal 0 1).map (· / 2)) :=
    (integrable_map_measure (f := fun y : ℝ => y / 2) hGm.aestronglyMeasurable (by fun_prop)).mpr hG
  rw [← zsU_law hW hB hC hmode] at hγ
  exact hγ.comp_measurable (zsU_meas hW hB hC hmode)

/-- Lemma W-LAW (i) at `F*_t`. -/
theorem condExp_zsU_F (hW : WorldLawOK W) (hB : BLMeasW B) (hC : CoupLaw B.Coup) {t : ℕ}
    (hmode : Measurable[W.𝓕 t] fun ω => modeU B ρ t ω) {G : ℝ → ℝ} (hGm : Measurable G)
    (hint : Integrable (fun ω => G (zsU B ρ t ω)) W.μ) :
    W.μ[fun ω => G (zsU B ρ t ω) | W.Fσ t] =ᵐ[W.μ] fun _ => ∫ y, G (y / 2) ∂(gaussianReal 0 1) := by
  have := hW.prob
  have hz : Measurable (W.zz t) := (hW.meas_zz t).mono (W.𝓕.le (t + 1)) le_rfl
  have hΦ : Measurable fun p : (ℝ × ℝ) × (Fin 3 → ℝ) => G (B.Coup p.1.1 p.1.2 p.2) :=
    hGm.comp (hC.meas.comp (f := fun p : (ℝ × ℝ) × (Fin 3 → ℝ) => (p.1.1, p.1.2, p.2)) (by fun_prop))
  have h := lemmaFR Ω (ℝ × ℝ) (Fin 3 → ℝ) (W.Fσ t) W.μ (shRU B ρ t) (W.zz t)
    (fun p => G (B.Coup p.1.1 p.1.2 p.2)) (hW.Fσ_le_m0 t) (shRU_meas B ρ hB hmode) hz (hW.z_indep t) hΦ hint
  rw [hW.z_law t] at h
  exact h.trans (Filter.Eventually.of_forall fun ω => by dsimp only; exact integral_coup hC hGm _ _)

/-- Lemma W-LAW (i) at `H_t`. -/
theorem condExp_zsU_H (hW : WorldLawOK W) (hB : BLMeasW B) (hC : CoupLaw B.Coup) {t : ℕ}
    (hmode : Measurable[W.𝓕 t] fun ω => modeU B ρ t ω) {G : ℝ → ℝ} (hGm : Measurable G)
    (hint : Integrable (fun ω => G (zsU B ρ t ω)) W.μ) :
    W.μ[fun ω => G (zsU B ρ t ω) | W.HC t] =ᵐ[W.μ] fun _ => ∫ y, G (y / 2) ∂(gaussianReal 0 1) := by
  have := hW.prob
  have h1 := condExp_condExp_of_le (μ := W.μ) (f := fun ω => G (zsU B ρ t ω)) (WorldLawOK.HC_le_Fσ (W := W) t)
    (hW.Fσ_le_m0 t)
  have h2 := condExp_congr_ae (m := W.HC t) (condExp_zsU_F hW hB hC hmode hGm hint)
  rw [condExp_const (hW.HC_le_m0 t)] at h2
  exact h1.symm.trans h2

theorem eRefU_bound (t : ℕ) (ω : Ω) :
    Real.exp (eRefU B ρ t ω ^ 2) ≤ (1 / 2 : ℝ) * (Real.exp (W.nz t ω ^ 2) + Real.exp (zsU B ρ t ω ^ 2)) := by
  have := exp_sq_mid_le (W.nz t ω) (zsU B ρ t ω)
  simp only [eRefU] at this ⊢
  linarith

variable (hW : WorldLawOK W) (hB : BLMeasW B) (hC : CoupLaw B.Coup)
include hW hB hC

theorem eRefU_meas {t : ℕ} (hmode : Measurable[W.𝓕 t] fun ω => modeU B ρ t ω) :
    Measurable[W.𝓕 (t + 1)] (eRefU B ρ t) :=
  ((hW.meas_nz t).add (zetaU_meas B ρ hW hB hC hmode)).div_const 2

theorem integrable_eRefU_exp {t : ℕ} (hmode : Measurable[W.𝓕 t] fun ω => modeU B ρ t ω) :
    Integrable (fun ω => Real.exp (eRefU B ρ t ω ^ 2)) W.μ := by
  have hA := hW.e_int t
  have hB' := integrable_zsU hW hB hC hmode (G := fun y => Real.exp (y ^ 2)) (by fun_prop) gauss_exp_quarter.1
  refine ((hA.add hB').const_mul (1 / 2)).mono' ?_ (Filter.Eventually.of_forall fun ω => ?_)
  · exact (Real.measurable_exp.comp
      (((eRefU_meas hW hB hC hmode).mono (W.𝓕.le _) le_rfl).pow_const 2)).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact eRefU_bound t ω

theorem eRefU_mean {t : ℕ} (hmode : Measurable[W.𝓕 t] fun ω => modeU B ρ t ω) :
    W.μ[eRefU B ρ t | W.HC t] =ᵐ[W.μ] 0 := by
  have := hW.prob
  have he : eRefU B ρ t = (1 / 2 : ℝ) • (W.nz t + fun ω => zsU B ρ t ω) := by
    funext ω; simp only [eRefU, Pi.smul_apply, Pi.add_apply, smul_eq_mul]; ring
  have hnm : Measurable (W.nz t) := (hW.meas_nz t).mono (W.𝓕.le _) le_rfl
  have hF : Integrable (W.nz t) W.μ := integrable_of_exp_sq hnm (hW.e_int t)
  have hG : Integrable (fun ω => zsU B ρ t ω) W.μ :=
    integrable_zsU hW hB hC hmode (G := id) measurable_id
      ((memLp_id_gaussianReal 1).integrable le_rfl |>.div_const 2)
  have h1 := hW.e_mean t
  have h2 := condExp_zsU_H hW hB hC hmode (G := id) measurable_id hG
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

theorem eRefU_exp {t : ℕ} (hmode : Measurable[W.𝓕 t] fun ω => modeU B ρ t ω) :
    W.μ[fun ω => Real.exp (eRefU B ρ t ω ^ 2) | W.HC t] ≤ᵐ[W.μ] fun _ => 2 := by
  have hA := hW.e_int t
  have hB' := integrable_zsU hW hB hC hmode (G := fun y => Real.exp (y ^ 2)) (by fun_prop) gauss_exp_quarter.1
  have hmono := condExp_mono (m := W.HC t) (integrable_eRefU_exp hW hB hC hmode)
    ((hA.add hB').smul (1 / 2 : ℝ)) (Filter.Eventually.of_forall fun ω => by
      simpa only [Pi.smul_apply, Pi.add_apply, smul_eq_mul] using eRefU_bound t ω)
  have hsm := condExp_smul (μ := W.μ) (1 / 2 : ℝ)
    ((fun ω => Real.exp (W.nz t ω ^ 2)) + fun ω => Real.exp (zsU B ρ t ω ^ 2)) (W.HC t)
  have hadd := condExp_add hA hB' (W.HC t)
  have h1 := hW.e_exp t
  have h2 := condExp_zsU_H hW hB hC hmode (G := fun y => Real.exp (y ^ 2)) (by fun_prop) hB'
  have h0 := gauss_exp_quarter.2
  filter_upwards [hmono, hsm, hadd, h1, h2] with ω hm hs ha h1ω h2ω
  have hm2 := hm.trans_eq hs
  simp only [Pi.smul_apply, smul_eq_mul] at hm2
  rw [ha] at hm2
  simp only [Pi.add_apply] at hm2
  rw [h2ω] at hm2
  linarith

/-- **Proposition W-SETE** for P° of Theorem UW: the coupled world with the draws `W.xi` and P°'s noise is an
instance of setting (E). -/
theorem setE_refU (hd : 1 ≤ d) (hKc : IsClosed K) (hKconv : Convex ℝ K) (hpos : Measurable[W.𝓕 0] B.pos) :
    Df2SetE d W.μ W.𝓕 W.xi (fun t => eRefU B ρ t) := by
  have hmode := modeU_meas B ρ hW hd hKc hKconv hpos hB hC
  exact
  { xi_meas := hW.meas_xi
    xi_law := hW.xi_law
    xi_indep := hW.xi_indep
    e_meas := fun t => eRefU_meas hW hB hC (hmode t)
    e_int := fun t => integrable_eRefU_exp hW hB hC (hmode t)
    e_mean := fun t => eRefU_mean hW hB hC (hmode t)
    e_exp := fun t => eRefU_exp hW hB hC (hmode t) }

end SetE

/-! ## (L1) for the epoch of P° at T4U -/

/-- The extension at T4U of the losses of the instance, jointly measurable in the position, the loss parameter and the
point (`ext_kTh_measAd` with `parW d n u` in place of `df2oPar d n δ`). -/
theorem ext_kTh_measW {n : ℕ} {u δc : ℝ} {K : Set (E d)} (hKc : IsClosed K) (hKconv : Convex ℝ K)
    (hR : 1 ≤ (df2oPar d n δc).R) (hmw : 1 / (df2oPar d n δc).R ≤ df2Mw d)
    (heps0 : 0 < (parW d n u).eps) (heps1 : (parW d n u).eps < 1) {Λ : Type} [MeasurableSpace Λ]
    {L : ℕ → Λ → E d → ℝ} {a s : ℕ} (hconv : ∀ l, ConvexOn ℝ K (L (a + s) l))
    (hm : ∀ y ∈ interior K, Measurable fun l => L (a + s) l y) :
    Measurable fun p : (PgSp d × Λ) × E d =>
      df2Ext (parW d n u) (kTh n δc K p.1.1) (gTh n δc K (fun t => L t p.1.2) a s p.1.1) p.2 := by
  classical
  set P : (PgSp d × Λ) × E d → ℝ := fun p => df2Pip (parW d n u) (kTh n δc K p.1.1) p.2 with hPdef
  have hP : Measurable P :=
    measurable_const.max (((gauge_kTh_meas hKc hKconv PgMeas.pgGoodMeas hR hmw).comp
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).div_const _)
  set F : Λ × E d → ℝ := fun p => (interior K).piecewise (L (a + s) p.1) 0 p.2 with hFdef
  have hF : Measurable F := Conj1.measurable_piecewise_interior K (L (a + s)) hconv hm
  have hGs : MeasurableSet {p : (PgSp d × Λ) × E d | PgGood d K (df2oPar d n δc).R (some p.1.1)} :=
    (measurable_fst.comp measurable_fst) (PgMeas.pgGoodMeas d K _ hKconv hKc)
  have hpt : Measurable fun p : (PgSp d × Λ) × E d => pgMu p.1.1 + pgOp p.1.1 ((P p)⁻¹ • p.2) :=
    (pg_continuous d).2.2.measurable.comp ((measurable_fst.comp measurable_fst).prodMk (hP.inv.smul measurable_snd))
  have heq : (fun p : (PgSp d × Λ) × E d =>
      df2Ext (parW d n u) (kTh n δc K p.1.1) (gTh n δc K (fun t => L t p.1.2) a s p.1.1) p.2) =
      fun p => P p * (if PgGood d K (df2oPar d n δc).R (some p.1.1) then
          F (p.1.2, pgMu p.1.1 + pgOp p.1.1 ((P p)⁻¹ • p.2)) / 2 else 0) +
        2 * (P p - 1) / (parW d n u).eps := by
    funext p
    by_cases hq : PgGood d K (df2oPar d n δc).R (some p.1.1)
    · have hq' : PgGood d K (parW d n u).R (some p.1.1) := hq
      have hin := play_interior hKconv hq' heps0 heps1 p.2
      rw [parW_R d n u δc] at hin
      have hk := kTh_good (n := n) (δ := δc) hq
      simp only [hPdef, hk, df2Ext, gTh, hq, ↓reduceIte, hFdef]
      rw [Set.piecewise_eq_of_mem _ _ _ hin]
    · simp [df2Ext, hPdef, gTh, hq]
  rw [heq]
  refine (hP.mul (Measurable.ite hGs ((hF.comp ((measurable_snd.comp measurable_fst).prodMk hpt)).div_const _)
    measurable_const)).add ((measurable_const.mul (hP.sub measurable_const)).div_const _)

/-- (L1) with the checked advice for the epoch of P° of Theorem UW at the start round `a`. -/
theorem epochMeasVU {n : ℕ} {u δc : ℝ} {K : Set (E d)} (hKc : IsClosed K) (hKconv : Convex ℝ K)
    (hR : 1 ≤ (df2oPar d n δc).R) (hmw : 1 / (df2oPar d n δc).R ≤ df2Mw d) (heps0 : 0 < (parW d n u).eps)
    (heps1 : (parW d n u).eps < 1) {Λ : Type} [MeasurableSpace Λ] {L : ℕ → Λ → E d → ℝ}
    (hadm : ∀ t < n, ∀ l, AdmLoss K (L t l)) (hm : ∀ t < n, ∀ y ∈ interior K, Measurable fun l => L t l y)
    (a : ℕ) :
    Df2EpochMeasV (parW d n u) n (n - a) (fun x : PgSp d × Λ => kTh n δc K x.1)
      (fun s x => gTh n δc K (fun t => L t x.2) a s x.1) (apAdv (d := d)) := by
  refine ⟨?_, fun s hs => ?_, ?_⟩
  · have h := gauge_kTh_meas (n := n) (δ := δc) hKc hKconv PgMeas.pgGoodMeas hR hmw
    have h2 := h.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd :
      Measurable fun x : (PgSp d × Λ) × E d => (x.1.1, x.2))
    rw [Function.comp_def] at h2
    exact h2
  · exact ext_kTh_measW hKc hKconv hR hmw heps0 heps1 (fun l => (hadm (a + s) (by omega) l).1)
      (hm (a + s) (by omega))
  · have h := nextAdv_measurable (parW d n u) n (fun q => df2KepsOf (kTh n δc K q) (parW d n u).eps)
      (keps_kTh_graph hKc hKconv _)
    have h2 := h.comp (((measurable_fst.comp (measurable_fst.comp measurable_fst)).prodMk
      (measurable_snd.comp measurable_fst)).prodMk measurable_snd :
      Measurable fun x : ((PgSp d × Λ) × Adv d) × Df2St d × (Fin d → ℝ) × ℝ => ((x.1.1.1, x.1.2), x.2))
    rw [Function.comp_def] at h2
    exact h2

/-! ## The epoch bound -/

section Epoch

variable {n : ℕ} {K : Set (E d)} {Ω : Type} [m0 : MeasurableSpace Ω] {W : CWorld d Ω} {B : RunW d n K W}
  {ρ : RefW}

/-- **The epoch bound**: the virtual epoch of P° of Theorem UW started before round `a < n` is an instance of
`UWOnSetE`. -/
theorem epoch_boundU {k : ℝ} {Bad : (d n : ℕ) → RefW → Df2Ctx d → Df2Path d → ℕ → Prop} (h : UWOnSetE k Bad)
    (hW : WorldLawOK W) (hreg : RegimeW d n ρ) (hKc : IsClosed K) (hKconv : Convex ℝ K)
    (hpos : Measurable[W.𝓕 0] B.pos) (hC : CoupLaw B.Coup) (hB : BLMeasW B) {a : ℕ} (ha : a < n) :
    W.μ {ω | Bad d n ρ (ctxU B ρ a ω) (pathU B ρ a ω) (n - a)} ≤ ENNReal.ofReal (k * ρ.δc) := by
  have := hW.prob
  have hR := one_le_R_of n ρ.δc hreg.hd
  have hmw := inv_R_le_of n ρ.δc hreg.hd
  have heps0 := EvP.eps_pos hreg
  have heps1 := EvP.eps_lt_one hreg
  have hmode := modeU_meas B ρ hW hreg.hd hKc hKconv hpos hB hC
  have hE := setE_shift W.μ W.𝓕 W.xi (fun t => eRefU B ρ t) (setE_refU hW hB hC hreg.hd hKc hKconv hpos) a
  have hθ : ∀ s, Measurable[fshift W.𝓕 a s] fun ω => (B.pos ω, lamAtW n B.F.lam a s ω) := fun s =>
    (hpos.mono (W.𝓕.mono (Nat.zero_le _)) le_rfl).prodMk (RunW.lamAtW_meas ha s)
  have hψ : ∀ s, Measurable[fshift W.𝓕 a (s + 1)] fun ω => B.adv (a + s) ω (modeU B ρ (a + s) ω) := fun s =>
    advU_meas B ρ hB (hmode (a + s))
  exact h d n (n - a) ρ hreg (by omega) (Nat.sub_le n a) (PgSp d × B.F.Λ) (Adv d)
    (fun x => kTh n ρ.δc K x.1) (fun s x => gTh n ρ.δc K (fun t => B.F.L t x.2) a s x.1) apAdv
    (fun x => body_kTh hKc hKconv hR hmw x.1)
    (fun x s hs => adm_gTh (f := fun t => B.F.L t x.2) hKconv hKc hR hmw (B.F.adm (a + s) (by omega) x.2) x.1)
    (apAdv_spec hreg.hd) (epochMeasVU hKc hKconv hR hmw heps0 heps1 B.F.adm B.F.meas a)
    Ω W.μ inferInstance (fshift W.𝓕 a)
    (fun s ω => (B.pos ω, lamAtW n B.F.lam a s ω)) (fun s ω => B.adv (a + s) ω (modeU B ρ (a + s) ω))
    (fun s => W.xi (a + s)) (fun s => eRefU B ρ (a + s)) hθ hψ (fun _ _ => rfl) hE

end Epoch

end AdversarialBco.UW
