/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import Mathlib
public import AdversarialBco.Bit.ShadowIface
public import AdversarialBco.Bit.TV

@[expose] public section

/-!
# (O2): the maximal coupling `coupMax`

`coupMax m r z` couples the dither `V = m + r Z̃/2 ~ N(m, r²/4)` of the computed run with the reference law
`N(0, 1/4)`, from three standard Gaussians `z = (Z̃, G^U, G^W)`: with `U = Φ(G^U)` and `W = Φ(G^W)` (`Φ` the standard
Gaussian distribution function, `phiI`), it keeps `V` when `U p(V) ≤ q(V)` (`p`, `q` the two densities) and otherwise
draws from the normalised residual `(q - p)⁺` at `W`. The residual sampler `gR` is the jointly measurable
representation of the residual kernel `residK` by the uniform law on `[0, 1]` (Mathlib's
`Kernel.exists_measurable_map_eq_unitInterval`, the generalised inverse distribution function). At `r ≤ 0` the
coupling is `Z̃/2`.

* `coupLaw_coupMax : CoupLaw coupMax`, (O2-L): jointly Borel, and the law is `N(0, 1/4)` at every `(m, r)`;
* `coupTV_coupMax : CoupTV coupMax`, (O2-C): at `r > 0`, `coupMax m r z ≠ m + r z₀/2` with probability at most
  `∫ (p - q)⁺ ≤ tvB m r` (the coupling lemma, `tv_gauss` and `lintegral_sub_le` of Bit/TV.lean).
-/

open MeasureTheory ProbabilityTheory unitInterval Set Filter Topology
open scoped ENNReal NNReal

namespace AdversarialBco.Bit.Cpl.MaxCoup

/-- The standard Gaussian distribution function, as a map to `[0, 1]`. -/
noncomputable def phiI (x : ℝ) : I := ⟨cdf (gaussianReal 0 1) x, cdf_nonneg _ x, cdf_le_one _ x⟩

/-- The density of `N(m, r²/4)`. -/
noncomputable def pE (m r v : ℝ) : ℝ≥0∞ := gaussianPDF m ((r / 2) ^ 2).toNNReal v

/-- The density of `N(0, 1/4)`. -/
noncomputable def qE (v : ℝ) : ℝ≥0∞ := gaussianPDF 0 ((1 / 2 : ℝ) ^ 2).toNNReal v

/-- The mass of the residual `(q - p)⁺`. -/
noncomputable def cE (m r : ℝ) : ℝ≥0∞ := ∫⁻ y, (qE y - pE m r y)

/-- The density of the normalised residual (the reference density when the residual is null). -/
noncomputable def rho (m r y : ℝ) : ℝ≥0∞ := if cE m r = 0 then qE y else (qE y - pE m r y) / cE m r

/-! ## The self-contained lemmas (farm batch lean/farm/wev-lean/b1) -/

theorem measurable_phiI : Measurable phiI := by
  exact (cdf (gaussianReal 0 1)).mono.measurable.subtype_mk

theorem continuous_cdf_gauss : Continuous (cdf (gaussianReal 0 1)) := by
  set F := cdf (gaussianReal 0 1)
  have : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal one_ne_zero
  refine continuous_iff_continuousAt.2 fun x => ?_
  have hl : Function.leftLim F x = F x := by
    have h1 : F.measure {x} = 0 := by rw [measure_cdf]; exact measure_singleton x
    rw [StieltjesFunction.measure_singleton, ENNReal.ofReal_eq_zero] at h1
    exact le_antisymm (F.mono.leftLim_le le_rfl) (by linarith)
  have hr : Function.rightLim F x = F x := by
    exact (F.right_continuous x).rightLim_eq
  rw [F.mono.continuousAt_iff_leftLim_eq_rightLim, hl, hr]

theorem gauss_cdf_le (t : I) : gaussianReal 0 1 {x | cdf (gaussianReal 0 1) x ≤ t} = ENNReal.ofReal t := by
  set F := cdf (gaussianReal 0 1) with hF
  set A := {x | F x ≤ t} with hA
  have hcont : Continuous F := continuous_cdf_gauss
  rcases eq_or_lt_of_le t.2.2 with ht1 | ht1
  · have : A = univ := eq_univ_of_forall fun x => by
      show F x ≤ t; rw [ht1]; exact cdf_le_one _ x
    rw [this, measure_univ, ht1, ENNReal.ofReal_one]
  -- bounded above
  obtain ⟨x0, hx0⟩ : ∃ x0, (t : ℝ) < F x0 :=
    ((tendsto_cdf_atTop (μ := gaussianReal 0 1)).eventually (lt_mem_nhds ht1)).exists
  have hbdd : BddAbove A := ⟨x0, fun x hx => by
    by_contra h
    exact absurd (hx.trans_lt hx0) (not_lt.2 (F.mono (not_le.1 h).le))⟩
  rcases A.eq_empty_or_nonempty with hE | hne
  · rw [hE, measure_empty]
    have ht0 : (t : ℝ) = 0 := by
      rcases eq_or_lt_of_le t.2.1 with h | h
      · exact h.symm
      obtain ⟨x, hx⟩ : ∃ x, F x < t :=
        ((tendsto_cdf_atBot (μ := gaussianReal 0 1)).eventually (gt_mem_nhds h)).exists
      exact absurd (show x ∈ A from hx.le) (hE ▸ Set.notMem_empty x)
    rw [ht0, ENNReal.ofReal_zero]
  set s := sSup A with hs
  have hclosed : IsClosed A := isClosed_le hcont continuous_const
  have hsA : s ∈ A := hclosed.csSup_mem hne hbdd
  have hAeq : A = Iic s := by
    ext x
    refine ⟨fun hx => le_csSup hbdd hx, fun hx => ?_⟩
    exact (F.mono hx).trans hsA
  have hFs : F s = t := by
    refine le_antisymm hsA ?_
    have hT : Tendsto F (𝓝[>] s) (𝓝 (F s)) := hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    refine ge_of_tendsto hT (eventually_nhdsWithin_of_forall fun x hx => ?_)
    by_contra h
    exact absurd (le_csSup hbdd (show x ∈ A from (not_le.1 h).le)) (not_le.2 hx)
  rw [hAeq, ← ofReal_cdf, hFs]

theorem map_phiI : (gaussianReal 0 1).map phiI = (volume : Measure I) := by
  refine Measure.ext_of_Iic _ _ fun t => ?_
  rw [Measure.map_apply measurable_phiI measurableSet_Iic, unitInterval.volume_Iic]
  exact gauss_cdf_le t

theorem volume_mul_le (p q : ℝ≥0∞) (hp0 : p ≠ 0) (hpt : p ≠ ⊤) (hq : q ≠ ⊤) :
    volume {u : I | ENNReal.ofReal (u : ℝ) * p ≤ q} = min (q / p) 1 := by
  have hqp : q / p ≠ ⊤ := ENNReal.div_ne_top hq hp0
  set s := (q / p).toReal with hs
  have hiff : ∀ u : I, ENNReal.ofReal (u : ℝ) * p ≤ q ↔ (u : ℝ) ≤ s := fun u => by
    rw [← ENNReal.le_div_iff_mul_le (Or.inl hp0) (Or.inl hpt), ENNReal.ofReal_le_iff_le_toReal hqp]
  have hset : {u : I | ENNReal.ofReal (u : ℝ) * p ≤ q} = {u : I | (u : ℝ) ≤ s} := by
    ext u; exact hiff u
  rw [hset]
  rcases le_or_gt 1 s with h1 | h1
  · have : {u : I | (u : ℝ) ≤ s} = univ := eq_univ_of_forall fun u => u.2.2.trans h1
    rw [this, measure_univ, min_eq_right]
    rw [← ENNReal.ofReal_toReal hqp, ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal h1
  · have hs0 : 0 ≤ s := ENNReal.toReal_nonneg
    have : {u : I | (u : ℝ) ≤ s} = Iic (⟨s, hs0, h1.le⟩ : I) := by
      ext u; rfl
    rw [this, unitInterval.volume_Iic, min_eq_left]
    · exact ENNReal.ofReal_toReal hqp
    · rw [← ENNReal.ofReal_toReal hqp, ← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal h1.le

theorem measurable_cons {n : ℕ} (a : ℝ) : Measurable fun w : Fin n → ℝ => (Fin.cons a w : Fin (n + 1) → ℝ) := by
  refine measurable_pi_iff.2 fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [Fin.cons_zero]; exact measurable_const
  · simp only [Fin.cons_succ]; exact measurable_pi_apply j

theorem lintegral_pi_succ (n : ℕ) (μ : Measure ℝ) [IsProbabilityMeasure μ] (h : (Fin (n + 1) → ℝ) → ℝ≥0∞)
    (hh : Measurable h) :
    ∫⁻ z, h z ∂(Measure.pi fun _ : Fin (n + 1) => μ) =
      ∫⁻ a, ∫⁻ w, h (Fin.cons a w) ∂(Measure.pi fun _ : Fin n => μ) ∂μ := by
  have e := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) 0
  rw [← e.symm.lintegral_comp hh]
  rw [lintegral_prod (fun p => h ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm p))
    (hh.comp (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm.measurable).aemeasurable]
  refine lintegral_congr fun x => lintegral_congr fun y => ?_
  congr 1
  simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.consEquiv]

theorem lintegral_gaussK3 (h : (Fin 3 → ℝ) → ℝ≥0∞) (hh : Measurable h) :
    ∫⁻ z, h z ∂(Measure.pi fun _ : Fin 3 => gaussianReal 0 1) =
      ∫⁻ a, ∫⁻ b, ∫⁻ c, h ![a, b, c] ∂gaussianReal 0 1 ∂gaussianReal 0 1 ∂gaussianReal 0 1 := by
  rw [lintegral_pi_succ 2 _ h hh]
  refine lintegral_congr fun a => ?_
  rw [lintegral_pi_succ 1 _ (fun w => h (Fin.cons a w)) (hh.comp (measurable_cons a))]
  refine lintegral_congr fun b => ?_
  rw [lintegral_pi_succ 0 _ (fun w => h (Fin.cons a (Fin.cons b w)))
    ((hh.comp (measurable_cons a)).comp (measurable_cons b))]
  refine lintegral_congr fun c => ?_
  have : ∀ w : Fin 0 → ℝ, (Fin.cons a (Fin.cons b (Fin.cons c w)) : Fin 3 → ℝ) = ![a, b, c] := by
    intro w; ext i; fin_cases i <;> rfl
  simp only [this, lintegral_const, measure_univ, mul_one]

theorem map_coord0_half :
    (Measure.pi fun _ : Fin 3 => gaussianReal 0 1).map (fun z => z 0 / 2) = (gaussianReal 0 1).map (· / 2) := by
  calc
    (Measure.pi fun _ : Fin 3 => gaussianReal 0 1).map (fun z => z 0 / 2)
        = (Measure.pi fun _ : Fin 3 => gaussianReal 0 1).map ((· / 2) ∘ (fun z => z 0)) := rfl
    _ = ((Measure.pi fun _ : Fin 3 => gaussianReal 0 1).map (fun z => z 0)).map (· / 2) := by
      rw [← Measure.map_map (μ := Measure.pi fun _ : Fin 3 => gaussianReal 0 1)
        (measurable_div_const 2) (measurable_pi_apply 0)]
    _ = (gaussianReal 0 1).map (· / 2) := by
      rw [(MeasureTheory.measurePreserving_eval (fun (_ : Fin 3) => gaussianReal 0 1) 0).map_eq]

theorem map_affine (m r : ℝ) (hr : r ≠ 0) :
    (gaussianReal 0 1).map (fun a => m + r * a / 2) = gaussianReal m ((r / 2) ^ 2).toNNReal := by
  have hsqnonneg : 0 ≤ (r / 2) ^ 2 := sq_nonneg _
  have hmeas_mul : Measurable (fun (a : ℝ) => (r / 2) * a) := by fun_prop
  have hmeas_add : Measurable (fun (a : ℝ) => m + a) := by fun_prop
  have h_eq_fun : (fun (a : ℝ) => m + r * a / 2) = (fun (a : ℝ) => m + a) ∘ (fun (a : ℝ) => (r / 2) * a) := by
    ext a
    simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
  have h_nnreal_eq : NNReal.mk ((r / 2) ^ 2) hsqnonneg = ((r / 2) ^ 2).toNNReal := by
    ext; simp [hsqnonneg]
  rw [h_eq_fun, ← Measure.map_map hmeas_add hmeas_mul, gaussianReal_map_const_mul (r / 2)]
  simp
  rw [gaussianReal_map_const_add m]
  simp
  rw [h_nnreal_eq]

theorem map_half : (gaussianReal 0 1).map (· / 2) = gaussianReal 0 ((1 / 2 : ℝ) ^ 2).toNNReal := by
  rw [ProbabilityTheory.gaussianReal_map_div_const 2]
  have h : (0 : ℝ) / 2 = (0 : ℝ) := by norm_num
  rw [h]
  congr
  ext
  norm_num

theorem lintegral_tsub_comm {X : Type*} [MeasurableSpace X] (μ : Measure X) (f g : X → ℝ≥0∞)
    (hf : Measurable f) (hg : Measurable g) (hfg : ∫⁻ x, f x ∂μ = ∫⁻ x, g x ∂μ) (hg1 : ∫⁻ x, g x ∂μ ≠ ⊤) :
    ∫⁻ x, (f x - g x) ∂μ = ∫⁻ x, (g x - f x) ∂μ := by
  set min_fg := fun x => min (f x) (g x) with hmin_fg_def
  have hmin_meas : Measurable min_fg := Measurable.min hf hg
  have h_int_f : ∫⁻ x, f x ∂μ = ∫⁻ x, min_fg x ∂μ + ∫⁻ x, (f x - g x) ∂μ := by
    calc
      ∫⁻ x, f x ∂μ = ∫⁻ x, (min_fg x + (f x - g x)) ∂μ := by
        refine lintegral_congr (fun x => ?_)
        dsimp [min_fg]
        rw [add_comm, tsub_add_min]
      _ = ∫⁻ x, min_fg x ∂μ + ∫⁻ x, (f x - g x) ∂μ := lintegral_add_left hmin_meas _
  have h_int_g : ∫⁻ x, g x ∂μ = ∫⁻ x, min_fg x ∂μ + ∫⁻ x, (g x - f x) ∂μ := by
    calc
      ∫⁻ x, g x ∂μ = ∫⁻ x, (min_fg x + (g x - f x)) ∂μ := by
        refine lintegral_congr (fun x => ?_)
        dsimp [min_fg]
        calc
          g x = (g x - f x) + min (g x) (f x) := (tsub_add_min (a := g x) (b := f x)).symm
          _ = (g x - f x) + min (f x) (g x) := by rw [min_comm (g x) (f x)]
          _ = min (f x) (g x) + (g x - f x) := by rw [add_comm]
      _ = ∫⁻ x, min_fg x ∂μ + ∫⁻ x, (g x - f x) ∂μ := lintegral_add_left hmin_meas _
  have h_int_f_ne_top : ∫⁻ x, f x ∂μ ≠ ⊤ := by rwa [hfg]
  have h_int_min_ne_top : ∫⁻ x, min_fg x ∂μ ≠ ⊤ := by
    refine ne_top_of_le_ne_top h_int_f_ne_top ?_
    refine lintegral_mono (fun x => ?_)
    dsimp [min_fg]
    exact min_le_left _ _
  have h_cancel : AddLECancellable (∫⁻ x, min_fg x ∂μ) :=
    ENNReal.cancel_of_ne h_int_min_ne_top
  rw [h_int_f, h_int_g] at hfg
  exact h_cancel.inj_right.mp hfg

theorem measurable_pE : Measurable fun x : ℝ × ℝ × ℝ => pE x.1 x.2.1 x.2.2 := by
  have h : Measurable ((fun x : ℝ × ℝ≥0 × ℝ => gaussianPDF x.1 x.2.1 x.2.2) ∘
      fun x : ℝ × ℝ × ℝ => (x.1, ((x.2.1 / 2) ^ 2).toNNReal, x.2.2)) :=
    measurable_uncurry_gaussianPDF.comp (by fun_prop)
  exact h

theorem measurable_rho : Measurable fun x : (ℝ × ℝ) × ℝ => rho x.1.1 x.1.2 x.2 := by
  have hq : Measurable qE := measurable_gaussianPDF _ _
  have hp : Measurable fun x : (ℝ × ℝ) × ℝ => pE x.1.1 x.1.2 x.2 := by
    have h : Measurable ((fun x : ℝ × ℝ × ℝ => pE x.1 x.2.1 x.2.2) ∘
        fun x : (ℝ × ℝ) × ℝ => (x.1.1, x.1.2, x.2)) := measurable_pE.comp (by fun_prop)
    exact h
  have hd : Measurable fun x : (ℝ × ℝ) × ℝ => qE x.2 - pE x.1.1 x.1.2 x.2 := (hq.comp measurable_snd).sub hp
  have hc : Measurable fun x : ℝ × ℝ => cE x.1 x.2 := by
    have h := hd.lintegral_prod_right' (ν := (volume : Measure ℝ))
    exact h
  have hc' : Measurable fun x : (ℝ × ℝ) × ℝ => cE x.1.1 x.1.2 := hc.comp measurable_fst
  have hZ : MeasurableSet {x : (ℝ × ℝ) × ℝ | cE x.1.1 x.1.2 = 0} := hc' (measurableSet_singleton 0)
  unfold rho
  exact Measurable.ite hZ (hq.comp measurable_snd) (hd.div hc')

theorem lintegral_rho (m r : ℝ) : ∫⁻ y, rho m r y = 1 := by
  have hvQ : ((1 / 2 : ℝ) ^ 2).toNNReal ≠ 0 := by
    rw [Ne, Real.toNNReal_eq_zero, not_le]; positivity
  have hq1 : ∫⁻ y, qE y = 1 := lintegral_gaussianPDF_eq_one _ hvQ
  by_cases hc : cE m r = 0
  · simp only [rho, hc, ite_true]; exact hq1
  · have hct : cE m r ≠ ⊤ := by
      refine ne_top_of_le_ne_top (b := 1) ENNReal.one_ne_top ?_
      rw [← hq1]; exact lintegral_mono fun y => tsub_le_self
    simp only [rho, hc, ite_false, div_eq_mul_inv]
    rw [lintegral_mul_const' _ _ (ENNReal.inv_ne_top.2 hc)]
    exact ENNReal.mul_inv_cancel hc hct

theorem accept_mul (p q : ℝ≥0∞) (hp0 : p ≠ 0) (hpt : p ≠ ⊤) (hq : q ≠ ⊤) :
    min (q / p) 1 * p = min q p ∧ (1 - min (q / p) 1) * p = p - q := by
  by_cases h : q ≤ p
  · -- case q ≤ p
    have hdiv : q / p ≤ 1 := ENNReal.div_le_of_le_mul (by simpa [mul_one] using h)
    have hmin1 : min (q / p) 1 = q / p := min_eq_left hdiv
    have hmin2 : min q p = q := min_eq_left h
    have hsub_mul : (1 - q / p) * p = p - q := by
      calc
        (1 - q / p) * p = 1 * p - (q / p) * p := ENNReal.sub_mul (λ _ _ => hpt)
        _ = p - (q / p) * p := by simp
        _ = p - q := by rw [ENNReal.div_mul_cancel hp0 hpt]
    constructor
    · calc
        min (q / p) 1 * p = (q / p) * p := by rw [hmin1]
        _ = q := ENNReal.div_mul_cancel hp0 hpt
        _ = min q p := by rw [hmin2]
    · calc
        (1 - min (q / p) 1) * p = (1 - (q / p)) * p := by rw [hmin1]
        _ = p - q := hsub_mul
  · -- case p < q
    have hlt : p < q := lt_of_not_ge h
    have hle : p ≤ q := le_of_lt hlt
    have hdiv : 1 ≤ q / p := by
      rw [ENNReal.le_div_iff_mul_le (Or.inl hp0) (Or.inl hpt)]
      simpa [one_mul] using hle
    have hmin1 : min (q / p) 1 = 1 := min_eq_right hdiv
    have hmin2 : min q p = p := min_eq_right hle
    constructor
    · calc
        min (q / p) 1 * p = 1 * p := by rw [hmin1]
        _ = p := by simp
        _ = min q p := by rw [hmin2]
    · calc
        (1 - min (q / p) 1) * p = (1 - 1) * p := by rw [hmin1]
        _ = 0 * p := by simp
        _ = 0 := by simp
        _ = p - q := by rw [tsub_eq_zero_of_le hle]

theorem law_combine (m r : ℝ) (hr : r ≠ 0) (S : Set ℝ) (hS : MeasurableSet S) :
    (∫⁻ v in S, min (qE v) (pE m r v)) + (∫⁻ v, (pE m r v - qE v)) * ∫⁻ v in S, rho m r v =
      ∫⁻ v in S, qE v := by
  have hvP : ((r / 2) ^ 2).toNNReal ≠ 0 := by
    rw [Ne, Real.toNNReal_eq_zero, not_le]; positivity
  have hvQ : ((1 / 2 : ℝ) ^ 2).toNNReal ≠ 0 := by
    rw [Ne, Real.toNNReal_eq_zero, not_le]; positivity
  have hp1 : ∫⁻ v, pE m r v = 1 := lintegral_gaussianPDF_eq_one _ hvP
  have hq1 : ∫⁻ v, qE v = 1 := lintegral_gaussianPDF_eq_one _ hvQ
  have hpm : Measurable (pE m r) := measurable_gaussianPDF _ _
  have hqm : Measurable qE := measurable_gaussianPDF _ _
  have hcomm : ∫⁻ v, (pE m r v - qE v) = cE m r :=
    lintegral_tsub_comm volume (pE m r) qE hpm hqm (hp1.trans hq1.symm) (by rw [hq1]; exact ENNReal.one_ne_top)
  have hpt : ∀ v, min (qE v) (pE m r v) + (qE v - pE m r v) = qE v := fun v => by
    rcases le_total (qE v) (pE m r v) with h | h
    · rw [min_eq_left h, tsub_eq_zero_of_le h, add_zero]
    · rw [min_eq_right h, add_tsub_cancel_of_le h]
  rw [hcomm]
  by_cases hc : cE m r = 0
  · rw [hc, zero_mul, add_zero]
    have hae : ∀ᵐ v ∂(volume : Measure ℝ), qE v - pE m r v = 0 :=
      (lintegral_eq_zero_iff (hqm.sub hpm)).1 hc
    refine setLIntegral_congr_fun_ae hS ?_
    filter_upwards [hae] with v hv _
    have h := hpt v
    rw [hv, add_zero] at h
    exact h
  · have hct : cE m r ≠ ⊤ := by
      refine ne_top_of_le_ne_top (b := 1) ENNReal.one_ne_top ?_
      rw [← hq1]; exact lintegral_mono fun y => tsub_le_self
    simp only [rho, hc, ite_false, div_eq_mul_inv]
    rw [lintegral_mul_const' _ _ (ENNReal.inv_ne_top.2 hc), mul_comm, mul_assoc, ENNReal.inv_mul_cancel hc hct,
      mul_one, ← lintegral_add_left (hqm.min hpm)]
    exact lintegral_congr fun v => hpt v

theorem tsub_le_tvB (m r : ℝ) (hr : 0 < r) :
    ∫⁻ v, (pE m r v - qE v) ≤ ENNReal.ofReal ((|r - 1| + |m|) / min r 1) := by
  have hvP : ((r / 2) ^ 2).toNNReal ≠ 0 := by
    rw [Ne, Real.toNNReal_eq_zero, not_le]; positivity
  have hvQ : ((1 / 2 : ℝ) ^ 2).toNNReal ≠ 0 := by
    rw [Ne, Real.toNNReal_eq_zero, not_le]; positivity
  show ∫⁻ v, (gaussianPDF m ((r / 2) ^ 2).toNNReal v - gaussianPDF 0 ((1 / 2 : ℝ) ^ 2).toNNReal v) ≤ _
  refine AdversarialBco.Bit.lintegral_sub_le volume (gaussianPDF m ((r / 2) ^ 2).toNNReal)
    (gaussianPDF 0 ((1 / 2 : ℝ) ^ 2).toNNReal) (measurable_gaussianPDF _ _) (measurable_gaussianPDF _ _) ?_ _
    fun S hS => ?_
  · rw [lintegral_gaussianPDF_eq_one _ hvQ]
    exact ENNReal.one_ne_top
  · rw [← gaussianReal_of_var_ne_zero _ hvP, ← gaussianReal_of_var_ne_zero _ hvQ]
    exact (AdversarialBco.Bit.tv_gauss m r hr S hS).1

/-! ## The residual kernel and its sampler -/

/-- The residual kernel: at the shift `(m, r)`, the law with density `rho m r`. -/
noncomputable def residK : Kernel (ℝ × ℝ) ℝ :=
  (Kernel.const (ℝ × ℝ) (volume : Measure ℝ)).withDensity fun x y => rho x.1 x.2 y

theorem residK_apply (x : ℝ × ℝ) (S : Set ℝ) : residK x S = ∫⁻ y in S, rho x.1 x.2 y := by
  rw [residK, Kernel.withDensity_apply' _ measurable_rho, Kernel.const_apply]

instance : IsMarkovKernel residK :=
  ⟨fun x => ⟨by rw [residK_apply, Measure.restrict_univ, lintegral_rho]⟩⟩

theorem exists_gR :
    ∃ f : ℝ × ℝ → I → ℝ, Measurable (Function.uncurry f) ∧ ∀ a, volume.map (f a) = residK a :=
  Kernel.exists_measurable_map_eq_unitInterval residK

/-- The residual sampler: `gR (m, r) W` has law `residK (m, r)` for `W` uniform on `[0, 1]`. -/
noncomputable def gR : ℝ × ℝ → I → ℝ := Classical.choose exists_gR

theorem measurable_gR : Measurable (Function.uncurry gR) := (Classical.choose_spec exists_gR).1

theorem map_gR (x : ℝ × ℝ) : volume.map (gR x) = residK x := (Classical.choose_spec exists_gR).2 x

end AdversarialBco.Bit.Cpl.MaxCoup

namespace AdversarialBco.Bit.Cpl

open MaxCoup

open Classical in
/-- The maximal coupling: from `z = (Z̃, G^U, G^W)`, keep `V = m + r Z̃/2` when
`Φ(G^U) p(V) ≤ q(V)`, else draw the residual at `Φ(G^W)`; `Z̃/2` at `r ≤ 0`. -/
noncomputable def coupMax (m r : ℝ) (z : Fin 3 → ℝ) : ℝ :=
  if r ≤ 0 then z 0 / 2
  else if ENNReal.ofReal (phiI (z 1) : ℝ) * pE m r (m + r * z 0 / 2) ≤ qE (m + r * z 0 / 2) then
    m + r * z 0 / 2
  else gR (m, r) (phiI (z 2))

end AdversarialBco.Bit.Cpl

namespace AdversarialBco.Bit.Cpl.MaxCoup

open Cpl

theorem var_ne_zero {r : ℝ} (hr : r ≠ 0) : ((r / 2) ^ 2).toNNReal ≠ 0 := by
  rw [Ne, Real.toNNReal_eq_zero, not_le]; positivity

theorem measurable_qE : Measurable qE := measurable_gaussianPDF _ _

theorem measurable_pE_comp {α : Type*} [MeasurableSpace α] {f g h : α → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hh : Measurable h) : Measurable fun x => pE (f x) (g x) (h x) := by
  have h1 : Measurable ((fun x : ℝ × ℝ × ℝ => pE x.1 x.2.1 x.2.2) ∘ fun x => (f x, g x, h x)) :=
    measurable_pE.comp (hf.prodMk (hg.prodMk hh))
  exact h1

theorem measurable_pE_mr (m r : ℝ) : Measurable (pE m r) :=
  measurable_pE_comp (f := fun _ => m) (g := fun _ => r) measurable_const measurable_const measurable_id

theorem pE_ne_zero (m r v : ℝ) (hr : r ≠ 0) : pE m r v ≠ 0 := (gaussianPDF_pos _ (var_ne_zero hr) v).ne'

theorem pE_ne_top (m r v : ℝ) : pE m r v ≠ ⊤ := gaussianPDF_ne_top

theorem qE_ne_top (v : ℝ) : qE v ≠ ⊤ := gaussianPDF_ne_top

theorem measurableSet_accT (p q : ℝ≥0∞) : MeasurableSet {u : I | ENNReal.ofReal (u : ℝ) * p ≤ q} :=
  measurableSet_le ((ENNReal.measurable_ofReal.comp measurable_subtype_coe).mul_const p) measurable_const

theorem measurableSet_acc (p q : ℝ≥0∞) : MeasurableSet {b : ℝ | ENNReal.ofReal (phiI b : ℝ) * p ≤ q} :=
  measurable_phiI (measurableSet_accT p q)

/-- The acceptance probability: `P(Φ(G) p ≤ q) = min (q/p) 1`. -/
theorem gauss_acc (p q : ℝ≥0∞) (hp0 : p ≠ 0) (hpt : p ≠ ⊤) (hq : q ≠ ⊤) :
    gaussianReal 0 1 {b | ENNReal.ofReal (phiI b : ℝ) * p ≤ q} = min (q / p) 1 := by
  have h : {b : ℝ | ENNReal.ofReal (phiI b : ℝ) * p ≤ q} = phiI ⁻¹' {u : I | ENNReal.ofReal (u : ℝ) * p ≤ q} := rfl
  rw [h, ← Measure.map_apply measurable_phiI (measurableSet_accT p q), map_phiI, volume_mul_le p q hp0 hpt hq]

/-- The residual draw `gR x (Φ(G^W))` has law `residK x`. -/
theorem lintegral_ind_gR (x : ℝ × ℝ) (S : Set ℝ) (hS : MeasurableSet S) :
    ∫⁻ c, S.indicator 1 (gR x (phiI c)) ∂gaussianReal 0 1 = residK x S := by
  have hg : Measurable (gR x) := measurable_gR.comp measurable_prodMk_left
  have h1 : Measurable (gR x ∘ phiI) := hg.comp measurable_phiI
  have h2 := lintegral_map (μ := gaussianReal 0 1) (measurable_one.indicator hS) h1
  simp only [Function.comp_apply] at h2
  rw [← h2, ← Measure.map_map hg measurable_phiI, map_phiI, map_gR, lintegral_indicator_one hS]

theorem coupMax_vec (m r a b c : ℝ) (hr : 0 < r) :
    coupMax m r ![a, b, c] =
      if ENNReal.ofReal (phiI b : ℝ) * pE m r (m + r * a / 2) ≤ qE (m + r * a / 2) then m + r * a / 2
      else gR (m, r) (phiI c) := by
  rw [coupMax, ite_eq_right (not_le.mpr hr)]
  rfl

theorem measurable_coupMax : Measurable fun x : ℝ × ℝ × (Fin 3 → ℝ) => coupMax x.1 x.2.1 x.2.2 := by
  have hV : Measurable fun x : ℝ × ℝ × (Fin 3 → ℝ) => x.1 + x.2.1 * x.2.2 0 / 2 := by fun_prop
  have hp : Measurable fun x : ℝ × ℝ × (Fin 3 → ℝ) => pE x.1 x.2.1 (x.1 + x.2.1 * x.2.2 0 / 2) :=
    measurable_pE_comp measurable_fst (measurable_fst.comp measurable_snd) hV
  have hq : Measurable fun x : ℝ × ℝ × (Fin 3 → ℝ) => qE (x.1 + x.2.1 * x.2.2 0 / 2) := measurable_qE.comp hV
  have hU : Measurable fun x : ℝ × ℝ × (Fin 3 → ℝ) => ENNReal.ofReal (phiI (x.2.2 1) : ℝ) :=
    ENNReal.measurable_ofReal.comp (measurable_subtype_coe.comp (measurable_phiI.comp (by fun_prop)))
  have hA : MeasurableSet {x : ℝ × ℝ × (Fin 3 → ℝ) |
      ENNReal.ofReal (phiI (x.2.2 1) : ℝ) * pE x.1 x.2.1 (x.1 + x.2.1 * x.2.2 0 / 2) ≤
        qE (x.1 + x.2.1 * x.2.2 0 / 2)} :=
    measurableSet_le (hU.mul hp) hq
  have hR : MeasurableSet {x : ℝ × ℝ × (Fin 3 → ℝ) | x.2.1 ≤ 0} :=
    measurableSet_le (measurable_fst.comp measurable_snd) measurable_const
  have hG : Measurable fun x : ℝ × ℝ × (Fin 3 → ℝ) => gR (x.1, x.2.1) (phiI (x.2.2 2)) :=
    measurable_gR.comp ((measurable_fst.prodMk (measurable_fst.comp measurable_snd)).prodMk
      (measurable_phiI.comp (by fun_prop)))
  unfold coupMax
  exact Measurable.ite hR (by fun_prop) (Measurable.ite hA hV hG)

/-- The pointwise algebra of the acceptance step, under the density `p` of the dither. -/
theorem dens_split (m r : ℝ) (hr : r ≠ 0) (S : Set ℝ) (R : ℝ≥0∞) (v : ℝ) :
    pE m r v * (min (qE v / pE m r v) 1 * S.indicator 1 v + (1 - min (qE v / pE m r v) 1) * R) =
      S.indicator (fun v => min (qE v) (pE m r v)) v + (pE m r v - qE v) * R := by
  obtain ⟨h1, h2⟩ := accept_mul (pE m r v) (qE v) (pE_ne_zero m r v hr) (pE_ne_top m r v) (qE_ne_top v)
  rw [mul_add, ← mul_assoc, ← mul_assoc, mul_comm (pE m r v), h1, mul_comm (pE m r v), h2]
  by_cases hv : v ∈ S <;> simp [hv]

theorem measurable_alpha (m r : ℝ) : Measurable fun v => min (qE v / pE m r v) 1 :=
  (measurable_qE.div (measurable_pE_mr m r)).min measurable_const

/-- The integral over the dither of the accept/reject mixture. -/
theorem lintegral_dither (m r : ℝ) (hr : r ≠ 0) (S : Set ℝ) (hS : MeasurableSet S) (R : ℝ≥0∞) :
    ∫⁻ a, (min (qE (m + r * a / 2) / pE m r (m + r * a / 2)) 1 * S.indicator 1 (m + r * a / 2) +
        (1 - min (qE (m + r * a / 2) / pE m r (m + r * a / 2)) 1) * R) ∂gaussianReal 0 1 =
      (∫⁻ v in S, min (qE v) (pE m r v)) + (∫⁻ v, (pE m r v - qE v)) * R := by
  have hG : Measurable fun v => min (qE v / pE m r v) 1 * S.indicator 1 v + (1 - min (qE v / pE m r v) 1) * R :=
    ((measurable_alpha m r).mul (measurable_one.indicator hS)).add
      ((measurable_const.sub (measurable_alpha m r)).mul measurable_const)
  have hV : Measurable fun a : ℝ => m + r * a / 2 := by fun_prop
  have hpm : Measurable (pE m r) := measurable_pE_mr m r
  have e1 := lintegral_map (μ := gaussianReal 0 1) hG hV
  rw [map_affine m r hr, gaussianReal_of_var_ne_zero _ (var_ne_zero hr),
    lintegral_withDensity_eq_lintegral_mul _ (measurable_gaussianPDF _ _) hG] at e1
  rw [← e1]
  refine (lintegral_congr fun v => dens_split m r hr S R v).trans ?_
  rw [lintegral_add_left ((measurable_qE.min hpm).indicator hS), lintegral_indicator hS,
    lintegral_mul_const (f := fun v => pE m r v - qE v) R (hpm.sub measurable_qE)]

theorem coupMax_of_nonpos (m r : ℝ) (hr : r ≤ 0) : coupMax m r = fun z => z 0 / 2 := by
  funext z; rw [coupMax, ite_eq_left hr]

/-- The residual coordinate `G^W`: either the kept dither or the residual law. -/
theorem lintegral_resid (x : ℝ × ℝ) (P : Prop) [Decidable P] (V : ℝ) (S : Set ℝ) (hS : MeasurableSet S) :
    ∫⁻ c, S.indicator 1 (if P then V else gR x (phiI c)) ∂gaussianReal 0 1 =
      if P then S.indicator 1 V else residK x S := by
  split_ifs
  · rw [lintegral_const, measure_univ, mul_one]
  · exact lintegral_ind_gR x S hS

theorem lintegral_ite_pred (P : ℝ → Prop) [DecidablePred P] (hP : MeasurableSet {b | P b}) (X Y : ℝ≥0∞) :
    ∫⁻ b, (if P b then X else Y) ∂gaussianReal 0 1 =
      gaussianReal 0 1 {b | P b} * X + gaussianReal 0 1 {b | P b}ᶜ * Y := by
  have h : (fun b => if P b then X else Y) =
      fun b => {b | P b}.indicator (fun _ => X) b + {b | P b}ᶜ.indicator (fun _ => Y) b := by
    funext b; by_cases hb : P b <;> simp [hb]
  rw [h, lintegral_add_left (measurable_const.indicator hP), lintegral_indicator_const hP,
    lintegral_indicator_const hP.compl, mul_comm X, mul_comm Y]

/-- The acceptance coordinate `G^U`. -/
theorem lintegral_acc (m r v : ℝ) (hr : r ≠ 0) (X Y : ℝ≥0∞) :
    ∫⁻ b, (if ENNReal.ofReal (phiI b : ℝ) * pE m r v ≤ qE v then X else Y) ∂gaussianReal 0 1 =
      min (qE v / pE m r v) 1 * X + (1 - min (qE v / pE m r v) 1) * Y := by
  have hm := measurableSet_acc (pE m r v) (qE v)
  rw [lintegral_ite_pred _ hm, prob_compl_eq_one_sub hm,
    gauss_acc _ _ (pE_ne_zero m r v hr) (pE_ne_top m r v) (qE_ne_top v)]

end AdversarialBco.Bit.Cpl.MaxCoup

namespace AdversarialBco.Bit.Cpl

open MaxCoup

/-- (O2-L) for `coupMax`: jointly Borel, law `N(0, 1/4)` at every shift. -/
theorem coupLaw_coupMax : CoupLaw coupMax where
  meas := measurable_coupMax
  law m r := by
    rcases le_or_gt r 0 with hr | hr
    · rw [coupMax_of_nonpos m r hr, map_coord0_half]
    have hm : Measurable (coupMax m r) := measurable_coupMax.comp (by fun_prop : Measurable fun z => (m, r, z))
    ext S hS
    rw [Measure.map_apply hm hS, ← lintegral_indicator_one (hm hS)]
    have hind : Measurable ((coupMax m r ⁻¹' S).indicator (1 : (Fin 3 → ℝ) → ℝ≥0∞)) :=
      measurable_one.indicator (hm hS)
    rw [lintegral_gaussK3 _ hind]
    have hpt : ∀ a b c, (coupMax m r ⁻¹' S).indicator (1 : (Fin 3 → ℝ) → ℝ≥0∞) ![a, b, c] =
        S.indicator 1 (coupMax m r ![a, b, c]) := fun a b c => rfl
    calc ∫⁻ a, ∫⁻ b, ∫⁻ c, (coupMax m r ⁻¹' S).indicator 1 ![a, b, c]
          ∂gaussianReal 0 1 ∂gaussianReal 0 1 ∂gaussianReal 0 1
        = ∫⁻ a, (min (qE (m + r * a / 2) / pE m r (m + r * a / 2)) 1 * S.indicator 1 (m + r * a / 2) +
            (1 - min (qE (m + r * a / 2) / pE m r (m + r * a / 2)) 1) * residK (m, r) S) ∂gaussianReal 0 1 := by
          refine lintegral_congr fun a => ?_
          simp_rw [hpt, coupMax_vec _ _ _ _ _ hr, lintegral_resid _ _ _ _ hS]
          exact lintegral_acc m r _ hr.ne' _ _
      _ = (∫⁻ v in S, min (qE v) (pE m r v)) + (∫⁻ v, (pE m r v - qE v)) * residK (m, r) S :=
          lintegral_dither m r hr.ne' S hS _
      _ = ((gaussianReal 0 1).map (· / 2)) S := by
          rw [residK_apply, law_combine m r hr.ne' S hS, map_half, gaussianReal_apply _ (var_ne_zero one_ne_zero)]
          rfl

/-- (O2-C) for `coupMax`: at `r > 0` the coupled dither leaves `m + r z₀/2` only on the rejection event, of
probability `∫ (p - q)⁺ ≤ tvB m r`. -/
theorem coupTV_coupMax : CoupTV coupMax := by
  intro m r hr
  set A : Set (Fin 3 → ℝ) :=
    {z | ¬ (ENNReal.ofReal (phiI (z 1) : ℝ) * pE m r (m + r * z 0 / 2) ≤ qE (m + r * z 0 / 2))} with hAdef
  have hsub : {z | coupMax m r z ≠ m + r * z 0 / 2} ⊆ A := by
    intro z hz hacc
    exact hz (by rw [coupMax, ite_eq_right (not_le.mpr hr), ite_eq_left hacc])
  have hV : Measurable fun z : Fin 3 → ℝ => m + r * z 0 / 2 := by fun_prop
  have hpm : Measurable (pE m r) := measurable_pE_mr m r
  have hAm : MeasurableSet A :=
    (measurableSet_le ((ENNReal.measurable_ofReal.comp (measurable_subtype_coe.comp
      (measurable_phiI.comp (measurable_pi_apply 1)))).mul (hpm.comp hV)) (measurable_qE.comp hV)).compl
  have hpt : ∀ a b c : ℝ, A.indicator (1 : (Fin 3 → ℝ) → ℝ≥0∞) ![a, b, c] =
      if ENNReal.ofReal (phiI b : ℝ) * pE m r (m + r * a / 2) ≤ qE (m + r * a / 2) then 0 else 1 := by
    intro a b c
    by_cases h : ENNReal.ofReal (phiI b : ℝ) * pE m r (m + r * a / 2) ≤ qE (m + r * a / 2)
    · rw [ite_eq_left h, Set.indicator_of_notMem]; exact fun hA => hA h
    · rw [ite_eq_right h, Set.indicator_of_mem (show ![a, b, c] ∈ A from h)]; rfl
  calc gaussK 3 {z | coupMax m r z ≠ m + r * z 0 / 2} ≤ gaussK 3 A := measure_mono hsub
    _ = ∫⁻ a, ∫⁻ b, ∫⁻ c, A.indicator 1 ![a, b, c] ∂gaussianReal 0 1 ∂gaussianReal 0 1 ∂gaussianReal 0 1 := by
        rw [← lintegral_indicator_one hAm, lintegral_gaussK3 _ (measurable_one.indicator hAm)]
    _ = ∫⁻ a, (min (qE (m + r * a / 2) / pE m r (m + r * a / 2)) 1 * (∅ : Set ℝ).indicator 1 (m + r * a / 2) +
            (1 - min (qE (m + r * a / 2) / pE m r (m + r * a / 2)) 1) * 1) ∂gaussianReal 0 1 := by
        refine lintegral_congr fun a => ?_
        simp only [Set.indicator_empty]
        rw [← lintegral_acc m r _ hr.ne' 0 1]
        simp_rw [hpt, lintegral_const, measure_univ, mul_one]
    _ = ∫⁻ v, (pE m r v - qE v) := by
        rw [lintegral_dither m r hr.ne' ∅ MeasurableSet.empty 1, Measure.restrict_empty, lintegral_zero_measure,
          zero_add, mul_one]
    _ ≤ ENNReal.ofReal (tvB m r) := tsub_le_tvB m r hr

end AdversarialBco.Bit.Cpl
