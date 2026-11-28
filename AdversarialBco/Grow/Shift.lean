/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Conj1Lower.StopNoise

@[expose] public section

/-!
# Route G: the change of measure by the product of the Gaussian round ratios

Route G, on the law of the sample `gameLaw π0 μ = π0 ⊗ gaussStream ⊗ μ` of Bayes.lean.
Shifts `m_t` of the noise, each reading the tip, the seed and `Z_0, ..., Z_{t-1}` only (`ReadsBefore t (m t)`):

* `lintegral_gauss_shift`: `∫ g(a + m) e^{-(m a + m^2/2)} dN(0, 1)(a) = ∫ g dN(0, 1)`;
* `lintegral_shiftAt`: one round, `E F = E[F(shift_t) e^{-(m_t Z_t + m_t^2/2)}]`;
* `lintegral_shiftAll`: `n` rounds, `E F = E[F(T_n) e^{-L_n}]`, with `T_n` the triangular shift `Z_t ↦ Z_t + m_t` for
  `t < n` (`shiftAll_noise`) and `L_n = Σ_{t < n} (m_t Z_t + m_t^2/2)` (`logLik`): the density of the null world
  against the sample's law is the product of the Gaussian round ratios;
* `integral_noiseSum_sq`: `E (Σ_{t < n} m_t Z_t)^2 = Σ_{t < n} E m_t^2` for bounded predictable weights;
* `measure_ge_shift`: for every measurable `S`, if `q0 ≤ P(T_n⁻¹ S)` with `q0 > 0` and `Σ_{t < n} E m_t^2 ≤ 2β`, then
  `P(S) ≥ q0 exp(-(β + (2β)^{1/2})/q0)` (Jensen for `exp` by its tangent line, Cauchy-Schwarz by the variance of
  `|M_n|`). No divergence, no chain rule.
-/

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

namespace AdversarialBco.Grow

open Lower.Bayes Lower.Stop

/-! ## The Gaussian translation -/

theorem gaussianPDF_mul_exp (m a : ℝ) :
    gaussianPDF 0 1 a * ENNReal.ofReal (Real.exp (-(m * a + m ^ 2 / 2))) = gaussianPDF 0 1 (a + m) := by
  rw [gaussianPDF, gaussianPDF, ← ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _)]
  congr 1
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- `∫ g(a + m) e^{-(m a + m^2/2)} dN(0, 1)(a) = ∫ g dN(0, 1)`. -/
theorem lintegral_gauss_shift (m : ℝ) {g : ℝ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ a, g (a + m) * ENNReal.ofReal (Real.exp (-(m * a + m ^ 2 / 2))) ∂gaussianReal 0 1 =
      ∫⁻ a, g a ∂gaussianReal 0 1 := by
  have he : Measurable (fun a : ℝ => ENNReal.ofReal (Real.exp (-(m * a + m ^ 2 / 2)))) := by fun_prop
  have hgm : Measurable (fun a : ℝ => g (a + m) * ENNReal.ofReal (Real.exp (-(m * a + m ^ 2 / 2)))) :=
    (hg.comp (measurable_add_const m)).mul he
  rw [gaussianReal_of_var_ne_zero _ one_ne_zero,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_gaussianPDF _ _) hgm,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_gaussianPDF _ _) hg]
  calc ∫⁻ a, (gaussianPDF 0 1 * fun a => g (a + m) * ENNReal.ofReal (Real.exp (-(m * a + m ^ 2 / 2)))) a
      = ∫⁻ a, (gaussianPDF 0 1 * g) (a + m) := by
        refine lintegral_congr fun a => ?_
        simp only [Pi.mul_apply]
        rw [← gaussianPDF_mul_exp m a]
        ring
    _ = ∫⁻ a, (gaussianPDF 0 1 * g) a := lintegral_add_right_eq_self _ m

variable {d : ℕ} {Ω : Type} [MeasurableSpace Ω]

/-! ## One round -/

/-- The sample with the noise of round `t` shifted by `m s`. -/
def shiftAt (t : ℕ) (m : Sample d Ω → ℝ) (s : Sample d Ω) : Sample d Ω :=
  (s.1, Function.update s.2.1 t (s.2.1 t + m s), s.2.2)

theorem measurable_shiftAt (t : ℕ) {m : Sample d Ω → ℝ} (hm : Measurable m) : Measurable (shiftAt t m) :=
  measurable_fst.prodMk (((measurable_update' (a := t)).comp
    ((measurable_fst.comp measurable_snd).prodMk ((measurable_noise t).add hm))).prodMk
      (measurable_snd.comp measurable_snd))

/-- One round of the change of measure: shifting `Z_t` by `m`, which does not read `Z_t`, has density
`e^{-(m Z_t + m^2/2)}`. -/
theorem lintegral_shiftAt (π0 : Measure (E d)) [IsProbabilityMeasure π0] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (t : ℕ) {m : Sample d Ω → ℝ} (hm : Measurable m) (hmr : ∀ s, m (resetZ t s) = m s)
    {F : Sample d Ω → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ s, F s ∂gameLaw π0 μ =
      ∫⁻ s, F (shiftAt t m s) * ENNReal.ofReal (Real.exp (-(m s * s.2.1 t + m s ^ 2 / 2))) ∂gameLaw π0 μ := by
  have hmu : ∀ θ Z b ω, m (θ, Function.update Z t b, ω) = m (θ, Z, ω) := fun θ Z b ω => by
    rw [← hmr (θ, Function.update Z t b, ω), resetZ_update, hmr]
  have hupd : Measurable (fun p : ℝ × Sample d Ω => (p.2.1, Function.update p.2.2.1 t p.1, p.2.2.2)) :=
    (measurable_fst.comp measurable_snd).prodMk (((measurable_update' (a := t)).comp
      ((measurable_fst.comp (measurable_snd.comp measurable_snd)).prodMk measurable_fst)).prodMk
        (measurable_snd.comp (measurable_snd.comp measurable_snd)))
  have hupd' : Measurable (fun p : ℝ × Sample d Ω =>
      ((p.2.1, Function.update p.2.2.1 t (p.1 + m p.2), p.2.2.2) : Sample d Ω)) :=
    (measurable_fst.comp measurable_snd).prodMk (((measurable_update' (a := t)).comp
      ((measurable_fst.comp (measurable_snd.comp measurable_snd)).prodMk
        (measurable_fst.add (hm.comp measurable_snd)))).prodMk
        (measurable_snd.comp (measurable_snd.comp measurable_snd)))
  have hmp : Measurable (fun p : ℝ × Sample d Ω => m p.2) := hm.comp measurable_snd
  have hE : Measurable (fun p : ℝ × Sample d Ω => ENNReal.ofReal (Real.exp (-(m p.2 * p.1 + m p.2 ^ 2 / 2)))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp ((hmp.mul measurable_fst).add
      ((hmp.pow_const 2).div_const 2)).neg)
  have k0 := lintegral_gameLaw_coord π0 μ t (F := fun p => F (p.2.1, Function.update p.2.2.1 t p.1, p.2.2.2))
    (hF.comp hupd) (fun a θ Z b ω => by simp only [Function.update_idem])
  have k1 := lintegral_gameLaw_coord π0 μ t
    (F := fun p => F (p.2.1, Function.update p.2.2.1 t (p.1 + m p.2), p.2.2.2) *
      ENNReal.ofReal (Real.exp (-(m p.2 * p.1 + m p.2 ^ 2 / 2))))
    ((hF.comp hupd').mul hE) (fun a θ Z b ω => by simp only [Function.update_idem, hmu])
  simp only [Function.update_eq_self] at k0
  rw [k0]
  refine Eq.trans ?_ k1.symm
  refine lintegral_congr fun s => ?_
  have hs : Measurable (fun a : ℝ => ((s.1, Function.update s.2.1 t a, s.2.2) : Sample d Ω)) :=
    measurable_const.prodMk (((measurable_update' (a := t)).comp
      (measurable_const.prodMk measurable_id)).prodMk measurable_const)
  exact (lintegral_gauss_shift (m s) (g := fun a => F (s.1, Function.update s.2.1 t a, s.2.2))
    (hF.comp hs)).symm

/-! ## `n` rounds -/

/-- The triangular shift: `Z_t ↦ Z_t + m_t` for `t < n`, the round `n - 1` first, so that each `m_t` reads the
unshifted noise before round `t`. -/
def shiftAll (m : ℕ → Sample d Ω → ℝ) : ℕ → Sample d Ω → Sample d Ω
  | 0 => id
  | n + 1 => fun s => shiftAll m n (shiftAt n (m n) s)

/-- The log of the density: `L_n = Σ_{t < n} (m_t Z_t + m_t^2/2)`. -/
noncomputable def logLik (m : ℕ → Sample d Ω → ℝ) (n : ℕ) (s : Sample d Ω) : ℝ :=
  ∑ t ∈ range n, (m t s * s.2.1 t + m t s ^ 2 / 2)

omit [MeasurableSpace Ω] in
theorem shiftAll_fst (m : ℕ → Sample d Ω → ℝ) (n : ℕ) (s : Sample d Ω) : (shiftAll m n s).1 = s.1 := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => exact (ih _).trans rfl

omit [MeasurableSpace Ω] in
theorem shiftAll_seed (m : ℕ → Sample d Ω → ℝ) (n : ℕ) (s : Sample d Ω) : (shiftAll m n s).2.2 = s.2.2 := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => exact (ih _).trans rfl

omit [MeasurableSpace Ω] in
/-- The noise of the shifted sample: `Z_t + m_t` for `t < n`, `Z_t` beyond. -/
theorem shiftAll_noise {m : ℕ → Sample d Ω → ℝ} (hmr : ∀ t, ReadsBefore t (m t)) (n : ℕ) (s : Sample d Ω) (t : ℕ) :
    (shiftAll m n s).2.1 t = if t < n then s.2.1 t + m t s else s.2.1 t := by
  induction n generalizing s with
  | zero => simp [shiftAll]
  | succ n ih =>
    show (shiftAll m n (shiftAt n (m n) s)).2.1 t = _
    rw [ih]
    rcases lt_trichotomy t n with h | h | h
    · have hne : t ≠ n := h.ne
      rw [ite_eq_left h, ite_eq_left (show t < n + 1 by omega)]
      simp only [shiftAt, Function.update_of_ne hne]
      congr 1
      exact hmr t _ _ rfl rfl fun i hi => by simp [Function.update_of_ne (show i ≠ n by omega)]
    · subst h
      rw [ite_eq_right (lt_irrefl _), ite_eq_left (Nat.lt_succ_self _)]
      simp [shiftAt]
    · rw [ite_eq_right (by omega), ite_eq_right (by omega)]
      simp [shiftAt, Function.update_of_ne (show t ≠ n by omega)]

theorem measurable_shiftAll {m : ℕ → Sample d Ω → ℝ} (hm : ∀ t, Measurable (m t)) (n : ℕ) :
    Measurable (shiftAll m n) := by
  induction n with
  | zero => exact measurable_id
  | succ n ih => exact ih.comp (measurable_shiftAt n (hm n))

theorem measurable_logLik {m : ℕ → Sample d Ω → ℝ} (hm : ∀ t, Measurable (m t)) (n : ℕ) :
    Measurable (logLik m n) :=
  Finset.measurable_sum _ fun t _ => ((hm t).mul (measurable_noise t)).add (((hm t).pow_const 2).div_const 2)

omit [MeasurableSpace Ω] in
theorem logLik_shiftAt {m : ℕ → Sample d Ω → ℝ} (hmr : ∀ t, ReadsBefore t (m t)) (n : ℕ) (s : Sample d Ω) :
    logLik m n (shiftAt n (m n) s) = logLik m n s := by
  unfold logLik
  refine Finset.sum_congr rfl fun t ht => ?_
  have ht' : t < n := Finset.mem_range.1 ht
  have h1 : m t (shiftAt n (m n) s) = m t s :=
    hmr t _ _ rfl rfl fun i hi => by simp [shiftAt, Function.update_of_ne (show i ≠ n by omega)]
  have h2 : (shiftAt n (m n) s).2.1 t = s.2.1 t := by simp [shiftAt, Function.update_of_ne (show t ≠ n by omega)]
  rw [h1, h2]

/-- `n` rounds of the change of measure: `E F = E[F(T_n) e^{-L_n}]`. -/
theorem lintegral_shiftAll (π0 : Measure (E d)) [IsProbabilityMeasure π0] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {m : ℕ → Sample d Ω → ℝ} (hm : ∀ t, Measurable (m t)) (hmr : ∀ t, ReadsBefore t (m t)) (n : ℕ)
    {F : Sample d Ω → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ s, F s ∂gameLaw π0 μ =
      ∫⁻ s, F (shiftAll m n s) * ENNReal.ofReal (Real.exp (-logLik m n s)) ∂gameLaw π0 μ := by
  induction n with
  | zero => simp [shiftAll, logLik]
  | succ n ih =>
    have hG : Measurable (fun s => F (shiftAll m n s) * ENNReal.ofReal (Real.exp (-logLik m n s))) :=
      (hF.comp (measurable_shiftAll hm n)).mul
        (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_logLik hm n).neg))
    rw [ih, lintegral_shiftAt π0 μ n (hm n) ((hmr n).resetZ le_rfl) hG]
    refine lintegral_congr fun s => ?_
    show F (shiftAll m n (shiftAt n (m n) s)) * ENNReal.ofReal (Real.exp (-logLik m n (shiftAt n (m n) s))) *
      ENNReal.ofReal (Real.exp (-(m n s * s.2.1 n + m n s ^ 2 / 2))) =
      F (shiftAll m n (shiftAt n (m n) s)) * ENNReal.ofReal (Real.exp (-logLik m (n + 1) s))
    rw [logLik_shiftAt hmr, mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 3
    simp only [logLik, Finset.sum_range_succ]
    ring

/-- The change of measure for an event: `P(S) = ∫_{T_n⁻¹ S} e^{-L_n} dP`. -/
theorem measure_eq_shift (π0 : Measure (E d)) [IsProbabilityMeasure π0] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {m : ℕ → Sample d Ω → ℝ} (hm : ∀ t, Measurable (m t)) (hmr : ∀ t, ReadsBefore t (m t)) (n : ℕ)
    {S : Set (Sample d Ω)} (hS : MeasurableSet S) :
    gameLaw π0 μ S =
      ∫⁻ s in shiftAll m n ⁻¹' S, ENNReal.ofReal (Real.exp (-logLik m n s)) ∂gameLaw π0 μ := by
  have h := lintegral_shiftAll π0 μ hm hmr n (measurable_one.indicator hS)
  rw [lintegral_indicator_one hS] at h
  rw [h, ← lintegral_indicator (measurable_shiftAll hm n hS)]
  refine lintegral_congr fun s => ?_
  by_cases hs : shiftAll m n s ∈ S
  · rw [Set.indicator_of_mem hs, Set.indicator_of_mem (show s ∈ shiftAll m n ⁻¹' S from hs)]
    simp
  · rw [Set.indicator_of_notMem hs, Set.indicator_of_notMem (show s ∉ shiftAll m n ⁻¹' S from hs), zero_mul]

/-! ## The second moment of a noise sum with bounded predictable weights -/

theorem memLp_weight_noise_le (π0 : Measure (E d)) [IsProbabilityMeasure π0] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {V : Sample d Ω → ℝ} (hVm : Measurable V) {w : ℝ} (hV : ∀ s, |V s| ≤ w) (t : ℕ) :
    MemLp (fun s => V s * s.2.1 t) 2 (gameLaw π0 μ) := by
  have h := (memLp_noise π0 μ t).const_mul w
  refine h.of_le (hVm.mul (measurable_noise t)).aestronglyMeasurable (ae_of_all _ fun s => ?_)
  have hw : 0 ≤ w := (abs_nonneg _).trans (hV s)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hw]
  exact mul_le_mul_of_nonneg_right (hV s) (abs_nonneg _)

theorem memLp_noiseSum_le (π0 : Measure (E d)) [IsProbabilityMeasure π0] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {V : ℕ → Sample d Ω → ℝ} {n : ℕ} (hVm : ∀ t, Measurable (V t)) {w : ℝ} (hV : ∀ t s, |V t s| ≤ w) :
    MemLp (noiseSum V n) 2 (gameLaw π0 μ) :=
  memLp_finsetSum _ fun t _ => memLp_weight_noise_le π0 μ (hVm t) (hV t) t

/-- `E (Σ_{t < n} V_t Z_t)^2 = Σ_{t < n} E V_t^2` for bounded predictable weights. -/
theorem integral_noiseSum_sq (π0 : Measure (E d)) [IsProbabilityMeasure π0] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {V : ℕ → Sample d Ω → ℝ} (hVm : ∀ t, Measurable (V t)) {w : ℝ}
    (hV : ∀ t s, |V t s| ≤ w) (hVr : ∀ t, ReadsBefore t (V t)) (n : ℕ) :
    ∫ s, noiseSum V n s ^ 2 ∂gameLaw π0 μ = ∑ t ∈ range n, ∫ s, V t s ^ 2 ∂gameLaw π0 μ := by
  have hG := isProbabilityMeasure_gameLaw π0 μ
  induction n with
  | zero => simp [noiseSum]
  | succ n ih =>
    have hM := memLp_noiseSum_le π0 μ (n := n) hVm hV
    have hVZ := memLp_weight_noise_le π0 μ (hVm n) (hV n) n
    have hMV : MemLp (fun s => noiseSum V n s * V n s) 2 (gameLaw π0 μ) := by
      have h := hM.const_mul w
      refine h.of_le ((measurable_noiseSum fun t _ => hVm t).mul (hVm n)).aestronglyMeasurable
        (ae_of_all _ fun s => ?_)
      have hw : 0 ≤ w := (abs_nonneg _).trans (hV n s)
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hw, mul_comm]
      exact mul_le_mul_of_nonneg_right (hV n s) (abs_nonneg _)
    have hcross : Integrable (fun s => noiseSum V n s * V n s * s.2.1 n) (gameLaw π0 μ) :=
      hMV.integrable_mul (memLp_noise π0 μ n)
    have hsq : Integrable (fun s => V n s ^ 2 * s.2.1 n ^ 2) (gameLaw π0 μ) := by
      refine hVZ.integrable_sq.congr (ae_of_all _ fun s => ?_)
      ring
    have hexp : ∀ s, noiseSum V (n + 1) s ^ 2 =
        noiseSum V n s ^ 2 + 2 * (noiseSum V n s * V n s * s.2.1 n) + V n s ^ 2 * s.2.1 n ^ 2 := fun s => by
      simp only [noiseSum, Finset.sum_range_succ]
      ring
    simp only [hexp]
    have hA : Integrable (fun s => noiseSum V n s ^ 2) (gameLaw π0 μ) := hM.integrable_sq
    have hB : Integrable (fun s => 2 * (noiseSum V n s * V n s * s.2.1 n)) (gameLaw π0 μ) := hcross.const_mul 2
    have hAB : Integrable (fun s => noiseSum V n s ^ 2 + 2 * (noiseSum V n s * V n s * s.2.1 n)) (gameLaw π0 μ) :=
      hA.add hB
    rw [integral_add hAB hsq, integral_add hA hB,
      integral_const_mul 2 (fun s => noiseSum V n s * V n s * s.2.1 n)]
    have h0 : ∫ s, noiseSum V n s * V n s * s.2.1 n ∂gameLaw π0 μ = 0 :=
      integral_mul_noise π0 μ n ((measurable_noiseSum fun t _ => hVm t).mul (hVm n))
        (((noiseSum_readsBefore fun t _ => hVr t).mul (hVr n)).resetZ le_rfl) hcross
    have h1 : ∫ s, V n s ^ 2 * s.2.1 n ^ 2 ∂gameLaw π0 μ = ∫ s, V n s ^ 2 ∂gameLaw π0 μ :=
      integral_mul_noise_sq π0 μ n ((hVm n).pow_const 2) (fun s => by rw [(hVr n).resetZ le_rfl s]) hsq
    rw [h0, h1, ih, Finset.sum_range_succ]
    ring

/-! ## Jensen and Cauchy-Schwarz -/

/-- Jensen for `exp` on a set, by the tangent line: `∫_S e^{-L} ≥ q e^{-(∫_S L)/q}`, `q = P(S) > 0`. -/
theorem lintegral_exp_neg_ge {α : Type} [MeasurableSpace α] (P : Measure α) [IsFiniteMeasure P] {S : Set α}
    (hq : 0 < P.real S) {L : α → ℝ} (hL : Integrable L P) :
    ENNReal.ofReal (P.real S * Real.exp (-(∫ s in S, L s ∂P) / P.real S)) ≤
      ∫⁻ s in S, ENNReal.ofReal (Real.exp (-L s)) ∂P := by
  set q := P.real S
  set c := -(∫ s in S, L s ∂P) / q
  set f : α → ℝ := fun s => Real.exp c * (1 - L s - c)
  have hf : Integrable f (P.restrict S) :=
    ((integrable_const 1).sub hL.restrict |>.sub (integrable_const c)).const_mul _
  have hfle : ∀ s, f s ≤ Real.exp (-L s) := fun s => by
    have h := Real.add_one_le_exp (-L s - c)
    have he : Real.exp c * Real.exp (-L s - c) = Real.exp (-L s) := by rw [← Real.exp_add]; ring_nf
    calc f s = Real.exp c * (-L s - c + 1) := by simp only [f]; ring
      _ ≤ Real.exp c * Real.exp (-L s - c) := mul_le_mul_of_nonneg_left h (Real.exp_pos c).le
      _ = Real.exp (-L s) := he
  have hint : ∫ s in S, f s ∂P = q * Real.exp c := by
    have hfe : ∀ s, f s = Real.exp c * (1 - c) - Real.exp c * L s := fun s => by simp only [f]; ring
    simp only [hfe]
    rw [integral_sub (integrable_const _) (hL.restrict.const_mul _), setIntegral_const, integral_const_mul]
    simp only [smul_eq_mul]
    have hq0 : q ≠ 0 := hq.ne'
    have : ∫ s in S, L s ∂P = -(q * c) := by simp only [c]; field_simp
    rw [this]
    ring
  rw [← hint]
  calc ENNReal.ofReal (∫ s in S, f s ∂P)
      ≤ ENNReal.ofReal (∫ s in S, max (f s) 0 ∂P) :=
        ENNReal.ofReal_le_ofReal (integral_mono hf hf.pos_part fun s => le_max_left _ _)
    _ = ∫⁻ s in S, ENNReal.ofReal (max (f s) 0) ∂P :=
        ofReal_integral_eq_lintegral_ofReal hf.pos_part (ae_of_all _ fun s => le_max_right _ _)
    _ ≤ ∫⁻ s in S, ENNReal.ofReal (Real.exp (-L s)) ∂P :=
        lintegral_mono fun s => ENNReal.ofReal_le_ofReal (max_le (hfle s) (Real.exp_pos _).le)

/-- `E|X| ≤ (E X^2)^{1/2}` on a probability space. -/
theorem integral_abs_le_sqrt {α : Type} [MeasurableSpace α] (P : Measure α) [IsProbabilityMeasure P] {X : α → ℝ}
    (hX : MemLp X 2 P) : ∫ s, |X s| ∂P ≤ Real.sqrt (∫ s, X s ^ 2 ∂P) := by
  have hA : MemLp (fun s => |X s|) 2 P := hX.abs
  have hv := variance_nonneg (fun s => |X s|) P
  rw [variance_eq_sub hA] at hv
  have h2 : ∫ s, ((fun s => |X s|) ^ 2) s ∂P = ∫ s, X s ^ 2 ∂P := by
    congr 1
    ext s
    simp [sq_abs]
  rw [h2] at hv
  exact Real.le_sqrt_of_sq_le (by linarith)

/-! ## The change of measure for an event -/

/-- **Route G's change of measure.** With shifts `m_t` bounded by `w`, reading the noise before round `t` only, and
`Σ_{t < n} E m_t^2 ≤ 2β`: for every measurable `S` with `q0 ≤ P(T_n⁻¹ S)`, `q0 > 0`,
`P(S) ≥ q0 exp(-(β + (2β)^{1/2})/q0)`. -/
theorem measure_ge_shift (π0 : Measure (E d)) [IsProbabilityMeasure π0] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {m : ℕ → Sample d Ω → ℝ} (hm : ∀ t, Measurable (m t)) (hmr : ∀ t, ReadsBefore t (m t)) {w : ℝ}
    (hmb : ∀ t s, |m t s| ≤ w) (n : ℕ) {β : ℝ}
    (hβ : ∑ t ∈ range n, ∫ s, m t s ^ 2 ∂gameLaw π0 μ ≤ 2 * β)
    {S : Set (Sample d Ω)} (hS : MeasurableSet S) {q0 : ℝ} (hq0 : 0 < q0)
    (hq : q0 ≤ (gameLaw π0 μ).real (shiftAll m n ⁻¹' S)) :
    ENNReal.ofReal (q0 * Real.exp (-(β + Real.sqrt (2 * β)) / q0)) ≤ gameLaw π0 μ S := by
  have hG := isProbabilityMeasure_gameLaw π0 μ
  set P := gameLaw π0 μ
  set S' := shiftAll m n ⁻¹' S
  set q := P.real S'
  have hqpos : 0 < q := hq0.trans_le hq
  -- the pieces of `L_n`
  have hM := memLp_noiseSum_le π0 μ (n := n) hm hmb
  have hsqi : ∀ t, Integrable (fun s => m t s ^ 2) P := fun t =>
    Integrable.of_bound ((hm t).pow_const 2).aestronglyMeasurable (w ^ 2) (ae_of_all _ fun s => by
      rw [Real.norm_eq_abs, abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (hmb t s) 2)
  have hQ : Integrable (fun s => ∑ t ∈ range n, m t s ^ 2 / 2) P :=
    integrable_finsetSum _ fun t _ => (hsqi t).div_const 2
  have hLeq : ∀ s, logLik m n s = noiseSum m n s + ∑ t ∈ range n, m t s ^ 2 / 2 := fun s => by
    simp only [logLik, noiseSum, Finset.sum_add_distrib]
  have hL : Integrable (logLik m n) P := by
    have : logLik m n = fun s => noiseSum m n s + ∑ t ∈ range n, m t s ^ 2 / 2 := funext hLeq
    rw [this]
    exact (hM.integrable one_le_two).add hQ
  -- `∫_{S'} L ≤ β + (2β)^{1/2}`
  have hQint : ∫ s, ∑ t ∈ range n, m t s ^ 2 / 2 ∂P ≤ β := by
    rw [integral_finsetSum _ fun t _ => (hsqi t).div_const 2]
    simp only [integral_div]
    rw [← Finset.sum_div]
    linarith
  have hMabs : ∫ s, |noiseSum m n s| ∂P ≤ Real.sqrt (2 * β) := by
    refine (integral_abs_le_sqrt P hM).trans (Real.sqrt_le_sqrt ?_)
    rw [integral_noiseSum_sq π0 μ hm hmb hmr n]
    exact hβ
  have hLS : ∫ s in S', logLik m n s ∂P ≤ β + Real.sqrt (2 * β) := by
    simp only [hLeq]
    rw [integral_add (hM.integrable one_le_two).restrict hQ.restrict]
    have h1 : ∫ s in S', noiseSum m n s ∂P ≤ ∫ s, |noiseSum m n s| ∂P :=
      (setIntegral_mono (hM.integrable one_le_two).restrict (hM.integrable one_le_two).abs.restrict
        fun s => le_abs_self _).trans
        (setIntegral_le_integral (hM.integrable one_le_two).abs (ae_of_all _ fun s => abs_nonneg _))
    have h2 : ∫ s in S', ∑ t ∈ range n, m t s ^ 2 / 2 ∂P ≤ ∫ s, ∑ t ∈ range n, m t s ^ 2 / 2 ∂P :=
      setIntegral_le_integral hQ (ae_of_all _ fun s =>
        Finset.sum_nonneg fun t _ => div_nonneg (sq_nonneg _) zero_le_two)
    linarith
  -- assemble
  rw [measure_eq_shift π0 μ hm hmr n hS]
  refine le_trans ?_ (lintegral_exp_neg_ge P hqpos hL)
  refine ENNReal.ofReal_le_ofReal ?_
  have hX : 0 ≤ β + Real.sqrt (2 * β) := by
    have h0 : 0 ≤ ∑ t ∈ range n, ∫ s, m t s ^ 2 ∂P :=
      Finset.sum_nonneg fun t _ => integral_nonneg fun s => sq_nonneg _
    have := Real.sqrt_nonneg (2 * β)
    linarith
  calc q0 * Real.exp (-(β + Real.sqrt (2 * β)) / q0)
      ≤ q * Real.exp (-(β + Real.sqrt (2 * β)) / q) := by
        refine mul_le_mul hq (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le hqpos.le
        rw [neg_div, neg_div, neg_le_neg_iff]
        exact div_le_div_of_nonneg_left hX hq0 hq
    _ ≤ q * Real.exp (-(∫ s in S', logLik m n s ∂P) / q) := by
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hqpos.le
        rw [neg_div, neg_div, neg_le_neg_iff]
        exact div_le_div_of_nonneg_right hLS hqpos.le

/-! ## The budget under a null world that does not read the tip -/

/-- The stopped sum of nonnegative prices: `Σ_{t < n} 1{G_t ≤ B} g_t ≤ B`, `G_t = Σ_{u ≤ t} g_u`. -/
theorem stopped_sum_le {g : ℕ → ℝ} (hg : ∀ t, 0 ≤ g t) {B : ℝ} (hB : 0 ≤ B) (n : ℕ) :
    ∑ t ∈ range n, (if ∑ u ∈ range (t + 1), g u ≤ B then g t else 0) ≤ B := by
  suffices h : ∀ n, ∑ t ∈ range n, (if ∑ u ∈ range (t + 1), g u ≤ B then g t else 0) ≤ B ∧
      ∑ t ∈ range n, (if ∑ u ∈ range (t + 1), g u ≤ B then g t else 0) ≤ ∑ u ∈ range n, g u from (h n).1
  intro n
  induction n with
  | zero => simp [hB]
  | succ n ih =>
    rw [Finset.sum_range_succ]
    split_ifs with h
    · rw [Finset.sum_range_succ] at h
      exact ⟨by linarith [ih.2], by rw [Finset.sum_range_succ]; linarith [ih.2]⟩
    · push Not at h
      refine ⟨by linarith [ih.1], ?_⟩
      rw [Finset.sum_range_succ]
      linarith [ih.2, hg n]

variable {d : ℕ} {Ω : Type} [MeasurableSpace Ω]

/-- **The budget.** If the shift of round `t` is `1{G_t ≤ B} h_t(θ, Z, ω)`, where the prices `g_u` and the stopping
read the noise and the seed only (the null world does not read the tip) and `∫ h_t(θ, ·)^2 dπ0(θ) = 2 g_t`, then
`Σ_{t < n} E m_t^2 ≤ 2B`. -/
theorem budget_le (π0 : Measure (E d)) [IsProbabilityMeasure π0] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {m : ℕ → Sample d Ω → ℝ} {g : ℕ → (ℕ → ℝ) × Ω → ℝ} {h : ℕ → Sample d Ω → ℝ} {B w : ℝ} (hB : 0 ≤ B)
    (hm : ∀ t s, m t s = if ∑ u ∈ range (t + 1), g u s.2 ≤ B then h t s else 0)
    (hmm : ∀ t, Measurable (m t)) (hmb : ∀ t s, |m t s| ≤ w) (hg0 : ∀ t y, 0 ≤ g t y)
    (hgm : ∀ t, Measurable (g t))
    (hh : ∀ t y, ∫ θ, h t (θ, y) ^ 2 ∂π0 = 2 * g t y) (n : ℕ) :
    ∑ t ∈ range n, ∫ s, m t s ^ 2 ∂gameLaw π0 μ ≤ 2 * B := by
  have hsqi : ∀ t, Integrable (fun s => m t s ^ 2) (gameLaw π0 μ) := fun t =>
    have := isProbabilityMeasure_gameLaw π0 μ
    Integrable.of_bound ((hmm t).pow_const 2).aestronglyMeasurable (w ^ 2) (ae_of_all _ fun s => by
      rw [Real.norm_eq_abs, abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (hmb t s) 2)
  have hinner : ∀ t y, ∫ θ, m t (θ, y) ^ 2 ∂π0 =
      2 * (if ∑ u ∈ range (t + 1), g u y ≤ B then g t y else 0) := fun t y => by
    simp only [hm]
    split_ifs
    · exact hh t y
    · simp
  have hstep : ∀ t, ∫ s, m t s ^ 2 ∂gameLaw π0 μ =
      ∫ y, 2 * (if ∑ u ∈ range (t + 1), g u y ≤ B then g t y else 0) ∂(RealRAM.gaussStream.prod μ) := fun t => by
    unfold gameLaw
    rw [integral_prod_symm _ (hsqi t)]
    simp only [hinner]
  simp only [hstep]
  have hgs : ∀ t, Measurable (fun y => 2 * (if ∑ u ∈ range (t + 1), g u y ≤ B then g t y else 0)) := fun t =>
    measurable_const.mul (Measurable.ite (measurableSet_le (Finset.measurable_sum _ fun u _ => hgm u)
      measurable_const) (hgm t) measurable_const)
  have hgi : ∀ t, Integrable (fun y => 2 * (if ∑ u ∈ range (t + 1), g u y ≤ B then g t y else 0))
      (RealRAM.gaussStream.prod μ) := fun t =>
    Integrable.of_bound (hgs t).aestronglyMeasurable (2 * B) (ae_of_all _ fun y => by
      rw [Real.norm_eq_abs]
      split_ifs with hc
      · have h1 : g t y ≤ B := by
          have := Finset.single_le_sum (f := fun u => g u y) (fun u _ => hg0 u y)
            (Finset.self_mem_range_succ t)
          exact this.trans hc
        rw [abs_of_nonneg (by linarith [hg0 t y])]
        linarith
      · simp [hB])
  rw [← integral_finsetSum _ fun t _ => hgi t]
  calc ∫ y, ∑ t ∈ range n, 2 * (if ∑ u ∈ range (t + 1), g u y ≤ B then g t y else 0) ∂(RealRAM.gaussStream.prod μ)
      ≤ ∫ _y, 2 * B ∂(RealRAM.gaussStream.prod μ) := by
        refine integral_mono (integrable_finsetSum _ fun t _ => hgi t) (integrable_const _) fun y => ?_
        simp only
        rw [← Finset.mul_sum]
        linarith [stopped_sum_le (fun t => hg0 t y) hB n]
    _ = 2 * B := by simp

end AdversarialBco.Grow
