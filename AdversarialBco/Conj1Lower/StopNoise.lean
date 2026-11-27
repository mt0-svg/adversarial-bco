/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Conj1Lower.Bayes

@[expose] public section

/-!
# The Gaussian stream along one coordinate, and predictable noise sums

The facts on the noise that Proposition STOP and Corollary LU-P use (the paper's bound with probability), on the
law of the sample `gameLaw π0 μ = π0 ⊗ gaussStream ⊗ μ` of Bayes.lean.

* `map_resetZ_noise`: the noise `Z_t` of round `t` is a standard Gaussian independent of the sample with `Z_t` reset to
  `0` (from `lintegral_gameLaw_coord`); `integral_gameLaw_noise`, its Bochner form for a function that reads `Z_t` only
  through its first argument.
* `integral_mul_noise`, `integral_mul_noise_sq`: `E[G Z_t] = 0` and `E[G Z_t²] = E[G]` for `G` that does not read
  `Z_t`.
* `noiseSum_sq_le`, `integral_noiseSum`: a noise sum with predictable weights in `[0, 1]`,
  `M_n = Σ_{t < n} V_t Z_t` with `V_t` reading the tip, the seed and `Z_0, ..., Z_{t-1}` only, has mean `0` and
  `E M_n² ≤ n`.
-/

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

namespace AdversarialBco.Lower.Stop

open Bayes

variable {d : ℕ} {Ω : Type} [MeasurableSpace Ω]

/-- The sample with the noise of round `t` set to `0`. -/
def resetZ (t : ℕ) (s : Sample d Ω) : Sample d Ω := (s.1, Function.update s.2.1 t 0, s.2.2)

theorem measurable_resetZ (t : ℕ) : Measurable (resetZ (d := d) (Ω := Ω) t) :=
  measurable_fst.prodMk (((measurable_update' (a := t)).comp
    ((measurable_fst.comp measurable_snd).prodMk measurable_const)).prodMk (measurable_snd.comp measurable_snd))

theorem measurable_noise (t : ℕ) : Measurable (fun s : Sample d Ω => s.2.1 t) :=
  (measurable_pi_apply t).comp (measurable_fst.comp measurable_snd)

omit [MeasurableSpace Ω] in
theorem resetZ_update (t : ℕ) (θ : E d) (Z : ℕ → ℝ) (b : ℝ) (ω : Ω) :
    resetZ t (θ, Function.update Z t b, ω) = resetZ t (θ, Z, ω) := by
  simp [resetZ, Function.update_idem]

/-- A function of the sample reads the noise only before round `t`. -/
def ReadsBefore (t : ℕ) (G : Sample d Ω → ℝ) : Prop :=
  ∀ s s' : Sample d Ω, s.1 = s'.1 → s.2.2 = s'.2.2 → (∀ i < t, s.2.1 i = s'.2.1 i) → G s = G s'

omit [MeasurableSpace Ω] in
theorem ReadsBefore.resetZ {t u : ℕ} {G : Sample d Ω → ℝ} (hG : ReadsBefore t G) (hu : t ≤ u) (s : Sample d Ω) :
    G (resetZ u s) = G s :=
  hG _ _ rfl rfl fun i hi => by simp [Stop.resetZ, Function.update_of_ne (by omega : i ≠ u)]

omit [MeasurableSpace Ω] in
theorem ReadsBefore.mul {t : ℕ} {G H : Sample d Ω → ℝ} (hG : ReadsBefore t G) (hH : ReadsBefore t H) :
    ReadsBefore t (fun s => G s * H s) :=
  fun s s' h1 h2 h3 => by
    show G s * H s = G s' * H s'
    rw [hG s s' h1 h2 h3, hH s s' h1 h2 h3]

/-- The noise of round `t` is a standard Gaussian independent of the sample with that noise reset. -/
theorem map_resetZ_noise (π0 : Measure (E d)) [IsProbabilityMeasure π0] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (t : ℕ) :
    (gameLaw π0 μ).map (fun s => (resetZ t s, s.2.1 t)) =
      ((gameLaw π0 μ).map (resetZ t)).prod (gaussianReal 0 1) := by
  have hG := isProbabilityMeasure_gameLaw π0 μ
  have hr := measurable_resetZ (d := d) (Ω := Ω) t
  have hz := measurable_noise (d := d) (Ω := Ω) t
  have hΨ : Measurable (fun s : Sample d Ω => (resetZ t s, s.2.1 t)) := hr.prodMk hz
  refine (Measure.prod_eq fun A B hA hB => ?_).symm
  rw [Measure.map_apply hΨ (hA.prod hB), Measure.map_apply hr hA, Set.mk_preimage_prod]
  have hA' : MeasurableSet (resetZ t ⁻¹' A) := hr hA
  have hF : Measurable (fun p : ℝ × Sample d Ω =>
      (resetZ t ⁻¹' A).indicator (1 : Sample d Ω → ℝ≥0∞) p.2 * B.indicator (1 : ℝ → ℝ≥0∞) p.1) :=
    ((measurable_one.indicator hA').comp measurable_snd).mul ((measurable_one.indicator hB).comp measurable_fst)
  have key := lintegral_gameLaw_coord π0 μ t hF (fun a θ Z b ω => by
    have h : ((θ, Function.update Z t b, ω) : Sample d Ω) ∈ resetZ t ⁻¹' A ↔ (θ, Z, ω) ∈ resetZ t ⁻¹' A := by
      simp only [Set.mem_preimage, resetZ_update]
    show (resetZ t ⁻¹' A).indicator (1 : Sample d Ω → ℝ≥0∞) (θ, Function.update Z t b, ω) * B.indicator 1 a =
      (resetZ t ⁻¹' A).indicator (1 : Sample d Ω → ℝ≥0∞) (θ, Z, ω) * B.indicator 1 a
    by_cases hm : ((θ, Z, ω) : Sample d Ω) ∈ resetZ t ⁻¹' A
    · rw [Set.indicator_of_mem (h.2 hm), Set.indicator_of_mem hm]
      rfl
    · rw [Set.indicator_of_notMem (mt h.1 hm), Set.indicator_of_notMem hm])
  have e1 : gameLaw π0 μ (resetZ t ⁻¹' A ∩ (fun s : Sample d Ω => s.2.1 t) ⁻¹' B) =
      ∫⁻ s, (resetZ t ⁻¹' A).indicator (1 : Sample d Ω → ℝ≥0∞) s * B.indicator (1 : ℝ → ℝ≥0∞) (s.2.1 t)
        ∂gameLaw π0 μ := by
    rw [← lintegral_indicator_one (hA'.inter (hz hB)), Set.inter_indicator_one]
    rfl
  rw [e1, key]
  have e2 : ∀ s : Sample d Ω, ∫⁻ z, (resetZ t ⁻¹' A).indicator (1 : Sample d Ω → ℝ≥0∞) s *
      B.indicator (1 : ℝ → ℝ≥0∞) z ∂gaussianReal 0 1 =
      (resetZ t ⁻¹' A).indicator (1 : Sample d Ω → ℝ≥0∞) s * gaussianReal 0 1 B := fun s => by
    rw [lintegral_const_mul _ (measurable_one.indicator hB), lintegral_indicator_one hB]
  simp only [e2]
  rw [lintegral_mul_const _ (measurable_one.indicator hA'), lintegral_indicator_one hA']

/-- The law of the noise of round `t` under the law of the sample. -/
theorem map_noise (π0 : Measure (E d)) [IsProbabilityMeasure π0] (μ : Measure Ω) [IsProbabilityMeasure μ] (t : ℕ) :
    (gameLaw π0 μ).map (fun s => s.2.1 t) = gaussianReal 0 1 := by
  have hr := measurable_resetZ (d := d) (Ω := Ω) t
  have hz := measurable_noise (d := d) (Ω := Ω) t
  have hΨ : Measurable (fun s : Sample d Ω => (resetZ t s, s.2.1 t)) := hr.prodMk hz
  have hG := isProbabilityMeasure_gameLaw π0 μ
  have h := congrArg (Measure.map Prod.snd) (map_resetZ_noise π0 μ t)
  rw [Measure.map_map measurable_snd hΨ, Measure.map_snd_prod, measure_univ, one_smul] at h
  exact h

theorem memLp_noise (π0 : Measure (E d)) [IsProbabilityMeasure π0] (μ : Measure Ω) [IsProbabilityMeasure μ] (t : ℕ) :
    MemLp (fun s : Sample d Ω => s.2.1 t) 2 (gameLaw π0 μ) := by
  have h := (memLp_map_measure_iff (g := id) (p := 2) measurable_id.aestronglyMeasurable
    (measurable_noise (d := d) (Ω := Ω) t).aemeasurable).1 (by rw [map_noise π0 μ t]; exact memLp_id_gaussianReal 2)
  exact h

theorem integrable_noise_sq (π0 : Measure (E d)) [IsProbabilityMeasure π0] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (t : ℕ) : Integrable (fun s : Sample d Ω => s.2.1 t ^ 2) (gameLaw π0 μ) :=
  (memLp_noise π0 μ t).integrable_sq

/-- The Bochner form of `lintegral_gameLaw_coord`: for `F` that reads the noise of round `t` only through its first
argument, `E F(Z_t, s) = E ∫ F(z, s) dN(0, 1)(z)`. -/
theorem integral_gameLaw_noise (π0 : Measure (E d)) [IsProbabilityMeasure π0] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (t : ℕ) {F : ℝ × Sample d Ω → ℝ} (hF : Measurable F)
    (hinv : ∀ a s, F (a, resetZ t s) = F (a, s)) (hint : Integrable (fun s => F (s.2.1 t, s)) (gameLaw π0 μ)) :
    ∫ s, F (s.2.1 t, s) ∂gameLaw π0 μ = ∫ s, ∫ z, F (z, s) ∂gaussianReal 0 1 ∂gameLaw π0 μ := by
  have hr := measurable_resetZ (d := d) (Ω := Ω) t
  have hG := isProbabilityMeasure_gameLaw π0 μ
  have hz := measurable_noise (d := d) (Ω := Ω) t
  have hΨ : Measurable (fun s : Sample d Ω => (resetZ t s, s.2.1 t)) := hr.prodMk hz
  have hFs : Measurable (fun p : Sample d Ω × ℝ => F (p.2, p.1)) := hF.comp measurable_swap
  have h1 : ∫ s, F (s.2.1 t, s) ∂gameLaw π0 μ =
      ∫ p, F (p.2, p.1) ∂(gameLaw π0 μ).map (fun s => (resetZ t s, s.2.1 t)) := by
    rw [integral_map hΨ.aemeasurable hFs.aestronglyMeasurable]
    simp only [hinv]
  have hint' : Integrable (fun p : Sample d Ω × ℝ => F (p.2, p.1))
      (((gameLaw π0 μ).map (resetZ t)).prod (gaussianReal 0 1)) := by
    rw [← map_resetZ_noise]
    refine (integrable_map_measure hFs.aestronglyMeasurable hΨ.aemeasurable).2 ?_
    simpa only [Function.comp_def, hinv] using hint
  have hI : StronglyMeasurable (fun s : Sample d Ω => ∫ z, F (z, s) ∂gaussianReal 0 1) :=
    StronglyMeasurable.integral_prod_left (f := fun z s => F (z, s)) hF.stronglyMeasurable
  rw [h1, map_resetZ_noise, integral_prod _ hint', integral_map hr.aemeasurable hI.aestronglyMeasurable]
  simp only [hinv]

/-- `E[G Z_t] = 0` for `G` that does not read `Z_t`. -/
theorem integral_mul_noise (π0 : Measure (E d)) [IsProbabilityMeasure π0] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (t : ℕ) {G : Sample d Ω → ℝ} (hG : Measurable G) (hinv : ∀ s, G (resetZ t s) = G s)
    (hint : Integrable (fun s => G s * s.2.1 t) (gameLaw π0 μ)) :
    ∫ s, G s * s.2.1 t ∂gameLaw π0 μ = 0 := by
  have h := integral_gameLaw_noise π0 μ t (F := fun p => G p.2 * p.1)
    ((hG.comp measurable_snd).mul measurable_fst) (fun a s => by simp only [hinv]) hint
  dsimp only at h
  rw [h]
  have h0 : ∀ s, ∫ z, G s * z ∂gaussianReal 0 1 = 0 := fun s => by
    rw [integral_const_mul (G s) (fun z => z), integral_id_gaussianReal, mul_zero]
  simp [h0]

/-- `∫ z² dN(0, 1) = 1`. -/
theorem integral_sq_gaussianReal : ∫ x, x ^ 2 ∂gaussianReal 0 1 = 1 := by
  have := variance_fun_id_gaussianReal (μ := 0) (v := 1)
  rw [variance_of_integral_eq_zero] at this
  · simpa using this
  · exact (memLp_id_gaussianReal 2).aemeasurable
  · simp

/-- `E[G Z_t²] = E[G]` for `G` that does not read `Z_t`. -/
theorem integral_mul_noise_sq (π0 : Measure (E d)) [IsProbabilityMeasure π0] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (t : ℕ) {G : Sample d Ω → ℝ} (hG : Measurable G) (hinv : ∀ s, G (resetZ t s) = G s)
    (hint : Integrable (fun s => G s * s.2.1 t ^ 2) (gameLaw π0 μ)) :
    ∫ s, G s * s.2.1 t ^ 2 ∂gameLaw π0 μ = ∫ s, G s ∂gameLaw π0 μ := by
  have h := integral_gameLaw_noise π0 μ t (F := fun p => G p.2 * p.1 ^ 2)
    ((hG.comp measurable_snd).mul (measurable_fst.pow_const 2)) (fun a s => by simp only [hinv]) hint
  dsimp only at h
  rw [h]
  have h0 : ∀ s, ∫ z, G s * z ^ 2 ∂gaussianReal 0 1 = G s := fun s => by
    rw [integral_const_mul (G s) (fun z => z ^ 2), integral_sq_gaussianReal, mul_one]
  simp [h0]

/-- `E Z_t² = 1`. -/
theorem integral_noise_sq (π0 : Measure (E d)) [IsProbabilityMeasure π0] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (t : ℕ) : ∫ s, s.2.1 t ^ 2 ∂gameLaw π0 μ = 1 := by
  have hG := isProbabilityMeasure_gameLaw π0 μ
  have h := integral_mul_noise_sq π0 μ t (G := fun _ => (1 : ℝ)) measurable_const (fun _ => rfl)
    (by simpa using integrable_noise_sq π0 μ t)
  simpa using h

/-- The noise sum with weights `V`: `M_n = Σ_{t < n} V_t Z_t`. -/
noncomputable def noiseSum (V : ℕ → Sample d Ω → ℝ) (n : ℕ) (s : Sample d Ω) : ℝ :=
  ∑ t ∈ range n, V t s * s.2.1 t

omit [MeasurableSpace Ω] in
theorem noiseSum_readsBefore {V : ℕ → Sample d Ω → ℝ} {n : ℕ} (hVr : ∀ t < n, ReadsBefore t (V t)) :
    ReadsBefore n (noiseSum V n) := fun s s' h1 h2 h3 => by
  unfold noiseSum
  refine Finset.sum_congr rfl fun t ht => ?_
  have ht' := Finset.mem_range.1 ht
  rw [hVr t ht' s s' h1 h2 fun i hi => h3 i (by omega), h3 t ht']

theorem measurable_noiseSum {V : ℕ → Sample d Ω → ℝ} {n : ℕ} (hVm : ∀ t < n, Measurable (V t)) :
    Measurable (noiseSum V n) :=
  Finset.measurable_sum _ fun t ht => (hVm t (Finset.mem_range.1 ht)).mul (measurable_noise t)

theorem memLp_weight_noise (π0 : Measure (E d)) [IsProbabilityMeasure π0] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {V : Sample d Ω → ℝ} (hVm : Measurable V) (hV : ∀ s, |V s| ≤ 1) (t : ℕ) :
    MemLp (fun s => V s * s.2.1 t) 2 (gameLaw π0 μ) :=
  (memLp_noise π0 μ t).of_le (hVm.mul (measurable_noise t)).aestronglyMeasurable (ae_of_all _ fun s => by
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
    exact mul_le_of_le_one_left (abs_nonneg _) (hV s))

theorem memLp_noiseSum (π0 : Measure (E d)) [IsProbabilityMeasure π0] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {V : ℕ → Sample d Ω → ℝ} {n : ℕ} (hVm : ∀ t < n, Measurable (V t)) (hV : ∀ t < n, ∀ s, |V t s| ≤ 1) :
    MemLp (noiseSum V n) 2 (gameLaw π0 μ) :=
  memLp_finsetSum _ fun t ht =>
    memLp_weight_noise π0 μ (hVm t (Finset.mem_range.1 ht)) (hV t (Finset.mem_range.1 ht)) t

/-- A noise sum with predictable weights has mean `0`. -/
theorem integral_noiseSum (π0 : Measure (E d)) [IsProbabilityMeasure π0] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {V : ℕ → Sample d Ω → ℝ} {n : ℕ} (hVm : ∀ t < n, Measurable (V t)) (hV : ∀ t < n, ∀ s, |V t s| ≤ 1)
    (hVr : ∀ t < n, ReadsBefore t (V t)) : ∫ s, noiseSum V n s ∂gameLaw π0 μ = 0 := by
  have hG := isProbabilityMeasure_gameLaw π0 μ
  unfold noiseSum
  rw [integral_finsetSum _ fun t ht => (memLp_weight_noise π0 μ (hVm t (Finset.mem_range.1 ht))
    (hV t (Finset.mem_range.1 ht)) t).integrable one_le_two]
  exact Finset.sum_eq_zero fun t ht => integral_mul_noise π0 μ t (hVm t (Finset.mem_range.1 ht))
    ((hVr t (Finset.mem_range.1 ht)).resetZ le_rfl)
    ((memLp_weight_noise π0 μ (hVm t (Finset.mem_range.1 ht)) (hV t (Finset.mem_range.1 ht)) t).integrable one_le_two)

/-- A noise sum with predictable weights in `[-1, 1]` has `E M_n² ≤ n`. -/
theorem noiseSum_sq_le (π0 : Measure (E d)) [IsProbabilityMeasure π0] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {V : ℕ → Sample d Ω → ℝ} {n : ℕ} (hVm : ∀ t < n, Measurable (V t)) (hV : ∀ t < n, ∀ s, |V t s| ≤ 1)
    (hVr : ∀ t < n, ReadsBefore t (V t)) : ∫ s, noiseSum V n s ^ 2 ∂gameLaw π0 μ ≤ n := by
  have hG := isProbabilityMeasure_gameLaw π0 μ
  induction n with
  | zero => simp [noiseSum]
  | succ n ih =>
    have hVm' : ∀ t < n, Measurable (V t) := fun t ht => hVm t (by omega)
    have hV' : ∀ t < n, ∀ s, |V t s| ≤ 1 := fun t ht => hV t (by omega)
    have hVr' : ∀ t < n, ReadsBefore t (V t) := fun t ht => hVr t (by omega)
    have ih' := ih hVm' hV' hVr'
    have hVn := hVm n (by omega)
    have hVb := hV n (by omega)
    have hVrn := hVr n (by omega)
    have hM := memLp_noiseSum π0 μ hVm' hV'
    have hVZ := memLp_weight_noise π0 μ hVn hVb n
    have hMV : MemLp (fun s => noiseSum V n s * V n s) 2 (gameLaw π0 μ) :=
      hM.of_le ((measurable_noiseSum hVm').mul hVn).aestronglyMeasurable (ae_of_all _ fun s => by
        rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _) (hVb s))
    have hcross : Integrable (fun s => noiseSum V n s * V n s * s.2.1 n) (gameLaw π0 μ) :=
      hMV.integrable_mul (memLp_noise π0 μ n)
    have hsq : Integrable (fun s => V n s ^ 2 * s.2.1 n ^ 2) (gameLaw π0 μ) := by
      have := hVZ.integrable_sq
      refine this.congr (ae_of_all _ fun s => ?_)
      ring
    have hV2 : ∀ s, V n s ^ 2 ≤ 1 := fun s => by
      have := hVb s
      rw [← sq_abs]
      nlinarith [abs_nonneg (V n s)]
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
      integral_mul_noise π0 μ n ((measurable_noiseSum hVm').mul hVn)
        (((noiseSum_readsBefore hVr').mul hVrn).resetZ le_rfl) hcross
    have h1 : ∫ s, V n s ^ 2 * s.2.1 n ^ 2 ∂gameLaw π0 μ = ∫ s, V n s ^ 2 ∂gameLaw π0 μ :=
      integral_mul_noise_sq π0 μ n (hVn.pow_const 2) (fun s => by rw [hVrn.resetZ le_rfl s]) hsq
    have h2 : ∫ s, V n s ^ 2 ∂gameLaw π0 μ ≤ 1 := by
      have := integral_mono_of_nonneg (μ := gameLaw π0 μ) (f := fun s => V n s ^ 2) (g := fun _ => (1 : ℝ))
        (ae_of_all _ fun s => sq_nonneg _) (integrable_const 1) (ae_of_all _ hV2)
      simpa using this
    rw [h0, h1]
    push_cast
    linarith

end AdversarialBco.Lower.Stop
