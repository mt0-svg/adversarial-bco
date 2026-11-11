/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import Mathlib

@[expose] public section

/-!
# One round of the Bayes core

Lemma 9.5 for one round. A law `π` on the tips `Θ`; the genie's answer `c θ` in a
finite set `α`; an observation `y` of law `N(s θ, v)`. The posterior given `(a, y)` is `π` reweighted by the likelihood
`lik c s v a y θ = 1[c θ = a] gaussianPDF (s θ) v y` and normalised, and `π` itself where the normaliser vanishes
(`bayesUpd`, the null-normaliser convention).

* `bayes_step`: the joint law of the tip and of `(c θ, y)` disintegrates along the posterior: for every measurable
  `G ≥ 0`, `∫ π(dθ) ∫ N(s θ, v)(dy) G(θ, c θ, y) = ∫ π(dθ) ∫ N(s θ, v)(dy) ∫ post(c θ, y)(dθ') G(θ', c θ, y)`.
* `post_round`: the same in a game with a learner, on the explicit product `π ⊗ N(0, 1) ⊗ μ` (tip, noise, seed): the
  play is `x = pol ω`, the answer `c x θ`, the observation `s x θ + sc z`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace AdversarialBco.Lower.Bayes

section Round

variable {Θ α : Type*} [MeasurableSpace Θ] [MeasurableSpace α]

/-- Bayes update of `π` by the likelihood `L`: `(∫ L dπ)⁻¹ L π`, and `π` itself where the normaliser `∫ L dπ` is `0`
or `∞`. -/
noncomputable def bayesUpd (π : Measure Θ) (L : Θ → ℝ≥0∞) : Measure Θ :=
  if ∫⁻ θ, L θ ∂π = 0 ∨ ∫⁻ θ, L θ ∂π = ∞ then π else (∫⁻ θ, L θ ∂π)⁻¹ • π.withDensity L

/-- The likelihood of the answer `a` and of the observation `y` at the tip `θ`: `1[c θ = a] N(s θ, v)(y)`. -/
noncomputable def lik (c : Θ → α) (s : Θ → ℝ) (v : ℝ≥0) (a : α) (y : ℝ) (θ : Θ) : ℝ≥0∞ :=
  (c ⁻¹' {a}).indicator (fun θ => gaussianPDF (s θ) v y) θ

theorem lintegral_bayesUpd (π : Measure Θ) {L f : Θ → ℝ≥0∞} (hL : Measurable L) (hf : Measurable f) :
    ∫⁻ θ, f θ ∂bayesUpd π L =
      if ∫⁻ θ, L θ ∂π = 0 ∨ ∫⁻ θ, L θ ∂π = ∞ then ∫⁻ θ, f θ ∂π
      else (∫⁻ θ, L θ ∂π)⁻¹ * ∫⁻ θ, L θ * f θ ∂π := by
  unfold bayesUpd
  split_ifs with h
  · rfl
  · rw [lintegral_smul_measure, lintegral_withDensity_eq_lintegral_mul _ hL hf]
    rfl

/-- With a finite normaliser, the normaliser times the posterior integral is the integral against the likelihood. -/
theorem normz_mul_lintegral_bayesUpd (π : Measure Θ) {L f : Θ → ℝ≥0∞} (hL : Measurable L) (hf : Measurable f)
    (hfin : ∫⁻ θ, L θ ∂π ≠ ∞) :
    (∫⁻ θ, L θ ∂π) * ∫⁻ θ, f θ ∂bayesUpd π L = ∫⁻ θ, L θ * f θ ∂π := by
  by_cases h0 : ∫⁻ θ, L θ ∂π = 0
  · have hL0 : L =ᵐ[π] 0 := (lintegral_eq_zero_iff hL).1 h0
    rw [h0, zero_mul]
    symm
    calc ∫⁻ θ, L θ * f θ ∂π = ∫⁻ _, 0 ∂π :=
          lintegral_congr_ae (by filter_upwards [hL0] with θ hθ; simp [hθ])
      _ = 0 := lintegral_zero
  · rw [lintegral_bayesUpd π hL hf]
    split_ifs with h
    · exact absurd h (by tauto)
    · rw [← mul_assoc, ENNReal.mul_inv_cancel h0 hfin, one_mul]

theorem gaussianPDF_le (m : ℝ) (v : ℝ≥0) (y : ℝ) :
    gaussianPDF m v y ≤ ENNReal.ofReal (Real.sqrt (2 * Real.pi * v))⁻¹ := by
  unfold gaussianPDF
  apply ENNReal.ofReal_le_ofReal
  rw [gaussianPDFReal]
  have h1 : Real.exp (-(y - m) ^ 2 / (2 * v)) ≤ 1 := by
    apply Real.exp_le_one_iff.2
    apply div_nonpos_of_nonpos_of_nonneg
    · exact neg_nonpos.2 (sq_nonneg _)
    · positivity
  have h2 : 0 ≤ (Real.sqrt (2 * Real.pi * v))⁻¹ := by positivity
  calc _ ≤ (Real.sqrt (2 * Real.pi * v))⁻¹ * 1 := mul_le_mul_of_nonneg_left h1 h2
    _ = _ := mul_one _

omit [MeasurableSpace Θ] [MeasurableSpace α] in
theorem lik_le (c : Θ → α) (s : Θ → ℝ) (v : ℝ≥0) (a : α) (y : ℝ) (θ : Θ) :
    lik c s v a y θ ≤ ENNReal.ofReal (Real.sqrt (2 * Real.pi * v))⁻¹ := by
  unfold lik
  by_cases h : θ ∈ c ⁻¹' {a}
  · rw [Set.indicator_of_mem h]; exact gaussianPDF_le _ _ _
  · rw [Set.indicator_of_notMem h]; exact bot_le

omit [MeasurableSpace α] in
theorem lintegral_lik_ne_top (π : Measure Θ) [IsFiniteMeasure π] (c : Θ → α) (s : Θ → ℝ) (v : ℝ≥0) (a : α)
    (y : ℝ) : ∫⁻ θ, lik c s v a y θ ∂π ≠ ∞ := by
  apply ne_top_of_le_ne_top (b := ∫⁻ _, ENNReal.ofReal (Real.sqrt (2 * Real.pi * v))⁻¹ ∂π)
  · rw [lintegral_const]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
  · exact lintegral_mono fun θ => lik_le c s v a y θ

theorem measurable_lik [Countable α] [MeasurableSingletonClass α] {c : Θ → α} {s : Θ → ℝ} (hc : Measurable c)
    (hs : Measurable s) (v : ℝ≥0) :
    Measurable (fun p : (α × ℝ) × Θ => lik c s v p.1.1 p.1.2 p.2) := by
  have hset : MeasurableSet {p : (α × ℝ) × Θ | c p.2 = p.1.1} :=
    measurableSet_eq_fun (hc.comp measurable_snd) (measurable_fst.comp measurable_fst)
  have heq : (fun p : (α × ℝ) × Θ => lik c s v p.1.1 p.1.2 p.2) =
      {p : (α × ℝ) × Θ | c p.2 = p.1.1}.indicator (fun p => gaussianPDF (s p.2) v p.1.2) := by
    ext p
    by_cases h : c p.2 = p.1.1
    · rw [lik, Set.indicator_of_mem (show p.2 ∈ c ⁻¹' {p.1.1} from h),
        Set.indicator_of_mem (show p ∈ {p : (α × ℝ) × Θ | c p.2 = p.1.1} from h)]
    · rw [lik, Set.indicator_of_notMem (show p.2 ∉ c ⁻¹' {p.1.1} from h),
        Set.indicator_of_notMem (show p ∉ {p : (α × ℝ) × Θ | c p.2 = p.1.1} from h)]
  rw [heq]
  refine Measurable.indicator ?_ hset
  exact measurable_uncurry_gaussianPDF.comp
    ((hs.comp measurable_snd).prodMk (measurable_const.prodMk (measurable_snd.comp measurable_fst)))

theorem lintegral_gaussianReal_eq (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ y, f y ∂gaussianReal m v = ∫⁻ y, gaussianPDF m v y * f y := by
  rw [gaussianReal_of_var_ne_zero m hv, lintegral_withDensity_eq_lintegral_mul _ (measurable_gaussianPDF m v) hf]
  rfl

omit [MeasurableSpace Θ] [MeasurableSpace α] in
theorem sum_lik_mul [Fintype α] (c : Θ → α) (s : Θ → ℝ) (v : ℝ≥0) (y : ℝ) (θ : Θ) (F : α → ℝ≥0∞) :
    ∑ a, lik c s v a y θ * F a = gaussianPDF (s θ) v y * F (c θ) := by
  classical
  simp only [lik, Set.indicator_apply, Set.mem_preimage, Set.mem_singleton_iff, ite_mul, zero_mul]
  rw [Finset.sum_ite_eq]
  simp

/-- The integral over the tip and the observation, with the answer read off the tip, as an integral over the
observation of a sum over the answers. -/
theorem lintegral_obs [Fintype α] [MeasurableSingletonClass α] (π : Measure Θ) [SFinite π] {c : Θ → α}
    {s : Θ → ℝ} (hc : Measurable c) (hs : Measurable s) {v : ℝ≥0} (hv : v ≠ 0) {F : Θ × α × ℝ → ℝ≥0∞}
    (hF : Measurable F) :
    ∫⁻ θ, ∫⁻ y, F (θ, c θ, y) ∂gaussianReal (s θ) v ∂π =
      ∫⁻ y, ∑ a, ∫⁻ θ, lik c s v a y θ * F (θ, a, y) ∂π := by
  have hlik := measurable_lik hc hs v
  have hterm : ∀ a : α, Measurable (fun q : Θ × ℝ => lik c s v a q.2 q.1 * F (q.1, a, q.2)) := fun a =>
    (hlik.comp ((measurable_const.prodMk measurable_snd).prodMk measurable_fst)).mul
      (hF.comp (measurable_fst.prodMk (measurable_const.prodMk measurable_snd)))
  calc ∫⁻ θ, ∫⁻ y, F (θ, c θ, y) ∂gaussianReal (s θ) v ∂π
      = ∫⁻ θ, (∫⁻ y, ∑ a, lik c s v a y θ * F (θ, a, y)) ∂π := by
        refine lintegral_congr fun θ => ?_
        rw [lintegral_gaussianReal_eq (f := fun y => F (θ, c θ, y)) _ hv
          (hF.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id)))]
        refine lintegral_congr fun y => ?_
        rw [sum_lik_mul c s v y θ (fun a => F (θ, a, y))]
    _ = ∫⁻ y, (∫⁻ θ, ∑ a, lik c s v a y θ * F (θ, a, y) ∂π) := by
        have hsum : Measurable (fun q : Θ × ℝ => ∑ a, lik c s v a q.2 q.1 * F (q.1, a, q.2)) :=
          Finset.measurable_sum _ fun a _ => hterm a
        exact lintegral_lintegral_swap (f := fun θ y => ∑ a, lik c s v a y θ * F (θ, a, y)) hsum.aemeasurable
    _ = ∫⁻ y, ∑ a, ∫⁻ θ, lik c s v a y θ * F (θ, a, y) ∂π := by
        refine lintegral_congr fun y => ?_
        refine lintegral_finsetSum _ fun a _ => ?_
        have h1 : Measurable (lik c s v a y) := hlik.comp (measurable_prodMk_left (x := (a, y)))
        have h2 : Measurable (fun θ => F (θ, a, y)) := hF.comp measurable_prodMk_right
        exact h1.mul h2

theorem measurable_lintegral_bayesUpd [Countable α] [MeasurableSingletonClass α] (π : Measure Θ) [SFinite π]
    {c : Θ → α} {s : Θ → ℝ} (hc : Measurable c) (hs : Measurable s) (v : ℝ≥0) {G : Θ × α × ℝ → ℝ≥0∞}
    (hG : Measurable G) :
    Measurable (fun p : α × ℝ => ∫⁻ θ', G (θ', p.1, p.2) ∂bayesUpd π (lik c s v p.1 p.2)) := by
  have hlik := measurable_lik hc hs v
  have hG' : Measurable (fun q : (α × ℝ) × Θ => G (q.2, q.1.1, q.1.2)) :=
    hG.comp (measurable_snd.prodMk ((measurable_fst.comp measurable_fst).prodMk
      (measurable_snd.comp measurable_fst)))
  have hN : Measurable (fun p : α × ℝ => ∫⁻ θ, lik c s v p.1 p.2 θ ∂π) := hlik.lintegral_prod_right'
  have heq : (fun p : α × ℝ => ∫⁻ θ', G (θ', p.1, p.2) ∂bayesUpd π (lik c s v p.1 p.2)) =
      fun p => if ∫⁻ θ, lik c s v p.1 p.2 θ ∂π = 0 ∨ ∫⁻ θ, lik c s v p.1 p.2 θ ∂π = ∞
        then ∫⁻ θ', G (θ', p.1, p.2) ∂π
        else (∫⁻ θ, lik c s v p.1 p.2 θ ∂π)⁻¹ * ∫⁻ θ', lik c s v p.1 p.2 θ' * G (θ', p.1, p.2) ∂π := by
    ext p
    exact lintegral_bayesUpd π (hlik.comp (measurable_const.prodMk measurable_id))
      (hG'.comp (measurable_const.prodMk measurable_id))
  rw [heq]
  refine Measurable.ite ?_ hG'.lintegral_prod_right' (hN.inv.mul (hlik.mul hG').lintegral_prod_right')
  exact (hN (measurableSet_singleton 0)).union (hN (measurableSet_singleton ∞))

/-- Lemma 9.5 for one round: the joint law of the tip and of `(c θ, y)` disintegrates along the posterior. -/
theorem bayes_step [Fintype α] [MeasurableSingletonClass α] (π : Measure Θ) [IsFiniteMeasure π]
    {c : Θ → α} {s : Θ → ℝ} (hc : Measurable c) (hs : Measurable s) {v : ℝ≥0} (hv : v ≠ 0)
    {G : Θ × α × ℝ → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ θ, ∫⁻ y, G (θ, c θ, y) ∂gaussianReal (s θ) v ∂π =
      ∫⁻ θ, ∫⁻ y, ∫⁻ θ', G (θ', c θ, y) ∂bayesUpd π (lik c s v (c θ) y) ∂gaussianReal (s θ) v ∂π := by
  have hlik := measurable_lik hc hs v
  have hΦ := measurable_lintegral_bayesUpd π hc hs v hG
  have hR := lintegral_obs π hc hs hv (F := fun q => ∫⁻ θ', G (θ', q.2.1, q.2.2) ∂bayesUpd π (lik c s v q.2.1 q.2.2))
    (hΦ.comp measurable_snd)
  rw [hR, lintegral_obs π hc hs hv hG]
  refine lintegral_congr fun y => Finset.sum_congr rfl fun a _ => ?_
  have hLm : Measurable (lik c s v a y) := hlik.comp (measurable_prodMk_left (x := (a, y)))
  have hGm : Measurable (fun θ => G (θ, a, y)) := hG.comp measurable_prodMk_right
  show ∫⁻ θ, lik c s v a y θ * G (θ, a, y) ∂π =
    ∫⁻ θ, lik c s v a y θ * (∫⁻ θ', G (θ', a, y) ∂bayesUpd π (lik c s v a y)) ∂π
  rw [lintegral_mul_const _ hLm, normz_mul_lintegral_bayesUpd π hLm hGm (lintegral_lik_ne_top π c s v a y)]

end Round

section Param

variable {Θ α P : Type*} [MeasurableSpace Θ] [MeasurableSpace α] [MeasurableSpace P]

/-- The likelihood is jointly measurable when the answer map, the signal, the answer and the observation depend
measurably on a parameter. -/
theorem measurable_lik_param [Countable α] [MeasurableSingletonClass α] {c : P → Θ → α} {s : P → Θ → ℝ}
    (hc : Measurable (fun q : P × Θ => c q.1 q.2)) (hs : Measurable (fun q : P × Θ => s q.1 q.2)) (v : ℝ≥0)
    {a : P → α} {y : P → ℝ} (ha : Measurable a) (hy : Measurable y) :
    Measurable (fun q : P × Θ => lik (c q.1) (s q.1) v (a q.1) (y q.1) q.2) := by
  have hset : MeasurableSet {q : P × Θ | c q.1 q.2 = a q.1} := measurableSet_eq_fun hc (ha.comp measurable_fst)
  have heq : (fun q : P × Θ => lik (c q.1) (s q.1) v (a q.1) (y q.1) q.2) =
      {q : P × Θ | c q.1 q.2 = a q.1}.indicator (fun q => gaussianPDF (s q.1 q.2) v (y q.1)) := by
    ext q
    by_cases h : c q.1 q.2 = a q.1
    · rw [lik, Set.indicator_of_mem (show q.2 ∈ c q.1 ⁻¹' {a q.1} from h),
        Set.indicator_of_mem (show q ∈ {q : P × Θ | c q.1 q.2 = a q.1} from h)]
    · rw [lik, Set.indicator_of_notMem (show q.2 ∉ c q.1 ⁻¹' {a q.1} from h),
        Set.indicator_of_notMem (show q ∉ {q : P × Θ | c q.1 q.2 = a q.1} from h)]
  rw [heq]
  exact Measurable.indicator (measurable_uncurry_gaussianPDF.comp
    (hs.prodMk (measurable_const.prodMk (hy.comp measurable_fst)))) hset

theorem measurable_lintegral_bayesUpd_param [Countable α] [MeasurableSingletonClass α] (π : Measure Θ)
    [SFinite π] {c : P → Θ → α} {s : P → Θ → ℝ} (hc : Measurable (fun q : P × Θ => c q.1 q.2))
    (hs : Measurable (fun q : P × Θ => s q.1 q.2)) (v : ℝ≥0) {a : P → α} {y : P → ℝ} (ha : Measurable a)
    (hy : Measurable y) {G : P × Θ → ℝ≥0∞} (hG : Measurable G) :
    Measurable (fun p => ∫⁻ θ', G (p, θ') ∂bayesUpd π (lik (c p) (s p) v (a p) (y p))) := by
  have hlik := measurable_lik_param hc hs v ha hy
  have hN : Measurable (fun p => ∫⁻ θ, lik (c p) (s p) v (a p) (y p) θ ∂π) := hlik.lintegral_prod_right'
  have heq : (fun p => ∫⁻ θ', G (p, θ') ∂bayesUpd π (lik (c p) (s p) v (a p) (y p))) =
      fun p => if ∫⁻ θ, lik (c p) (s p) v (a p) (y p) θ ∂π = 0 ∨
          ∫⁻ θ, lik (c p) (s p) v (a p) (y p) θ ∂π = ∞
        then ∫⁻ θ', G (p, θ') ∂π
        else (∫⁻ θ, lik (c p) (s p) v (a p) (y p) θ ∂π)⁻¹ *
          ∫⁻ θ', lik (c p) (s p) v (a p) (y p) θ' * G (p, θ') ∂π := by
    ext p
    exact lintegral_bayesUpd π (hlik.comp (measurable_prodMk_left (x := p)))
      (hG.comp (measurable_prodMk_left (x := p)))
  rw [heq]
  refine Measurable.ite ?_ hG.lintegral_prod_right' (hN.inv.mul (hlik.mul hG).lintegral_prod_right')
  exact (hN (measurableSet_singleton 0)).union (hN (measurableSet_singleton ∞))

end Param

section Game

/-- The variance `sc²` of the observation noise `sc Z`. -/
def noiseVar (sc : ℝ) : ℝ≥0 := ⟨sc ^ 2, sq_nonneg sc⟩

theorem noiseVar_ne_zero {sc : ℝ} (h : sc ≠ 0) : noiseVar sc ≠ 0 := by
  intro h0
  have h1 : sc ^ 2 = 0 := congrArg Subtype.val h0
  exact h (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h1)

theorem gaussianReal_map_affine (m sc : ℝ) :
    (gaussianReal 0 1).map (fun z => m + sc * z) = gaussianReal m (noiseVar sc) := by
  have h : (fun z : ℝ => m + sc * z) = (fun z => m + z) ∘ (fun z => sc * z) := rfl
  rw [h, ← Measure.map_map (by fun_prop) (by fun_prop), gaussianReal_map_const_mul,
    gaussianReal_map_const_add]
  congr 1
  · simp
  · ext
    simp only [mul_one]
    rfl

theorem lintegral_gauss_affine (m sc : ℝ) {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ z, f (m + sc * z) ∂gaussianReal 0 1 = ∫⁻ y, f y ∂gaussianReal m (noiseVar sc) := by
  rw [← gaussianReal_map_affine, lintegral_map hf (by fun_prop)]

/-- The integral over the explicit product `π ⊗ ν ⊗ μ` (tip, noise, seed) as the seed's integral outside. -/
theorem lintegral_prod3 {Θ Z Ω : Type*} [MeasurableSpace Θ] [MeasurableSpace Z] [MeasurableSpace Ω]
    (π : Measure Θ) [SFinite π] (ν : Measure Z) [SFinite ν] (μ : Measure Ω) [SFinite μ]
    {f : Θ × Z × Ω → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ p, f p ∂(π.prod (ν.prod μ)) = ∫⁻ ω, ∫⁻ θ, ∫⁻ z, f (θ, z, ω) ∂ν ∂π ∂μ := by
  rw [lintegral_prod _ hf.aemeasurable]
  have h1 : ∀ θ, ∫⁻ q, f (θ, q) ∂(ν.prod μ) = ∫⁻ ω, ∫⁻ z, f (θ, z, ω) ∂ν ∂μ := fun θ =>
    lintegral_prod_symm _ (hf.comp measurable_prodMk_left).aemeasurable
  rw [lintegral_congr h1]
  have hm : Measurable (fun q : Θ × Ω => ∫⁻ z, f (q.1, z, q.2) ∂ν) :=
    (hf.comp ((measurable_fst.comp measurable_fst).prodMk
      (measurable_snd.prodMk (measurable_snd.comp measurable_fst)))).lintegral_prod_right'
  exact lintegral_lintegral_swap (f := fun θ ω => ∫⁻ z, f (θ, z, ω) ∂ν) hm.aemeasurable

/-- Lemma 9.5 for one round of a game: tip `θ ~ π`, noise `z ~ N(0, 1)`, seed `ω ~ μ`; the learner plays
`x = pol ω`, the genie answers `c x θ`, the learner observes `s x θ + sc z`. Given the play, the answer and the
observation (and the seed), the tip has the law `bayesUpd π (lik ...)`. -/
theorem post_round {Θ α Ω X : Type*} [MeasurableSpace Θ] [MeasurableSpace α] [MeasurableSpace Ω]
    [MeasurableSpace X] [Fintype α] [MeasurableSingletonClass α] (π : Measure Θ) [IsFiniteMeasure π]
    (μ : Measure Ω) [SFinite μ] {pol : Ω → X} (hpol : Measurable pol) {c : X → Θ → α} {s : X → Θ → ℝ}
    (hc : Measurable (fun q : X × Θ => c q.1 q.2)) (hs : Measurable (fun q : X × Θ => s q.1 q.2))
    {sc : ℝ} (hsc : sc ≠ 0) {F : Θ × (X × α × ℝ) × Ω → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ p, F (p.1, (pol p.2.2, c (pol p.2.2) p.1, s (pol p.2.2) p.1 + sc * p.2.1), p.2.2)
        ∂(π.prod ((gaussianReal 0 1).prod μ)) =
      ∫⁻ p, ∫⁻ θ', F (θ', (pol p.2.2, c (pol p.2.2) p.1, s (pol p.2.2) p.1 + sc * p.2.1), p.2.2)
        ∂bayesUpd π (lik (c (pol p.2.2)) (s (pol p.2.2)) (noiseVar sc) (c (pol p.2.2) p.1)
          (s (pol p.2.2) p.1 + sc * p.2.1)) ∂(π.prod ((gaussianReal 0 1).prod μ)) := by
  have hpω : Measurable (fun p : Θ × ℝ × Ω => pol p.2.2) := hpol.comp (measurable_snd.comp measurable_snd)
  have hcp : Measurable (fun q : (Θ × ℝ × Ω) × Θ => c (pol q.1.2.2) q.2) :=
    hc.comp ((hpω.comp measurable_fst).prodMk measurable_snd)
  have hsp : Measurable (fun q : (Θ × ℝ × Ω) × Θ => s (pol q.1.2.2) q.2) :=
    hs.comp ((hpω.comp measurable_fst).prodMk measurable_snd)
  have ha : Measurable (fun p : Θ × ℝ × Ω => c (pol p.2.2) p.1) := hc.comp (hpω.prodMk measurable_fst)
  have hy : Measurable (fun p : Θ × ℝ × Ω => s (pol p.2.2) p.1 + sc * p.2.1) :=
    (hs.comp (hpω.prodMk measurable_fst)).add (measurable_const.mul (measurable_fst.comp measurable_snd))
  have hH : Measurable (fun p : Θ × ℝ × Ω =>
      (pol p.2.2, c (pol p.2.2) p.1, s (pol p.2.2) p.1 + sc * p.2.1)) := hpω.prodMk (ha.prodMk hy)
  have hL : Measurable (fun p : Θ × ℝ × Ω =>
      F (p.1, (pol p.2.2, c (pol p.2.2) p.1, s (pol p.2.2) p.1 + sc * p.2.1), p.2.2)) :=
    hF.comp (measurable_fst.prodMk (hH.prodMk (measurable_snd.comp measurable_snd)))
  have hR := measurable_lintegral_bayesUpd_param π (c := fun p : Θ × ℝ × Ω => c (pol p.2.2))
    (s := fun p : Θ × ℝ × Ω => s (pol p.2.2)) hcp hsp (noiseVar sc) ha hy
    (G := fun q => F (q.2, (pol q.1.2.2, c (pol q.1.2.2) q.1.1, s (pol q.1.2.2) q.1.1 + sc * q.1.2.1), q.1.2.2))
    (hF.comp (measurable_snd.prodMk ((hH.comp measurable_fst).prodMk
      (measurable_snd.comp (measurable_snd.comp measurable_fst)))))
  rw [lintegral_prod3 _ _ _ hL, lintegral_prod3 _ _ _ hR]
  refine lintegral_congr fun ω => ?_
  have hcx : Measurable (c (pol ω)) := hc.comp (measurable_prodMk_left (x := pol ω))
  have hsx : Measurable (s (pol ω)) := hs.comp (measurable_prodMk_left (x := pol ω))
  have hG : Measurable (fun q : Θ × α × ℝ => F (q.1, (pol ω, q.2.1, q.2.2), ω)) :=
    hF.comp (measurable_fst.prodMk ((measurable_const.prodMk measurable_snd).prodMk measurable_const))
  calc ∫⁻ θ, ∫⁻ z, F (θ, (pol ω, c (pol ω) θ, s (pol ω) θ + sc * z), ω) ∂gaussianReal 0 1 ∂π
      = ∫⁻ θ, ∫⁻ y, F (θ, (pol ω, c (pol ω) θ, y), ω) ∂gaussianReal (s (pol ω) θ) (noiseVar sc) ∂π :=
        lintegral_congr fun θ => lintegral_gauss_affine _ _ (f := fun y => F (θ, (pol ω, c (pol ω) θ, y), ω))
          (hG.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id)))
    _ = ∫⁻ θ, ∫⁻ y, ∫⁻ θ', F (θ', (pol ω, c (pol ω) θ, y), ω)
          ∂bayesUpd π (lik (c (pol ω)) (s (pol ω)) (noiseVar sc) (c (pol ω) θ) y)
          ∂gaussianReal (s (pol ω) θ) (noiseVar sc) ∂π :=
        bayes_step π hcx hsx (noiseVar_ne_zero hsc) hG
    _ = _ := by
        refine lintegral_congr fun θ => (lintegral_gauss_affine _ _ ?_).symm
        exact measurable_lintegral_bayesUpd_param π (P := ℝ) (c := fun _ => c (pol ω))
          (s := fun _ => s (pol ω)) (hcx.comp measurable_snd) (hsx.comp measurable_snd) (noiseVar sc)
          (a := fun _ => c (pol ω) θ) (y := id) measurable_const measurable_id
          (G := fun q => F (q.2, (pol ω, c (pol ω) θ, q.1), ω))
          (hF.comp (measurable_snd.prodMk ((measurable_const.prodMk (measurable_const.prodMk measurable_fst)).prodMk
            measurable_const)))

end Game

end AdversarialBco.Lower.Bayes
