/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.Df2Layer2Proof

@[expose] public section

/-!
# The increments of Lemma U on setting (E): conditional moments

One round of setting (E) (`Df2SetE`), with no definition of the learner: a parameter `σ` measurable in `𝒢`, a draw
`ξ` of law `gam d` independent of `𝒢`, and a noise `e` centred with `E[exp(e²)] ≤ 2` given `𝒢 ⊔ σ(ξ)`. For two
functions `A`, `B` of `(σ, ξ)` of polynomial growth in `ξ`, uniformly in `σ`, the increment

  `Z = A(σ, ξ) + B(σ, ξ) e - ∫ A(σ, z) dγ(z)`

is square integrable, centred given `𝒢`, and `E[Z² | 𝒢] ≤ ∫ (A(σ, z)² + B(σ, z)²) dγ(z)` (`cond_incr`). In the
applications `A = I F φ` and `B = I pip φ`, with `F` the extension, `φ` a direction, `I` a bound condition on the
state, so `Z = I (Y φ - E[Y φ | 𝒢])`.

Proof: the noise is centred given `𝒢' = 𝒢 ⊔ σ(ξ)` and `E[e² | 𝒢'] ≤ 1` (`e² ≤ exp(e²) - 1`), so
`E[Z | 𝒢'] = A - m` and `E[Z² | 𝒢'] ≤ (A - m)² + B²`; then the tower property and Lemma FR (`lemmaFR`).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace AdversarialBco.Poly.EvSI

variable {d : ℕ}

/-- The standard Gaussian law on `Fin d → ℝ`, the law of the draws of setting (E). -/
noncomputable abbrev gam (d : ℕ) : Measure (Fin d → ℝ) := Measure.pi fun _ : Fin d => gaussianReal 0 1

/-- The mean of `A(s, ·)` under `gam d`. -/
noncomputable def mean {S : Type*} (A : S × (Fin d → ℝ) → ℝ) (s : S) : ℝ := ∫ z, A (s, z) ∂(gam d)

/-- The increment `A(σ, ξ) + B(σ, ξ) e - mean A σ`. -/
noncomputable def incr {Ω S : Type*} (A B : S × (Fin d → ℝ) → ℝ) (σ : Ω → S) (ξ : Ω → Fin d → ℝ) (e : Ω → ℝ)
    (ω : Ω) : ℝ :=
  A (σ ω, ξ ω) + B (σ ω, ξ ω) * e ω - mean A (σ ω)

/-! ## Moments -/

/-- Polynomial moments of the Gaussian draw. -/
theorem integrable_poly_gam (k : ℕ) : Integrable (fun z : Fin d → ℝ => (1 + ‖z‖) ^ k) (gam d) := by
  -- Let f be the map to EuclideanSpace
  let f : (Fin d → ℝ) → EuclideanSpace ℝ (Fin d) := WithLp.toLp 2
  have h_map : Measure.map f (gam d) = stdGaussian (EuclideanSpace ℝ (Fin d)) := by
    dsimp [gam]
    rw [ProbabilityTheory.map_pi_eq_stdGaussian (ι := Fin d)]
  -- Step 1: Show integrability of (1 + ‖x‖)^k under stdGaussian
  have h_int_std : Integrable (fun (x : EuclideanSpace ℝ (Fin d)) => (1 + ‖x‖) ^ k)
      (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    -- Use binomial expansion
    by_cases hk : k = 0
    · subst hk; simp
    · have h_expand : (fun (x : EuclideanSpace ℝ (Fin d)) => (1 + ‖x‖) ^ k) =
          fun x => ∑ m ∈ Finset.range (k + 1), ((k.choose m : ℝ) * ‖x‖ ^ (k - m)) := by
        ext x; simp [add_pow, mul_comm]
      rw [h_expand]
      refine integrable_finsetSum _ (fun m hm => ?_)
      -- For each m, we need to show C(k,m) * ‖x‖^(k-m) is integrable
      by_cases hzero : k - m = 0
      · -- If k - m = 0, then ‖x‖^0 = 1
        have : (fun (x : EuclideanSpace ℝ (Fin d)) => (k.choose m : ℝ) * ‖x‖ ^ (k - m)) =
            fun _ => (k.choose m : ℝ) := by
          ext x; simp [hzero]
        rw [this]
        exact integrable_const (μ := stdGaussian (EuclideanSpace ℝ (Fin d))) (c := (k.choose m : ℝ))
      · -- Otherwise, ‖x‖^(k-m) is integrable by MemLp.integrable_norm_pow
        have h_mem : MemLp id ((k - m : ℕ) : ENNReal) (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
          apply ProbabilityTheory.IsGaussian.memLp_id _ ((k - m : ℕ) : ENNReal)
          simp
        have h_int_norm : Integrable (fun (x : EuclideanSpace ℝ (Fin d)) => ‖x‖ ^ (k - m))
            (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
          apply MemLp.integrable_norm_pow h_mem hzero
        -- Multiply by constant
        exact (h_int_norm.const_mul (k.choose m : ℝ))
  -- Step 2: Transfer back using integrable_map_measure
  have h_meas_f : AEMeasurable f (gam d) :=
    (WithLp.measurable_toLp 2 _).aemeasurable
  have h_ae_f : AEStronglyMeasurable (fun (x : EuclideanSpace ℝ (Fin d)) => (1 + ‖x‖) ^ k)
      (Measure.map f (gam d)) := by
    have h_cont : Continuous (fun (x : EuclideanSpace ℝ (Fin d)) => (1 + ‖x‖) ^ k) := by
      continuity
    exact h_cont.aestronglyMeasurable
  -- Use integrable_map_measure: Integrable g (map f μ) ↔ Integrable (g ∘ f) μ
  have h_int_comp : Integrable ((fun (x : EuclideanSpace ℝ (Fin d)) => (1 + ‖x‖) ^ k) ∘ f) (gam d) := by
    apply ((integrable_map_measure h_ae_f h_meas_f).mp ?_)
    rw [h_map]
    exact h_int_std
  -- Now h_int_comp : Integrable (fun z => (1 + ‖WithLp.toLp 2 z‖)^k) (gam d)
  -- We need to relate this to (1 + ‖z‖)^k using the norm inequality
  have h_norm_le : ∀ z : Fin d → ℝ, ‖z‖ ≤ ‖WithLp.toLp 2 z‖ := by
    intro z
    by_cases hne : Nonempty (Fin d)
    · have := hne
      have h' : ∀ i : Fin d, |z i| ≤ ‖WithLp.toLp 2 z‖ := by
        intro i
        have := PiLp.norm_apply_le (WithLp.toLp 2 z) i
        simpa using this
      rw [pi_norm_le_iff_of_nonempty]
      intro i
      simpa using h' i
    · have : IsEmpty (Fin d) := not_nonempty_iff.mp hne
      have hzero : ‖z‖ = 0 := by
        have : ‖z‖ ≤ 0 := by
          simp [Pi.norm_def]
        linarith [norm_nonneg z]
      have hzero2 : ‖WithLp.toLp 2 z‖ = 0 := by
        apply norm_eq_zero.mpr
        ext i
        exact this.elim i
      linarith
  -- Use Integrable.mono' to compare the two functions
  refine Integrable.mono' h_int_comp ?_ ?_
  · -- AEStronglyMeasurable of (1 + ‖z‖)^k
    have h_cont : Continuous (fun (z : Fin d → ℝ) => (1 + ‖z‖) ^ k) := by
      continuity
    exact h_cont.aestronglyMeasurable
  · -- Pointwise inequality of norms
    filter_upwards with z
    have h := h_norm_le z
    have h_nonneg : 0 ≤ ‖z‖ := norm_nonneg _
    -- Use the monotonicity lemma
    have h_mono : (1 + ‖z‖) ^ k ≤ (1 + ‖WithLp.toLp 2 z‖) ^ k :=
      pow_le_pow_left₀ (by linarith) (by linarith) k
    -- Now take norms: since both sides are nonnegative, ‖a‖ = a
    have h_nonneg_left : 0 ≤ (1 + ‖z‖) ^ k := pow_nonneg (by nlinarith) k
    dsimp [f]
    have h_abs : |(1 + ‖z‖) ^ k| = (1 + ‖z‖) ^ k := abs_of_nonneg h_nonneg_left
    rw [h_abs]
    exact h_mono

/-- `e⁴ ≤ 2 exp(e²)`, so the noise has a fourth moment. -/
theorem integrable_four_of_exp {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} {e : Ω → ℝ}
    (he : Measurable e) (hei : Integrable (fun ω => Real.exp (e ω ^ 2)) μ) :
    Integrable (fun ω => (1 + |e ω|) ^ 4) μ := by
  have h_ineq : ∀ x : ℝ, (1 + |x|) ^ 4 ≤ 24 * Real.exp (x ^ 2) := by
    intro x
    have h_x4_eq : x ^ 4 = |x| ^ 4 := by
      have h_sq_eq : x ^ 2 = |x| ^ 2 := by
        simp [sq, abs_mul_abs_self]
      calc
        x ^ 4 = (x ^ 2) ^ 2 := by ring
        _ = (|x| ^ 2) ^ 2 := by rw [h_sq_eq]
        _ = |x| ^ 4 := by ring
    have h_add_le : (1 + |x|) ^ 4 ≤ 8 * (1 + |x| ^ 4) := by
      have h1 : 4*1^3*|x| ≤ 2*1^4 + 2*1^2*|x|^2 := by
        have hpos : 0 ≤ 2*1^2*(1-|x|)^2 := by positivity
        nlinarith
      have h2 : 4*1*|x|^3 ≤ 2*1^2*|x|^2 + 2*|x|^4 := by
        have hpos : 0 ≤ 2*|x|^2*(1-|x|)^2 := by positivity
        nlinarith
      have h3 : 6*1^2*|x|^2 ≤ 3*1^4 + 3*|x|^4 := by
        have hpos : 0 ≤ 3*(1^2 - |x|^2)^2 := by positivity
        nlinarith
      have h4 : 4*1^2*|x|^2 ≤ 2*1^4 + 2*|x|^4 := by
        have hpos : 0 ≤ 2*(1^2 - |x|^2)^2 := by positivity
        nlinarith
      nlinarith
    have h_exp_ineq : x ^ 4 / 2 ≤ Real.exp (x ^ 2) := by
      have hx2_nonneg : 0 ≤ x ^ 2 := sq_nonneg x
      have h_quad := Real.quadratic_le_exp_of_nonneg hx2_nonneg
      nlinarith
    have h_exp_pos : 1 ≤ Real.exp (x ^ 2) := by
      have hx2_nonneg : 0 ≤ x ^ 2 := sq_nonneg x
      exact Real.one_le_exp hx2_nonneg
    calc
      (1 + |x|) ^ 4 ≤ 8 * (1 + |x| ^ 4) := h_add_le
      _ = 8 * (1 + x ^ 4) := by rw [h_x4_eq]
      _ = 8 + 8 * x ^ 4 := by ring
      _ ≤ 8 + 16 * Real.exp (x ^ 2) := by
        nlinarith
      _ ≤ 24 * Real.exp (x ^ 2) := by
        nlinarith
  have h_meas : AEStronglyMeasurable (fun ω => (1 + |e ω|) ^ 4) μ := by
    have h_cont : Continuous (fun x : ℝ => (1 + |x|) ^ 4) := by
      continuity
    have h_meas' : Measurable (fun x : ℝ => (1 + |x|) ^ 4) := h_cont.measurable
    exact (h_meas'.comp he).aestronglyMeasurable
  have h_bound : ∀ᵐ ω ∂μ, ‖(1 + |e ω|) ^ 4‖ ≤ 24 * Real.exp ((e ω) ^ 2) := by
    filter_upwards with ω
    have h := h_ineq (e ω)
    have h_nonneg : 0 ≤ (1 + |e ω|) ^ 4 := by positivity
    have h_norm : ‖(1 + |e ω|) ^ 4‖ = (1 + |e ω|) ^ 4 := abs_of_nonneg h_nonneg
    rw [h_norm]
    exact h
  have h_int : Integrable (fun ω => 24 * Real.exp ((e ω) ^ 2)) μ :=
    hei.const_mul 24
  exact h_int.mono' h_meas h_bound

/-- `E[e² | m] ≤ 1` from `E[exp(e²) | m] ≤ 2`. -/
theorem condExp_sq_le_one {Ω : Type*} (m : MeasurableSpace Ω) {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hm : m ≤ m0) {e : Ω → ℝ} (he : Measurable e)
    (hei : Integrable (fun ω => Real.exp (e ω ^ 2)) μ)
    (hee : μ[fun ω => Real.exp (e ω ^ 2) | m] ≤ᵐ[μ] fun _ => 2) :
    μ[fun ω => e ω ^ 2 | m] ≤ᵐ[μ] fun _ => 1 := by
  have hsq : Integrable (fun ω => e ω ^ 2) μ := by
    refine hei.mono' (he.pow_const 2).aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have := Real.add_one_le_exp (e ω ^ 2)
    linarith
  have hle : (fun ω => e ω ^ 2) ≤ᵐ[μ] fun ω => Real.exp (e ω ^ 2) - 1 :=
    Filter.Eventually.of_forall fun ω => by have := Real.add_one_le_exp (e ω ^ 2); simp only; linarith
  have h1 := condExp_mono (m := m) hsq (hei.sub (integrable_const 1)) hle
  have h2 := condExp_sub hei (integrable_const (1 : ℝ)) m
  rw [condExp_const hm] at h2
  filter_upwards [h1, h2, hee] with ω h1 h2 h3
  rw [h2] at h1
  simp only [Pi.sub_apply] at h1
  linarith

/-- Domination by a polynomial in `‖ξ‖` times `(1 + |e|)^i`, `i ≤ 2`. -/
theorem integrable_of_dom {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ξ : Ω → Fin d → ℝ} {e : Ω → ℝ} (hξ : Measurable ξ) (he : Measurable e) (hlaw : μ.map ξ = gam d)
    (hei : Integrable (fun ω => Real.exp (e ω ^ 2)) μ) {f : Ω → ℝ} (hf : AEStronglyMeasurable f μ) (C : ℝ)
    (i j : ℕ) (hi : i ≤ 2) (hfb : ∀ ω, |f ω| ≤ C * ((1 + ‖ξ ω‖) ^ j * (1 + |e ω|) ^ i)) : Integrable f μ := by
  have hP_nonneg (ω) : 0 ≤ (1 + ‖ξ ω‖) ^ j * (1 + |e ω|) ^ i := by
    positivity
  have h_absC_bound (ω) : |f ω| ≤ |C| * ((1 + ‖ξ ω‖) ^ j * (1 + |e ω|) ^ i) := by
    by_cases hC : 0 ≤ C
    · have hC_abs : |C| = C := abs_of_nonneg hC
      rw [hC_abs]
      exact hfb ω
    · have hC_nonpos : C ≤ 0 := le_of_lt (not_le.mp hC)
      have h_nonpos : C * ((1 + ‖ξ ω‖) ^ j * (1 + |e ω|) ^ i) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hC_nonpos (hP_nonneg ω)
      have h_abs_f_zero : |f ω| = 0 := by
        apply le_antisymm ?_ (abs_nonneg _)
        calc
          |f ω| ≤ C * ((1 + ‖ξ ω‖) ^ j * (1 + |e ω|) ^ i) := hfb ω
          _ ≤ 0 := h_nonpos
      have h_target_nonneg : 0 ≤ |C| * ((1 + ‖ξ ω‖) ^ j * (1 + |e ω|) ^ i) := by
        have h_absC_nonneg : 0 ≤ |C| := abs_nonneg _
        nlinarith
      rw [h_abs_f_zero]
      exact h_target_nonneg
  have h_sq_bound (ω) : (1 + ‖ξ ω‖) ^ j * (1 + |e ω|) ^ i ≤
      ((1 + ‖ξ ω‖) ^ j) ^ 2 + ((1 + |e ω|) ^ i) ^ 2 := by
    have h := two_mul_le_add_sq ((1 + ‖ξ ω‖) ^ j) ((1 + |e ω|) ^ i)
    have h_nonneg_prod : 0 ≤ (1 + ‖ξ ω‖) ^ j * (1 + |e ω|) ^ i := hP_nonneg ω
    nlinarith
  have h_pow_bound (ω) : (1 + |e ω|) ^ (2 * i) ≤ (1 + |e ω|) ^ 4 := by
    have h_base : 1 ≤ 1 + |e ω| := by
      have h_abs_nonneg : 0 ≤ |e ω| := abs_nonneg _
      linarith
    have h_exp : 2 * i ≤ 4 := by omega
    refine Nat.le_induction (by rfl) (fun k hk ih => ?_) 4 h_exp
    rw [pow_succ]
    calc
      (1 + |e ω|) ^ (2 * i) ≤ (1 + |e ω|) ^ k := ih
      _ = (1 + |e ω|) ^ k * 1 := by ring
      _ ≤ (1 + |e ω|) ^ k * (1 + |e ω|) :=
        mul_le_mul_of_nonneg_left h_base (by positivity)
      _ = (1 + |e ω|) ^ (k + 1) := by rw [pow_succ]
  have h_main_bound (ω) : |f ω| ≤ |C| * (((1 + ‖ξ ω‖) ^ j) ^ 2 + (1 + |e ω|) ^ 4) := by
    have h1 : |f ω| ≤ |C| * ((1 + ‖ξ ω‖) ^ j * (1 + |e ω|) ^ i) := h_absC_bound ω
    have h2 : |C| * ((1 + ‖ξ ω‖) ^ j * (1 + |e ω|) ^ i) ≤
        |C| * (((1 + ‖ξ ω‖) ^ j) ^ 2 + ((1 + |e ω|) ^ i) ^ 2) := by
      have h_absC_nonneg : 0 ≤ |C| := abs_nonneg _
      exact mul_le_mul_of_nonneg_left (h_sq_bound ω) h_absC_nonneg
    have h3 : |C| * (((1 + ‖ξ ω‖) ^ j) ^ 2 + ((1 + |e ω|) ^ i) ^ 2) ≤
        |C| * (((1 + ‖ξ ω‖) ^ j) ^ 2 + (1 + |e ω|) ^ 4) := by
      have h_absC_nonneg : 0 ≤ |C| := abs_nonneg _
      have h_sq_le : ((1 + |e ω|) ^ i) ^ 2 ≤ (1 + |e ω|) ^ 4 := by
        calc
          ((1 + |e ω|) ^ i) ^ 2 = (1 + |e ω|) ^ (i * 2) := by rw [← pow_mul]
          _ = (1 + |e ω|) ^ (2 * i) := by rw [mul_comm]
          _ ≤ (1 + |e ω|) ^ 4 := h_pow_bound ω
      have h_add : ((1 + ‖ξ ω‖) ^ j) ^ 2 + ((1 + |e ω|) ^ i) ^ 2 ≤
          ((1 + ‖ξ ω‖) ^ j) ^ 2 + (1 + |e ω|) ^ 4 := by
        nlinarith
      exact mul_le_mul_of_nonneg_left h_add h_absC_nonneg
    linarith
  have h_int1 : Integrable (fun ω => ((1 + ‖ξ ω‖) ^ j) ^ 2) μ := by
    have h_int_gam : Integrable (fun z : Fin d → ℝ => (1 + ‖z‖) ^ (2 * j)) (gam d) :=
      integrable_poly_gam (2 * j)
    rw [← hlaw] at h_int_gam
    have h_map : Integrable ((fun z : Fin d → ℝ => (1 + ‖z‖) ^ (2 * j)) ∘ ξ) μ :=
      h_int_gam.comp_measurable hξ
    have : ((fun z : Fin d → ℝ => (1 + ‖z‖) ^ (2 * j)) ∘ ξ) = (fun ω => ((1 + ‖ξ ω‖) ^ j) ^ 2) := by
      ext ω; simp [← pow_mul, mul_comm]
    rw [this] at h_map
    exact h_map
  have h_int2 : Integrable (fun ω => (1 + |e ω|) ^ 4) μ :=
    integrable_four_of_exp he hei
  have h_int_sum : Integrable (fun ω => ((1 + ‖ξ ω‖) ^ j) ^ 2 + (1 + |e ω|) ^ 4) μ :=
    h_int1.add h_int2
  have h_int_bound : Integrable (fun ω => |C| * (((1 + ‖ξ ω‖) ^ j) ^ 2 + (1 + |e ω|) ^ 4)) μ :=
    h_int_sum.const_mul |C|
  refine Integrable.mono' h_int_bound hf ?_
  refine ae_of_all μ (fun ω => ?_)
  simpa [Real.norm_eq_abs] using h_main_bound ω

/-! ## The increment -/

/-- The mean is measurable in the parameter. -/
theorem measurable_mean {S : Type*} [MeasurableSpace S] {A : S × (Fin d → ℝ) → ℝ} (hA : Measurable A) :
    Measurable (mean A) :=
  (hA.stronglyMeasurable.integral_prod_right' (ν := gam d)).measurable

/-- The increment of one round: square integrable, centred given `𝒢`, with its conditional second moment at most the
Gaussian integral of `A² + B²` at the parameter. -/
theorem cond_incr {Ω S : Type} (𝒢 : MeasurableSpace Ω) {m0 : MeasurableSpace Ω} [MeasurableSpace S]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (h𝒢 : 𝒢 ≤ m0) (σ : Ω → S) (ξ : Ω → Fin d → ℝ) (e : Ω → ℝ)
    (hσ : Measurable[𝒢] σ) (hξ : Measurable ξ) (he : Measurable e) (hlaw : μ.map ξ = gam d)
    (hind : Indep (MeasurableSpace.comap ξ inferInstance) 𝒢 μ)
    (hei : Integrable (fun ω => Real.exp (e ω ^ 2)) μ)
    (hem : μ[e | 𝒢 ⊔ MeasurableSpace.comap ξ inferInstance] =ᵐ[μ] 0)
    (hee : μ[fun ω => Real.exp (e ω ^ 2) | 𝒢 ⊔ MeasurableSpace.comap ξ inferInstance] ≤ᵐ[μ] fun _ => 2)
    (A B : S × (Fin d → ℝ) → ℝ) (hA : Measurable A) (hB : Measurable B) (K : ℝ) (k : ℕ)
    (hK : 0 ≤ K) (hAK : ∀ x, |A x| ≤ K * (1 + ‖x.2‖) ^ k) (hBK : ∀ x, |B x| ≤ K * (1 + ‖x.2‖) ^ k) :
    Integrable (incr A B σ ξ e) μ ∧ Integrable (fun ω => incr A B σ ξ e ω ^ 2) μ ∧
      μ[incr A B σ ξ e | 𝒢] =ᵐ[μ] 0 ∧
      μ[fun ω => incr A B σ ξ e ω ^ 2 | 𝒢] ≤ᵐ[μ] fun ω => ∫ z, (A (σ ω, z) ^ 2 + B (σ ω, z) ^ 2) ∂(gam d) := by
  classical
  have hξle : MeasurableSpace.comap ξ inferInstance ≤ m0 := hξ.comap_le
  have h𝒢G : (𝒢 ⊔ MeasurableSpace.comap ξ inferInstance) ≤ m0 := sup_le h𝒢 hξle
  have hσ' : Measurable[(𝒢 ⊔ MeasurableSpace.comap ξ inferInstance)] σ := hσ.mono le_sup_left le_rfl
  have hξ' : Measurable[(𝒢 ⊔ MeasurableSpace.comap ξ inferInstance)] ξ := (comap_measurable ξ).mono le_sup_right le_rfl
  have hσ0 : Measurable σ := hσ.mono h𝒢 le_rfl
  set a : Ω → ℝ := fun ω => A (σ ω, ξ ω) with ha_def
  set b : Ω → ℝ := fun ω => B (σ ω, ξ ω) with hb_def
  set mσ : Ω → ℝ := fun ω => mean A (σ ω) with hm_def
  have ha' : Measurable[(𝒢 ⊔ MeasurableSpace.comap ξ inferInstance)] a := hA.comp (hσ'.prodMk hξ')
  have hb' : Measurable[(𝒢 ⊔ MeasurableSpace.comap ξ inferInstance)] b := hB.comp (hσ'.prodMk hξ')
  have hm𝒢 : Measurable[𝒢] mσ := (measurable_mean hA).comp hσ
  have hm' : Measurable[(𝒢 ⊔ MeasurableSpace.comap ξ inferInstance)] mσ := hm𝒢.mono le_sup_left le_rfl
  have ha : Measurable a := ha'.mono h𝒢G le_rfl
  have hb : Measurable b := hb'.mono h𝒢G le_rfl
  have hm : Measurable mσ := hm𝒢.mono h𝒢 le_rfl
  -- the Gaussian moments at a fixed parameter
  have hAs : ∀ (s : S) (j : ℕ), Integrable (fun z => |A (s, z)| ^ j) (gam d) := by
    intro s j
    refine ((integrable_poly_gam (d := d) (k * j)).const_mul (K ^ j)).mono'
      ((hA.comp (measurable_const.prodMk measurable_id)).abs.pow_const j).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg _) _), pow_mul, ← mul_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hAK (s, z)) j
  have hBs : ∀ (s : S) (j : ℕ), Integrable (fun z => |B (s, z)| ^ j) (gam d) := by
    intro s j
    refine ((integrable_poly_gam (d := d) (k * j)).const_mul (K ^ j)).mono'
      ((hB.comp (measurable_const.prodMk measurable_id)).abs.pow_const j).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg _) _), pow_mul, ← mul_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hBK (s, z)) j
  have hA1 : ∀ s : S, Integrable (fun z => A (s, z)) (gam d) := fun s =>
    (hAs s 1).mono' (hA.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => by simp)
  set M : ℝ := ∫ z, (1 + ‖z‖) ^ k ∂(gam d) with hMdef
  have hM0 : 0 ≤ M := integral_nonneg fun z => pow_nonneg (by positivity) _
  have hmean : ∀ s, |mean A s| ≤ K * M := by
    intro s
    unfold mean
    refine (abs_integral_le_integral_abs).trans ?_
    rw [hMdef, ← integral_const_mul]
    exact integral_mono (hA1 s).abs ((integrable_poly_gam k).const_mul K) fun z => hAK (s, z)
  -- domination on `Ω`
  have hdom := fun {f : Ω → ℝ} (hf : AEStronglyMeasurable f μ) (C : ℝ) (i j : ℕ) (hi : i ≤ 2)
      (hfb : ∀ ω, |f ω| ≤ C * ((1 + ‖ξ ω‖) ^ j * (1 + |e ω|) ^ i)) =>
    integrable_of_dom hξ he hlaw hei hf C i j hi hfb
  have hP : ∀ ω, 1 ≤ 1 + ‖ξ ω‖ := fun ω => by have := norm_nonneg (ξ ω); linarith
  have hE : ∀ ω, 1 ≤ 1 + |e ω| := fun ω => by have := abs_nonneg (e ω); linarith
  have hPk : ∀ ω, 1 ≤ (1 + ‖ξ ω‖) ^ k := fun ω => one_le_pow₀ (hP ω)
  have hab : ∀ ω, |a ω| ≤ K * (1 + ‖ξ ω‖) ^ k := fun ω => hAK (σ ω, ξ ω)
  have hbb : ∀ ω, |b ω| ≤ K * (1 + ‖ξ ω‖) ^ k := fun ω => hBK (σ ω, ξ ω)
  have hamb : ∀ ω, |a ω - mσ ω| ≤ (K + K * M) * (1 + ‖ξ ω‖) ^ k := by
    intro ω
    calc |a ω - mσ ω| ≤ |a ω| + |mσ ω| := abs_sub _ _
      _ ≤ K * (1 + ‖ξ ω‖) ^ k + K * M := add_le_add (hab ω) (hmean _)
      _ ≤ K * (1 + ‖ξ ω‖) ^ k + K * M * (1 + ‖ξ ω‖) ^ k := by
        have := le_mul_of_one_le_right (mul_nonneg hK hM0) (hPk ω); linarith
      _ = (K + K * M) * (1 + ‖ξ ω‖) ^ k := by ring
  have heb : ∀ ω, |e ω| ≤ 1 + |e ω| := fun ω => by linarith
  -- integrability
  have i_e : Integrable e μ := hdom he.aestronglyMeasurable 1 1 0 (by norm_num) fun ω => by simp
  have i_amb : Integrable (fun ω => a ω - mσ ω) μ :=
    hdom (ha.sub hm).aestronglyMeasurable (K + K * M) 0 k (by norm_num) fun ω => by simpa using hamb ω
  have i_a : Integrable a μ := hdom ha.aestronglyMeasurable K 0 k (by norm_num) fun ω => by simpa using hab ω
  have i_m : Integrable mσ μ := by
    refine (integrable_const (K * M)).mono' hm.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs]; exact hmean _
  have i_be : Integrable (fun ω => b ω * e ω) μ := by
    refine hdom (hb.mul he).aestronglyMeasurable K 1 k (by norm_num) fun ω => ?_
    rw [abs_mul, pow_one]
    have := hbb ω
    calc |b ω| * |e ω| ≤ (K * (1 + ‖ξ ω‖) ^ k) * (1 + |e ω|) :=
          mul_le_mul this (heb ω) (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have i_w2 : Integrable (fun ω => (2 * (a ω - mσ ω) * b ω) * e ω) μ := by
    refine hdom (((ha.sub hm).const_mul 2 |>.mul hb).mul he).aestronglyMeasurable (2 * (K + K * M) * K) 1 (2 * k)
      (by norm_num) fun ω => ?_
    rw [abs_mul, abs_mul, abs_mul, abs_two, pow_one, pow_mul']
    have h1 := hamb ω; have h2 := hbb ω; have h3 := heb ω
    have hpk := pow_nonneg (le_trans zero_le_one (hP ω)) k
    calc 2 * |a ω - mσ ω| * |b ω| * |e ω|
        ≤ 2 * ((K + K * M) * (1 + ‖ξ ω‖) ^ k) * (K * (1 + ‖ξ ω‖) ^ k) * (1 + |e ω|) := by gcongr
      _ = _ := by ring
  have i_w3 : Integrable (fun ω => b ω ^ 2 * e ω ^ 2) μ := by
    refine hdom ((hb.pow_const 2).mul (he.pow_const 2)).aestronglyMeasurable (K ^ 2) 2 (2 * k) le_rfl fun ω => ?_
    rw [abs_mul, abs_pow, abs_pow, pow_mul']
    have h2 := hbb ω; have h3 := heb ω
    calc |b ω| ^ 2 * |e ω| ^ 2 ≤ (K * (1 + ‖ξ ω‖) ^ k) ^ 2 * (1 + |e ω|) ^ 2 := by gcongr
      _ = _ := by ring
  have i_e2 : Integrable (fun ω => e ω ^ 2) μ :=
    hdom (he.pow_const 2).aestronglyMeasurable 1 2 0 le_rfl fun ω => by
      rw [abs_pow]; simpa using pow_le_pow_left₀ (abs_nonneg _) (heb ω) 2
  have i_w1 : Integrable (fun ω => (a ω - mσ ω) ^ 2) μ := by
    refine hdom ((ha.sub hm).pow_const 2).aestronglyMeasurable ((K + K * M) ^ 2) 0 (2 * k) (by norm_num)
      fun ω => ?_
    rw [abs_pow, pow_mul']
    simpa [mul_pow] using pow_le_pow_left₀ (abs_nonneg _) (hamb ω) 2
  have i_b2 : Integrable (fun ω => b ω ^ 2) μ := by
    refine hdom (hb.pow_const 2).aestronglyMeasurable (K ^ 2) 0 (2 * k) (by norm_num) fun ω => ?_
    rw [abs_pow, pow_mul']
    simpa [mul_pow] using pow_le_pow_left₀ (abs_nonneg _) (hbb ω) 2
  have hZ : incr A B σ ξ e = fun ω => (a ω - mσ ω) + b ω * e ω := by
    funext ω; simp only [incr, a, b, mσ]; ring
  have hZ2 : (fun ω => incr A B σ ξ e ω ^ 2) =
      fun ω => ((a ω - mσ ω) ^ 2 + (2 * (a ω - mσ ω) * b ω) * e ω) + b ω ^ 2 * e ω ^ 2 := by
    funext ω; simp only [incr, a, b, mσ]; ring
  have i_Z : Integrable (incr A B σ ξ e) μ := by rw [hZ]; exact i_amb.add i_be
  have i_Z2 : Integrable (fun ω => incr A B σ ξ e ω ^ 2) μ := by rw [hZ2]; exact (i_w1.add i_w2).add i_w3
  refine ⟨i_Z, i_Z2, ?_, ?_⟩
  · -- the conditional mean
    have hc' : μ[incr A B σ ξ e | (𝒢 ⊔ MeasurableSpace.comap ξ inferInstance)] =ᵐ[μ] fun ω => a ω - mσ ω := by
      rw [hZ]
      have h1 := condExp_add i_amb i_be (𝒢 ⊔ MeasurableSpace.comap ξ inferInstance)
      have h2 : μ[fun ω => a ω - mσ ω | (𝒢 ⊔ MeasurableSpace.comap ξ inferInstance)] = fun ω => a ω - mσ ω :=
        condExp_of_stronglyMeasurable h𝒢G (ha'.sub hm').stronglyMeasurable i_amb
      have h3 := condExp_mul_of_stronglyMeasurable_left (m := (𝒢 ⊔ MeasurableSpace.comap ξ inferInstance)) hb'.stronglyMeasurable i_be i_e
      filter_upwards [h1, h3, hem] with ω h1 h3 h4
      have h3' : μ[fun ω => b ω * e ω | (𝒢 ⊔ MeasurableSpace.comap ξ inferInstance)] ω =
          b ω * μ[e | (𝒢 ⊔ MeasurableSpace.comap ξ inferInstance)] ω := h3
      refine h1.trans ?_
      rw [Pi.add_apply, h2, h3', h4]
      simp
    have hT := (condExp_condExp_of_le (f := incr A B σ ξ e) (μ := μ) (le_sup_left : 𝒢 ≤ (𝒢 ⊔ MeasurableSpace.comap ξ inferInstance)) h𝒢G).symm
    have hC := condExp_congr_ae (m := 𝒢) hc'
    have hS := condExp_sub i_a i_m 𝒢
    have hM2 : μ[mσ | 𝒢] = mσ := condExp_of_stronglyMeasurable h𝒢 hm𝒢.stronglyMeasurable i_m
    have hFR := lemmaFR Ω S (Fin d → ℝ) 𝒢 μ σ ξ A h𝒢 hσ hξ hind hA i_a
    rw [hlaw] at hFR
    filter_upwards [hT, hC, hS, hFR] with ω hT hC hS hFR
    rw [hT, hC]
    have : (fun ω => a ω - mσ ω) = a - mσ := rfl
    rw [this, hS, Pi.sub_apply, hM2]
    simp only [Pi.zero_apply]
    rw [hFR]
    simp [mσ, mean]
  · -- the conditional second moment
    have hle' : μ[fun ω => incr A B σ ξ e ω ^ 2 | (𝒢 ⊔ MeasurableSpace.comap ξ inferInstance)] ≤ᵐ[μ] fun ω => (a ω - mσ ω) ^ 2 + b ω ^ 2 := by
      rw [hZ2]
      have h1 := condExp_add (i_w1.add i_w2) i_w3 (𝒢 ⊔ MeasurableSpace.comap ξ inferInstance)
      have h1' := condExp_add i_w1 i_w2 (𝒢 ⊔ MeasurableSpace.comap ξ inferInstance)
      have h2 : μ[fun ω => (a ω - mσ ω) ^ 2 | (𝒢 ⊔ MeasurableSpace.comap ξ inferInstance)] = fun ω => (a ω - mσ ω) ^ 2 :=
        condExp_of_stronglyMeasurable h𝒢G ((ha'.sub hm').pow_const 2).stronglyMeasurable i_w1
      have h3 := condExp_mul_of_stronglyMeasurable_left (m := (𝒢 ⊔ MeasurableSpace.comap ξ inferInstance))
        ((ha'.sub hm').const_mul 2 |>.mul hb').stronglyMeasurable i_w2 i_e
      have h4 := condExp_mul_of_stronglyMeasurable_left (m := (𝒢 ⊔ MeasurableSpace.comap ξ inferInstance)) (hb'.pow_const 2).stronglyMeasurable i_w3 i_e2
      have h5 := condExp_sq_le_one (𝒢 ⊔ MeasurableSpace.comap ξ inferInstance) h𝒢G he hei hee
      filter_upwards [h1, h1', h3, h4, h5, hem] with ω h1 h1' h3 h4 h5 h6
      have h3' : μ[fun ω => (2 * (a ω - mσ ω) * b ω) * e ω | (𝒢 ⊔ MeasurableSpace.comap ξ inferInstance)] ω =
          (2 * (a ω - mσ ω) * b ω) * μ[e | (𝒢 ⊔ MeasurableSpace.comap ξ inferInstance)] ω := h3
      have h4' : μ[fun ω => b ω ^ 2 * e ω ^ 2 | (𝒢 ⊔ MeasurableSpace.comap ξ inferInstance)] ω =
          b ω ^ 2 * μ[fun ω => e ω ^ 2 | (𝒢 ⊔ MeasurableSpace.comap ξ inferInstance)] ω := h4
      refine le_of_eq_of_le h1 ?_
      rw [Pi.add_apply]
      refine le_of_eq_of_le (congrArg (· + _) h1') ?_
      rw [Pi.add_apply, h2, h3', h4', h6]
      simp only [Pi.zero_apply, mul_zero, add_zero]
      have hb2 : 0 ≤ b ω ^ 2 := sq_nonneg _
      nlinarith [mul_le_mul_of_nonneg_left h5 hb2]
    have hT := (condExp_condExp_of_le (f := fun ω => incr A B σ ξ e ω ^ 2) (μ := μ)
      (le_sup_left : 𝒢 ≤ (𝒢 ⊔ MeasurableSpace.comap ξ inferInstance)) h𝒢G).symm
    have hMono := condExp_mono (m := 𝒢) integrable_condExp (i_w1.add i_b2) hle'
    have hF : Measurable fun x : S × (Fin d → ℝ) => (A x - mean A x.1) ^ 2 + B x ^ 2 :=
      ((hA.sub ((measurable_mean hA).comp measurable_fst)).pow_const 2).add (hB.pow_const 2)
    have hFR := lemmaFR Ω S (Fin d → ℝ) 𝒢 μ σ ξ (fun x => (A x - mean A x.1) ^ 2 + B x ^ 2) h𝒢 hσ hξ hind hF
      (i_w1.add i_b2)
    rw [hlaw] at hFR
    filter_upwards [hT, hMono, hFR] with ω hT hMono hFR
    rw [hT]
    refine hMono.trans ?_
    have e2 : (fun ω => (a ω - mσ ω) ^ 2 + b ω ^ 2) = fun ω => (A (σ ω, ξ ω) - mean A (σ ω, ξ ω).1) ^ 2 +
        B (σ ω, ξ ω) ^ 2 := rfl
    refine le_of_eq_of_le hFR ?_
    -- `∫ (A - m)² ≤ ∫ A²`
    set s := σ ω
    have iA2 : Integrable (fun z => A (s, z) ^ 2) (gam d) := by
      simpa [sq_abs] using hAs s 2
    have iB2 : Integrable (fun z => B (s, z) ^ 2) (gam d) := by
      simpa [sq_abs] using hBs s 2
    have iAm2 : Integrable (fun z => (A (s, z) - mean A s) ^ 2) (gam d) := by
      have : (fun z => (A (s, z) - mean A s) ^ 2) =
          fun z => A (s, z) ^ 2 - 2 * mean A s * A (s, z) + mean A s ^ 2 := by funext z; ring
      rw [this]; exact (iA2.sub ((hA1 s).const_mul _)).add (integrable_const _)
    have hvar : ∫ z, (A (s, z) - mean A s) ^ 2 ∂(gam d) = ∫ z, A (s, z) ^ 2 ∂(gam d) - mean A s ^ 2 := by
      have : (fun z => (A (s, z) - mean A s) ^ 2) =
          fun z => A (s, z) ^ 2 - 2 * mean A s * A (s, z) + mean A s ^ 2 := by funext z; ring
      have i1 : Integrable (fun z => A (s, z) ^ 2 - 2 * mean A s * A (s, z)) (gam d) :=
        iA2.sub ((hA1 s).const_mul _)
      have i2 : Integrable (fun z => 2 * mean A s * A (s, z)) (gam d) := (hA1 s).const_mul _
      rw [this, integral_add i1 (integrable_const _), integral_sub iA2 i2, integral_const_mul, integral_const]
      simp only [probReal_univ, smul_eq_mul, one_mul]
      rw [show ∫ z, A (s, z) ∂(gam d) = mean A s from rfl]
      ring
    show ∫ z, ((A (s, z) - mean A (s, z).1) ^ 2 + B (s, z) ^ 2) ∂(gam d) ≤ ∫ z, (A (s, z) ^ 2 + B (s, z) ^ 2) ∂(gam d)
    simp only
    rw [integral_add iAm2 iB2, integral_add iA2 iB2, hvar]
    nlinarith [sq_nonneg (mean A s)]

end AdversarialBco.Poly.EvSI
