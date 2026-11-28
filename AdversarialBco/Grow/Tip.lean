/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Conj1Lower.CellsRound
public import AdversarialBco.Conj1Lower.Moments

@[expose] public section

/-!
# The tip law of Route G: the vertices of a cube, and its cells

The static dent of Theorem GROW draws its tip from a law on `B(0, 1/2)` with no
ripe cell at any play. Here the law is uniform on the `2^d` vertices of the cube `[-a, a]^d`, `a = 1/(2 √d)`
(`tipLaw`), all on the sphere `‖θ‖ = 1/2`, in the frame `m = 0`, `A = 2 (d + 2)^{1/2} I` (`frameG`):

* `integral_tipLaw`: `E f(θ) = 2^{-d} Σ_ε f(vtx ε)`;
* `mgf_tipLaw_le`: `E e^{s ⟨w, θ⟩} ≤ e^{s² a² ‖w‖²/2}` (a product of `cosh`, Hoeffding for Rademacher signs);
* `tail_mass_le`, `tail_moment_le`: with `v = a² c²`, `P(⟨w, θ⟩ > t) ≤ e^{-t²/(2v)}` and
  `E[⟨w, θ⟩²; ⟨w, θ⟩ > t] ≤ 2 e^{t - t²/(2v)}` for `‖w‖ ≤ c`, `t ≥ v`;
* `restSet_tipLaw`: no cell is ripe (the outer and inner cells hold no vertex, the tail is small), so rest is everything.
-/

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal RealInnerProductSpace

namespace AdversarialBco.Grow

open AdversarialBco.Lower

/-! ## The vertex law -/

/-- The half-side `a = 1/(2 √d)` of the cube. -/
noncomputable def side (d : ℕ) : ℝ := 1 / (2 * Real.sqrt d)

/-- The vertex of the cube `[-a, a]^d` with the sign pattern `ε`. -/
noncomputable def vtx (d : ℕ) (ε : Fin d → Bool) : E d :=
  WithLp.toLp 2 (fun i => if ε i then side d else -side d)

/-- The tip law: uniform on the `2^d` vertices. -/
noncomputable def tipLaw (d : ℕ) : Measure (E d) :=
  (PMF.uniformOfFintype (Fin d → Bool)).toMeasure.map (vtx d)

variable {d : ℕ}

theorem measurable_vtx : Measurable (vtx d) := measurable_of_countable _

instance isProbabilityMeasure_tipLaw : IsProbabilityMeasure (tipLaw d) := by
  unfold tipLaw
  infer_instance

/-- `E f(θ) = 2^{-d} Σ_ε f(vtx ε)`. -/
theorem integral_tipLaw {f : E d → ℝ} (hf : Measurable f) :
    ∫ θ, f θ ∂tipLaw d = ((2 : ℝ) ^ d)⁻¹ * ∑ ε : Fin d → Bool, f (vtx d ε) := by
  unfold tipLaw
  rw [integral_map measurable_vtx.aemeasurable hf.aestronglyMeasurable, PMF.integral_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ε _ => ?_
  rw [PMF.uniformOfFintype_apply, smul_eq_mul]
  congr 1
  simp [Fintype.card_bool, Fintype.card_fin]

theorem vtx_apply (ε : Fin d → Bool) (i : Fin d) :
    (vtx d ε).ofLp i = if ε i then side d else -side d := rfl

theorem side_sq (hd : 1 ≤ d) : side d ^ 2 = 1 / (4 * d) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  unfold side
  rw [div_pow, mul_pow, Real.sq_sqrt hd0.le]
  ring

/-- Every vertex lies on the sphere `‖θ‖ = 1/2`. -/
theorem norm_vtx (hd : 1 ≤ d) (ε : Fin d → Bool) : ‖vtx d ε‖ = 1 / 2 := by
  have hsq : ‖vtx d ε‖ ^ 2 = 1 / 4 := by
    rw [EuclideanSpace.norm_sq_eq]
    have : ∀ i : Fin d, ‖(vtx d ε).ofLp i‖ ^ 2 = side d ^ 2 := fun i => by
      rw [vtx_apply, Real.norm_eq_abs, sq_abs]
      split_ifs <;> ring
    simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, side_sq hd]
    have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
    field_simp
  have h0 := norm_nonneg (vtx d ε)
  nlinarith

/-- The tip law is carried by the sphere `‖θ‖ = 1/2`. -/
theorem tipLaw_sphere (hd : 1 ≤ d) : tipLaw d {θ | ‖θ‖ ≠ 1 / 2} = 0 := by
  unfold tipLaw
  have hS : MeasurableSet {θ : E d | ‖θ‖ ≠ 1 / 2} := (measurableSet_singleton (1 / 2 : ℝ)).compl.preimage measurable_norm
  rw [Measure.map_apply measurable_vtx hS]
  have : vtx d ⁻¹' {θ | ‖θ‖ ≠ 1 / 2} = ∅ := by
    ext ε
    simp [norm_vtx hd ε]
  rw [this, measure_empty]

/-! ## The moment generating function -/

theorem inner_vtx (w : E d) (ε : Fin d → Bool) :
    ⟪w, vtx d ε⟫ = ∑ i, w.ofLp i * (if ε i then side d else -side d) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [dotProduct, star_trivial, vtx_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- `E e^{s ⟨w, θ⟩} ≤ e^{s² a² ‖w‖²/2}`: a product of `cosh`. -/
theorem mgf_tipLaw_le (w : E d) (s : ℝ) :
    ∫ θ, Real.exp (s * ⟪w, θ⟫) ∂tipLaw d ≤ Real.exp (s ^ 2 * side d ^ 2 * ‖w‖ ^ 2 / 2) := by
  have hm : Measurable fun θ : E d => Real.exp (s * ⟪w, θ⟫) :=
    Real.measurable_exp.comp (measurable_const.mul (measurable_const.inner measurable_id))
  rw [integral_tipLaw hm]
  have hprod : ((2 : ℝ) ^ d)⁻¹ * ∑ ε : Fin d → Bool, Real.exp (s * ⟪w, vtx d ε⟫) =
      ∏ i : Fin d, Real.cosh (s * side d * w.ofLp i) := by
    have h1 : ∀ ε : Fin d → Bool, Real.exp (s * ⟪w, vtx d ε⟫) =
        ∏ i, Real.exp (s * (w.ofLp i * (if ε i then side d else -side d))) := fun ε => by
      rw [inner_vtx, Finset.mul_sum, Real.exp_sum]
    simp only [h1]
    have h2 : ((2 : ℝ) ^ d)⁻¹ = ∏ _i : Fin d, (2 : ℝ)⁻¹ := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, inv_pow]
    rw [← Fintype.prod_sum (fun (i : Fin d) (b : Bool) =>
      Real.exp (s * (w.ofLp i * (if b then side d else -side d)))), h2, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Fintype.sum_bool, Real.cosh_eq]
    simp only [ite_true, Bool.false_eq_true, ite_false]
    ring_nf
  rw [hprod]
  calc ∏ i : Fin d, Real.cosh (s * side d * w.ofLp i)
      ≤ ∏ i : Fin d, Real.exp ((s * side d * w.ofLp i) ^ 2 / 2) :=
        Finset.prod_le_prod₀ (fun i _ => (Real.cosh_pos _).le) fun i _ => Real.cosh_le_exp_half_sq _
    _ = Real.exp (s ^ 2 * side d ^ 2 * ‖w‖ ^ 2 / 2) := by
        rw [← Real.exp_sum, EuclideanSpace.norm_sq_eq]
        congr 1
        rw [Finset.mul_sum, Finset.sum_div]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Real.norm_eq_abs, sq_abs]
        ring

theorem integrable_tipLaw {f : E d → ℝ} (hf : Measurable f) : Integrable f (tipLaw d) := by
  unfold tipLaw
  exact (integrable_map_measure hf.aestronglyMeasurable measurable_vtx.aemeasurable).2 Integrable.of_finite

/-! ## The tail of a linear form -/

/-- Chernoff: `P(⟨w, θ⟩ > t) ≤ e^{-t²/(2v)}` for `‖w‖ ≤ c`, `v = a² c² > 0`. -/
theorem tail_mass_le (w : E d) {c t : ℝ} (hw : ‖w‖ ≤ c) (hv : 0 < side d ^ 2 * c ^ 2) (ht : 0 ≤ t) :
    (tipLaw d).real {θ | t < ⟪w, θ⟫} ≤ Real.exp (-t ^ 2 / (2 * (side d ^ 2 * c ^ 2))) := by
  set v := side d ^ 2 * c ^ 2 with hv_def
  have hX : Measurable fun θ : E d => ⟪w, θ⟫ := measurable_const.inner measurable_id
  have hs : 0 ≤ t / v := div_nonneg ht hv.le
  have h := measure_ge_le_exp_mul_mgf (X := fun θ : E d => ⟪w, θ⟫) (μ := tipLaw d) t hs
    (integrable_tipLaw (Real.measurable_exp.comp (measurable_const.mul hX)))
  have hm : mgf (fun θ : E d => ⟪w, θ⟫) (tipLaw d) (t / v) ≤ Real.exp ((t / v) ^ 2 * v / 2) := by
    refine (mgf_tipLaw_le w (t / v)).trans (Real.exp_le_exp.2 ?_)
    have hw2 : ‖w‖ ^ 2 ≤ c ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hw 2
    have : (t / v) ^ 2 * side d ^ 2 * ‖w‖ ^ 2 ≤ (t / v) ^ 2 * side d ^ 2 * c ^ 2 :=
      mul_le_mul_of_nonneg_left hw2 (by positivity)
    rw [hv_def] at this ⊢
    nlinarith
  calc (tipLaw d).real {θ | t < ⟪w, θ⟫} ≤ (tipLaw d).real {θ | t ≤ ⟪w, θ⟫} :=
        measureReal_mono fun θ (hθ : t < ⟪w, θ⟫) => (le_of_lt hθ : t ≤ ⟪w, θ⟫)
    _ ≤ Real.exp (-(t / v) * t) * mgf (fun θ : E d => ⟪w, θ⟫) (tipLaw d) (t / v) := h
    _ ≤ Real.exp (-(t / v) * t) * Real.exp ((t / v) ^ 2 * v / 2) :=
        mul_le_mul_of_nonneg_left hm (Real.exp_pos _).le
    _ = Real.exp (-t ^ 2 / (2 * v)) := by
        rw [← Real.exp_add]
        congr 1
        field_simp
        ring

/-- `E[⟨w, θ⟩²; ⟨w, θ⟩ > t] ≤ 2 e^{t - t²/(2v)}` for `‖w‖ ≤ c`, `v = a² c²`, `t ≥ v > 0`. -/
theorem tail_moment_le (w : E d) {c t : ℝ} (hw : ‖w‖ ≤ c) (hv : 0 < side d ^ 2 * c ^ 2)
    (ht : side d ^ 2 * c ^ 2 ≤ t) :
    ∫ θ in {θ | t < ⟪w, θ⟫}, ⟪w, θ⟫ ^ 2 ∂tipLaw d ≤ 2 * Real.exp (t - t ^ 2 / (2 * (side d ^ 2 * c ^ 2))) := by
  set v := side d ^ 2 * c ^ 2 with hv_def
  have hX : Measurable fun θ : E d => ⟪w, θ⟫ := measurable_const.inner measurable_id
  have ht0 : 0 < t := hv.trans_le ht
  set lam := t / v - 1 with hlam
  have hlam0 : 0 ≤ lam := by
    rw [hlam, sub_nonneg, le_div_iff₀ hv]
    linarith
  have hS : MeasurableSet {θ : E d | t < ⟪w, θ⟫} := measurableSet_lt measurable_const hX
  have hpt : ∀ θ : E d, {θ : E d | t < ⟪w, θ⟫}.indicator (fun θ => ⟪w, θ⟫ ^ 2) θ ≤
      2 * Real.exp (-lam * t) * Real.exp (t / v * ⟪w, θ⟫) := fun θ => by
    by_cases hθ : t < ⟪w, θ⟫
    · rw [Set.indicator_of_mem (show θ ∈ {θ : E d | t < ⟪w, θ⟫} from hθ)]
      have hY : 0 ≤ ⟪w, θ⟫ := ht0.le.trans hθ.le
      have h1 := Real.quadratic_le_exp_of_nonneg hY
      have h2 : 1 ≤ Real.exp (lam * (⟪w, θ⟫ - t)) :=
        Real.one_le_exp (mul_nonneg hlam0 (by linarith))
      have h3 : Real.exp ⟪w, θ⟫ * Real.exp (lam * (⟪w, θ⟫ - t)) = Real.exp (-lam * t) * Real.exp (t / v * ⟪w, θ⟫) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        rw [hlam]
        ring
      have h4 : ⟪w, θ⟫ ^ 2 ≤ 2 * Real.exp ⟪w, θ⟫ := by nlinarith
      have h5 : 0 ≤ Real.exp ⟪w, θ⟫ := (Real.exp_pos _).le
      nlinarith
    · rw [Set.indicator_of_notMem (show θ ∉ {θ : E d | t < ⟪w, θ⟫} from hθ)]
      positivity
  rw [← integral_indicator hS]
  have hint : Integrable (fun θ => 2 * Real.exp (-lam * t) * Real.exp (t / v * ⟪w, θ⟫)) (tipLaw d) :=
    integrable_tipLaw (measurable_const.mul (Real.measurable_exp.comp (measurable_const.mul hX)))
  have hm : ∫ θ, Real.exp (t / v * ⟪w, θ⟫) ∂tipLaw d ≤ Real.exp ((t / v) ^ 2 * v / 2) := by
    refine (mgf_tipLaw_le w (t / v)).trans (Real.exp_le_exp.2 ?_)
    have hw2 : ‖w‖ ^ 2 ≤ c ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hw 2
    have : (t / v) ^ 2 * side d ^ 2 * ‖w‖ ^ 2 ≤ (t / v) ^ 2 * side d ^ 2 * c ^ 2 :=
      mul_le_mul_of_nonneg_left hw2 (by positivity)
    rw [hv_def] at this ⊢
    nlinarith
  calc ∫ θ, {θ : E d | t < ⟪w, θ⟫}.indicator (fun θ => ⟪w, θ⟫ ^ 2) θ ∂tipLaw d
      ≤ ∫ θ, 2 * Real.exp (-lam * t) * Real.exp (t / v * ⟪w, θ⟫) ∂tipLaw d :=
        integral_mono (integrable_tipLaw ((hX.pow_const 2).indicator hS)) hint hpt
    _ = 2 * Real.exp (-lam * t) * ∫ θ, Real.exp (t / v * ⟪w, θ⟫) ∂tipLaw d := integral_const_mul _ _
    _ ≤ 2 * Real.exp (-lam * t) * Real.exp ((t / v) ^ 2 * v / 2) :=
        mul_le_mul_of_nonneg_left hm (by positivity)
    _ = 2 * Real.exp (t - t ^ 2 / (2 * v)) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        rw [hlam]
        field_simp
        ring

/-! ## The frame and the cells -/

/-- The scale `c = 2 (d + 2)^{1/2}` of the frame: `|v|_M = c ‖v‖`, `M = 4 (d + 2) I`. -/
noncomputable def frameC (d : ℕ) : ℝ := 2 * Real.sqrt (d + 2)

/-- The frame of the static dent: `A = c I`. -/
noncomputable def frameG (d : ℕ) : E d →L[ℝ] E d := frameC d • ContinuousLinearMap.id ℝ (E d)

theorem frameC_pos (d : ℕ) : 0 < frameC d := by unfold frameC; positivity

theorem frameC_sq (d : ℕ) : frameC d ^ 2 = 4 * (d + 2) := by
  unfold frameC
  rw [mul_pow, Real.sq_sqrt (by positivity)]
  ring

theorem frameG_apply (v : E d) : frameG d v = frameC d • v := rfl

theorem norm_frameG_apply (v : E d) : ‖frameG d v‖ = frameC d * ‖v‖ := by
  rw [frameG_apply, norm_smul, Real.norm_eq_abs, abs_of_pos (frameC_pos d)]

theorem norm_frameG_le : ‖frameG d‖ ≤ frameC d :=
  ContinuousLinearMap.opNorm_le_bound _ (frameC_pos d).le fun v => (norm_frameG_apply v).le

/-- The direction of the read: `T = ⟨u, θ⟩` with `u = (c/‖x‖) x`. -/
noncomputable def dirG (d : ℕ) (x : E d) : E d := (frameC d / ‖x‖) • x

theorem norm_dirG_le (x : E d) : ‖dirG d x‖ ≤ frameC d := by
  unfold dirG
  rw [norm_smul, Real.norm_eq_abs]
  by_cases hx : x = 0
  · simp [hx, (frameC_pos d).le]
  · have hx0 : 0 < ‖x‖ := norm_pos_iff.2 hx
    rw [abs_of_pos (div_pos (frameC_pos d) hx0), div_mul_cancel₀ _ hx0.ne']

/-- The read of the frame at the centre `0`: `T(θ, x) = ⟨u, θ⟩`. -/
theorem readT_frameG (θ x : E d) : readT (frameG d) 0 θ x = ⟪dirG d x, θ⟫ := by
  unfold readT dirG
  simp only [sub_zero, frameG_apply, norm_smul, Real.norm_eq_abs, abs_of_pos (frameC_pos d), inner_smul_left,
    inner_smul_right, RCLike.conj_to_real]
  by_cases hx : x = 0
  · simp [hx]
  · have hx0 : 0 < ‖x‖ := norm_pos_iff.2 hx
    have hc := frameC_pos d
    field_simp

/-- On the sphere `‖θ‖ = 1/2`, `|θ|_M² = d + 2`. -/
theorem norm_frameG_sphere {θ : E d} (hθ : ‖θ‖ = 1 / 2) : ‖frameG d (θ - 0)‖ ^ 2 = d + 2 := by
  rw [sub_zero, norm_frameG_apply, mul_pow, frameC_sq, hθ]
  ring

theorem side_sq_frameC_sq (hd : 1 ≤ d) : side d ^ 2 * frameC d ^ 2 = ((d : ℝ) + 2) / d := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  rw [side_sq hd, frameC_sq]
  field_simp

theorem cellSet_tail_frameG (k dd DMv : ℝ) (x : E d) :
    cellSet (frameG d) 0 k dd DMv x Cell.tail = {θ | Real.sqrt (2 * k) < ⟪dirG d x, θ⟫} := by
  ext θ
  simp only [cellSet, Set.mem_ofPred_eq, cellOf_tail_iff, readT_frameG]

/-- The outer and inner cells hold no vertex. -/
theorem tipLaw_outer_inner (hd : 1 ≤ d) (k : ℝ) (x : E d) :
    (tipLaw d).real (cellSet (frameG d) 0 k d d x Cell.outer) = 0 ∧
      (tipLaw d).real (cellSet (frameG d) 0 k d d x Cell.inner) = 0 := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hsub : ∀ c, c = Cell.outer ∨ c = Cell.inner → cellSet (frameG d) 0 k d d x c ⊆ {θ | ‖θ‖ ≠ 1 / 2} := by
    intro c hc θ hθ hn
    have hR := norm_frameG_sphere (d := d) hn
    simp only [cellSet, Set.mem_ofPred_eq] at hθ
    rcases hc with rfl | rfl
    · rw [cellOf_outer_iff] at hθ
      linarith [hθ.2]
    · rw [cellOf_inner_iff] at hθ
      linarith [hθ.2.2]
  have h0 := tipLaw_sphere hd
  exact ⟨by rw [measureReal_def, measure_mono_null (hsub _ (Or.inl rfl)) h0, ENNReal.toReal_zero],
    by rw [measureReal_def, measure_mono_null (hsub _ (Or.inr rfl)) h0, ENNReal.toReal_zero]⟩

/-- **U-CELLS** for the vertex law: no cell is ripe at any play, under the two tail inequalities. -/
theorem not_ripe_tipLaw (hd : 1 ≤ d) {k : ℝ} (hk : 0 < k) (x : E d)
    (hv : ((d : ℝ) + 2) / d ≤ Real.sqrt (2 * k))
    (h1 : Real.exp (-(k * d / (d + 2))) < k ^ 3 / (d : ℝ) ^ 3)
    (h2 : 2 * Real.exp (Real.sqrt (2 * k) - k * d / (d + 2)) < k ^ 3 / (d : ℝ) ^ 2) (c : Cell) :
    ¬ ripe (tipLaw d) (frameG d) 0 k d d x c := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hv0 : 0 < side d ^ 2 * frameC d ^ 2 := by rw [side_sq_frameC_sq hd]; positivity
  have hsq : Real.sqrt (2 * k) ^ 2 / (2 * (side d ^ 2 * frameC d ^ 2)) = k * d / (d + 2) := by
    rw [Real.sq_sqrt (by linarith), side_sq_frameC_sq hd]
    field_simp
  obtain ⟨ho, hi⟩ := tipLaw_outer_inner hd k x
  cases c with
  | tail =>
    simp only [ripe, not_or, not_le, cellSet_tail_frameG, readT_frameG]
    constructor
    · refine lt_of_le_of_lt (tail_mass_le (dirG d x) (norm_dirG_le x) hv0 (Real.sqrt_nonneg _)) ?_
      rw [neg_div, hsq]
      exact h1
    · refine lt_of_le_of_lt (tail_moment_le (dirG d x) (norm_dirG_le x) hv0 ?_) ?_
      · rw [side_sq_frameC_sq hd]; exact hv
      · rw [hsq]; exact h2
  | outer =>
    simp only [ripe, not_le, ho, epsShell]
    positivity
  | inner =>
    simp only [ripe, not_le, hi, epsShell]
    positivity
  | regular => simp [ripe]

/-- Rest is everything. -/
theorem restSet_tipLaw (hd : 1 ≤ d) {k : ℝ} (hk : 0 < k) (x : E d)
    (hv : ((d : ℝ) + 2) / d ≤ Real.sqrt (2 * k))
    (h1 : Real.exp (-(k * d / (d + 2))) < k ^ 3 / (d : ℝ) ^ 3)
    (h2 : 2 * Real.exp (Real.sqrt (2 * k) - k * d / (d + 2)) < k ^ 3 / (d : ℝ) ^ 2) :
    restSet (tipLaw d) (frameG d) 0 k d d x = Set.univ := by
  rw [restSet_eq]
  ext θ
  simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
  exact not_ripe_tipLaw hd hk x hv h1 h2 _

end AdversarialBco.Grow
