/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.Df2EvGTools
public import AdversarialBco.Poly.Df2EvSIRound

@[expose] public section

/-!
# Lemma SK' (ii), (iii), (v): the Gaussian facts

* `chi2_tail`: `P(|ξ|² > b) ≤ exp(-(√b - √d)²/2)` for `d ≤ b`, by the concentration of the norm at the constant
  `1/2` (`EvGY.gauge_conc` on the unit ball) and `E|ξ| ≤ √d`; `chi2_tail_b0`: `P(|ξ|² > 2d + c) ≤ exp(-c/4)`;
* `pi_tail_at`, `pi_round_at`: the gauge tail of `EvGY.pi_tail` at any threshold `θ ≥ 2`,
  `P(π(μ + T g) > θ) ≤ exp(-2 L (θ - 2)²)`;
* `int_dot_pow_four`, `int_dot_pow_eight`, `int_dot_sq_sub_pow_four`: `E⟨ξ, b⟩⁴ ≤ √105 |b|⁴`,
  `E⟨ξ, b⟩⁸ ≤ √2027025 |b|⁸`, `E(⟨ξ, b⟩² - |b|²)⁴ ≤ (√2027025 + 1) |b|⁸` (the directions of (c), (d), (e)).
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped Matrix

namespace AdversarialBco.UW.SKp

open AdversarialBco.Poly AdversarialBco.Poly.EvSI

variable {d : ℕ}

/-! ## The chi-square tail -/

/-- `x ⬝ x = |x|²` in the Euclidean norm. -/
theorem dot_self_eq_norm_sq (x : Fin d → ℝ) : x ⬝ᵥ x = ‖(WithLp.toLp 2 x : E d)‖ ^ 2 := by
  rw [norm_toLp, Real.sq_sqrt (dot_self_nonneg' x)]

/-- **The chi-square tail** by the concentration of the norm: `P(|ξ|² > b) ≤ exp(-(√b - √d)²/2)` for `d ≤ b`. -/
theorem chi2_tail (hd : 1 ≤ d) (b : ℝ) (hb : (d : ℝ) ≤ b) :
    (Measure.pi fun _ : Fin d => gaussianReal 0 1) {x | b < x ⬝ᵥ x} ≤
      ENNReal.ofReal (Real.exp (-((Real.sqrt b - Real.sqrt d) ^ 2 / 2))) := by
  set K : Set (E d) := Metric.closedBall 0 1 with hKdef
  set T : E d →L[ℝ] E d := ContinuousLinearMap.id ℝ (E d) with hTdef
  have hgK : ∀ x : E d, gauge K x = ‖x‖ := fun x => by rw [hKdef, gauge_closedBall zero_le_one, div_one]
  have hTn : ‖T‖ = 1 := by
    refine le_antisymm ContinuousLinearMap.norm_id_le ?_
    set x : E d := EuclideanSpace.single (⟨0, hd⟩ : Fin d) (1 : ℝ) with hx
    have hx1 : ‖x‖ = 1 := by rw [hx, EuclideanSpace.norm_single, norm_one]
    have h := T.le_opNorm x
    rw [hx1, mul_one] at h
    rwa [hTdef, ContinuousLinearMap.id_apply, hx1] at h
  set t := Real.sqrt b - Real.sqrt d with htdef
  have ht : 0 ≤ t := sub_nonneg.2 (Real.sqrt_le_sqrt hb)
  set c := ∫ h, gauge K (T h) ∂(stdGaussian (E d)) with hcdef
  have hc : c ≤ Real.sqrt d := by
    have e : (fun h : E d => gauge K (T h)) = fun h => ‖h‖ := by
      funext h; rw [hgK, hTdef, ContinuousLinearMap.id_apply]
    rw [hcdef, e]
    exact AdversarialBco.integral_norm_stdGaussian_le d
  have hconc := EvGY.gauge_conc K (convex_closedBall 0 1) Metric.isClosed_closedBall le_rfl T t ht
  rw [hTn] at hconc
  have hcont : Continuous fun g : E d => gauge K (T g) := by
    have e : (fun g : E d => gauge K (T g)) = fun g => ‖g‖ := by
      funext g; rw [hgK, hTdef, ContinuousLinearMap.id_apply]
    rw [e]; exact continuous_norm
  have hmeas : MeasurableSet {g : E d | c + t ≤ gauge K (T g)} :=
    measurableSet_le measurable_const hcont.measurable
  have hsub : {x : Fin d → ℝ | b < x ⬝ᵥ x} ⊆
      (WithLp.toLp 2 : (Fin d → ℝ) → E d) ⁻¹' {g : E d | c + t ≤ gauge K (T g)} := by
    intro x hx
    simp only [Set.mem_preimage, Set.mem_ofPred_eq] at hx ⊢
    rw [hgK, hTdef, ContinuousLinearMap.id_apply]
    have hb0 : 0 ≤ b := le_trans (Nat.cast_nonneg d) hb
    have h1 : Real.sqrt b < ‖(WithLp.toLp 2 x : E d)‖ := by
      rw [← Real.sqrt_sq (norm_nonneg (WithLp.toLp 2 x : E d)), ← dot_self_eq_norm_sq]
      exact Real.sqrt_lt_sqrt hb0 hx
    have : c + t ≤ Real.sqrt b := by rw [htdef]; linarith
    linarith
  calc (Measure.pi fun _ : Fin d => gaussianReal 0 1) {x | b < x ⬝ᵥ x}
      ≤ (Measure.pi fun _ : Fin d => gaussianReal 0 1)
          ((WithLp.toLp 2 : (Fin d → ℝ) → E d) ⁻¹' {g : E d | c + t ≤ gauge K (T g)}) := measure_mono hsub
    _ = stdGaussian (E d) {g : E d | c + t ≤ gauge K (T g)} := by
        rw [← map_pi_eq_stdGaussian, Measure.map_apply (WithLp.measurable_toLp 2 _) hmeas]
    _ ≤ ENNReal.ofReal (Real.exp (-(t ^ 2 / (2 * 1 ^ 2)))) := hconc
    _ = ENNReal.ofReal (Real.exp (-((Real.sqrt b - Real.sqrt d) ^ 2 / 2))) := by
        rw [htdef]; norm_num

/-- `(√(2a + c) - √a)² ≥ c/2` for `a, c ≥ 0`. -/
theorem sqrt_gap (a c : ℝ) (ha : 0 ≤ a) (hc : 0 ≤ c) : c / 2 ≤ (Real.sqrt (2 * a + c) - Real.sqrt a) ^ 2 := by
  set x := Real.sqrt a with hx
  set y := Real.sqrt (2 * a + c) with hy
  have hx2 : x ^ 2 = a := Real.sq_sqrt ha
  have hy2 : y ^ 2 = 2 * a + c := Real.sq_sqrt (by linarith)
  nlinarith [sq_nonneg (2 * x - y)]

/-- `P(|ξ|² > 2d + c) ≤ exp(-c/4)` for `c ≥ 0`. -/
theorem chi2_tail_b0 (hd : 1 ≤ d) (c b : ℝ) (hc : 0 ≤ c) (hb : 2 * d + c ≤ b) :
    (Measure.pi fun _ : Fin d => gaussianReal 0 1) {x | b < x ⬝ᵥ x} ≤ ENNReal.ofReal (Real.exp (-(c / 4))) := by
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  set c' := b - 2 * d with hc'
  have hc'0 : c ≤ c' := by rw [hc']; linarith
  have hbd : (d : ℝ) ≤ b := by linarith
  refine (chi2_tail hd b hbd).trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_))
  have hb' : b = 2 * d + c' := by rw [hc']; ring
  have h := sqrt_gap (d : ℝ) c' hd0 (by linarith)
  rw [← hb'] at h
  linarith

/-! ## The gauge tail at a threshold -/

open Topology Filter in
/-- The gauge tail of `EvGY.pi_tail` at a threshold `θ ≥ 2`: `P(π(μ + T g) > θ) ≤ exp(-2 L (θ - 2)²)` for
`π(μ) ≤ 1`, `‖T‖ ≤ 1/(2 √L)`, `L ≥ 1`. -/
theorem pi_tail_at (hd : 1 ≤ d) (K : Set (E d)) (hK : Convex ℝ K) (hKc : IsClosed K)
    (hball : Metric.closedBall 0 1 ⊆ K) (hMw : pgMw K ≤ df2Mw d) (mu : E d) (hmu : gauge K mu ≤ 1)
    (T : E d →L[ℝ] E d) (Le : ℝ) (hLe : 1 ≤ Le) (hT : ‖T‖ ≤ 1 / (2 * Real.sqrt Le)) (θ : ℝ) (hθ : 2 ≤ θ) :
    stdGaussian (E d) {g | θ < gauge K (mu + T g)} ≤ ENNReal.ofReal (Real.exp (-(2 * Le * (θ - 2) ^ 2))) := by
  set γ := stdGaussian (E d) with hγ
  set s := 1 / (2 * Real.sqrt Le) with hs_def
  set c := ∫ g, gauge K (T g) ∂γ with hc_def
  set t := θ - 2 with ht_def
  have hLe_pos : 0 < Le := by linarith
  have hsqrt_pos : 0 < Real.sqrt Le := Real.sqrt_pos.mpr hLe_pos
  have hs_nonneg : 0 ≤ s := by rw [hs_def]; positivity
  have ht_nonneg : 0 ≤ t := by rw [ht_def]; linarith
  have h_absorbent : Absorbent ℝ K := by
    have hball_mem : Metric.closedBall (0 : E d) 1 ∈ 𝓝 (0 : E d) :=
      Metric.closedBall_mem_nhds 0 (by norm_num : (0 : ℝ) < 1)
    exact absorbent_nhds_zero (mem_of_superset hball_mem hball)
  by_cases hT_zero : ‖T‖ = 0
  · have hT_eq_zero : T = 0 := norm_eq_zero.mp hT_zero
    have h_empty : {g | θ < gauge K (mu + T g)} = (∅ : Set (E d)) := by
      ext g
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
      rw [hT_eq_zero, ContinuousLinearMap.zero_apply, add_zero]
      linarith
    rw [h_empty, measure_empty]
    exact zero_le
  · have hT_pos : 0 < ‖T‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hT_zero)
    have hc_le_one : c ≤ 1 := by
      have h_mean : c ≤ s * pgMw K * Real.sqrt (d : ℝ) := EvGY.gauge_mean_le hd K hK hKc hball T s hs_nonneg hT
      have h_mw_small : df2Mw d * Real.sqrt (d : ℝ) ≤ 2 * Real.sqrt Le := EvGY.mw_small hd Le hLe
      have h_factor_nonneg : 0 ≤ s * Real.sqrt (d : ℝ) := mul_nonneg hs_nonneg (Real.sqrt_nonneg _)
      calc c ≤ s * pgMw K * Real.sqrt (d : ℝ) := h_mean
        _ = (s * Real.sqrt (d : ℝ)) * pgMw K := by ring
        _ ≤ (s * Real.sqrt (d : ℝ)) * df2Mw d := mul_le_mul_of_nonneg_left hMw h_factor_nonneg
        _ = s * (df2Mw d * Real.sqrt (d : ℝ)) := by ring
        _ ≤ s * (2 * Real.sqrt Le) := mul_le_mul_of_nonneg_left h_mw_small hs_nonneg
        _ = 1 := by rw [hs_def]; field_simp
    have h_subset : {g | θ < gauge K (mu + T g)} ⊆ {g | c + t ≤ gauge K (T g)} := by
      intro g hg
      simp only [Set.mem_ofPred_eq] at hg ⊢
      have h_add : gauge K (mu + T g) ≤ gauge K mu + gauge K (T g) := gauge_add_le hK h_absorbent mu (T g)
      rw [ht_def]
      linarith
    have h_gc : γ {g | c + t ≤ gauge K (T g)} ≤ ENNReal.ofReal (Real.exp (-(t ^ 2 / (2 * ‖T‖ ^ 2)))) :=
      EvGY.gauge_conc K hK hKc hball T t ht_nonneg
    have hT_sq_le : ‖T‖ ^ 2 ≤ 1 / (4 * Le) := by
      have h_sq : ‖T‖ ^ 2 ≤ s ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hT 2
      have h_s_sq : s ^ 2 = 1 / (4 * Le) := by
        rw [hs_def, div_pow, mul_pow, Real.sq_sqrt hLe_pos.le]; norm_num
      rwa [h_s_sq] at h_sq
    have h_exp_ineq : Real.exp (-(t ^ 2 / (2 * ‖T‖ ^ 2))) ≤ Real.exp (-(2 * Le * t ^ 2)) := by
      refine Real.exp_le_exp.mpr (neg_le_neg ?_)
      have hpos : 0 < 2 * ‖T‖ ^ 2 := by positivity
      rw [le_div_iff₀ hpos]
      have h4 : 4 * Le * ‖T‖ ^ 2 ≤ 1 := by
        calc 4 * Le * ‖T‖ ^ 2 ≤ 4 * Le * (1 / (4 * Le)) := mul_le_mul_of_nonneg_left hT_sq_le (by positivity)
          _ = 1 := by field_simp
      nlinarith [sq_nonneg t]
    calc γ {g | θ < gauge K (mu + T g)} ≤ γ {g | c + t ≤ gauge K (T g)} := measure_mono h_subset
      _ ≤ ENNReal.ofReal (Real.exp (-(t ^ 2 / (2 * ‖T‖ ^ 2)))) := h_gc
      _ ≤ ENNReal.ofReal (Real.exp (-(2 * Le * (θ - 2) ^ 2))) := ENNReal.ofReal_le_ofReal h_exp_ineq

/-- The gauge tail of one round at a threshold `θ ≥ 2`, on `ℝ^d` with the matrix `A` of the state (the form of
`EvGY.pi_round_law`). -/
theorem pi_round_at (hd : 1 ≤ d) (K : Set (E d)) (hK : Convex ℝ K) (hKc : IsClosed K)
    (hball : Metric.closedBall 0 1 ⊆ K) (hMw : pgMw K ≤ df2Mw d) (mu : Fin d → ℝ)
    (hmu : gauge K (WithLp.toLp 2 mu) ≤ 1) (A : Matrix (Fin d) (Fin d) ℝ) (lam : ℝ) (hlam0 : 0 ≤ lam)
    (hlam1 : lam ≤ 1) (Le : ℝ) (hLe : 1 ≤ Le) (hA : ∀ w, (A *ᵥ w) ⬝ᵥ (A *ᵥ w) ≤ 2 * (1 / (8 * Le)) * (w ⬝ᵥ w))
    (θ : ℝ) (hθ : 2 ≤ θ) :
    (Measure.pi fun _ : Fin d => gaussianReal 0 1)
        {x | θ < gauge K (WithLp.toLp 2 (mu + (1 - lam) • (A *ᵥ x)))} ≤
      ENNReal.ofReal (Real.exp (-(2 * Le * (θ - 2) ^ 2))) := by
  set T := (1 - lam) • Matrix.toEuclideanCLM (𝕜 := ℝ) A with hTdef
  have hLe_pos : 0 < Le := by linarith
  have hk_pos : 0 ≤ 2 * (1 / (8 * Le)) := by positivity
  have hA_norm : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A‖ ≤ Real.sqrt (2 * (1 / (8 * Le))) :=
    EvGY.toEuclideanCLM_norm_le A (2 * (1 / (8 * Le))) hk_pos hA
  have h_sqrt : Real.sqrt (2 * (1 / (8 * Le))) = 1 / (2 * Real.sqrt Le) := by
    rw [show 2 * (1 / (8 * Le)) = 1 / (4 * Le) by field_simp; ring, Real.sqrt_div' 1 (by positivity : (0 : ℝ) ≤ 4 * Le),
      Real.sqrt_one, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), show Real.sqrt 4 = 2 by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  have hT_norm : ‖T‖ ≤ 1 / (2 * Real.sqrt Le) := by
    rw [hTdef, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - lam), ← h_sqrt]
    have h0 : 0 ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A‖ := norm_nonneg _
    have h1 : 1 - lam ≤ 1 := by linarith
    nlinarith
  have h_meas : Measurable (WithLp.toLp 2 : (Fin d → ℝ) → E d) := WithLp.measurable_toLp 2 _
  have h_set_eq : {x : Fin d → ℝ | θ < gauge K (WithLp.toLp 2 (mu + (1 - lam) • (A *ᵥ x)))} =
      (WithLp.toLp 2) ⁻¹' {g : E d | θ < gauge K (WithLp.toLp 2 mu + T g)} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_ofPred_eq]
    rw [WithLp.toLp_add, WithLp.toLp_smul, hTdef, ContinuousLinearMap.smul_apply, Matrix.toEuclideanCLM_toLp]
  have h_gauge_measurable : MeasurableSet {g : E d | θ < gauge K (WithLp.toLp 2 mu + T g)} := by
    have h_cont : Continuous (gauge K : E d → ℝ) :=
      continuous_gauge hK (Filter.mem_of_superset (Metric.closedBall_mem_nhds 0 (by norm_num : (0 : ℝ) < 1)) hball)
    exact measurableSet_lt measurable_const
      (h_cont.comp (continuous_const.add T.continuous)).measurable
  rw [h_set_eq, ← Measure.map_apply h_meas h_gauge_measurable, map_pi_eq_stdGaussian]
  exact pi_tail_at hd K hK hKc hball hMw (WithLp.toLp 2 mu) hmu T Le hLe hT_norm θ hθ

/-! ## Moments -/

/-- `x^{2k} = 1{0 < |x|} x^{2k}` for `k ≥ 1`, at `x = ⟨z, u⟩`. -/
theorem pow_eq_indicator (u : Fin d → ℝ) (k : ℕ) (hk : 1 ≤ k) :
    (fun z : Fin d → ℝ => (z ⬝ᵥ u) ^ (2 * k)) =
      {z : Fin d → ℝ | (0 : ℝ) < |z ⬝ᵥ u|}.indicator (fun z => (z ⬝ᵥ u) ^ (2 * k)) := by
  funext z
  by_cases h : (0 : ℝ) < |z ⬝ᵥ u|
  · rw [Set.indicator_of_mem (show z ∈ {z : Fin d → ℝ | (0 : ℝ) < |z ⬝ᵥ u|} from h)]
  · rw [Set.indicator_of_notMem (show z ∉ {z : Fin d → ℝ | (0 : ℝ) < |z ⬝ᵥ u|} from h)]
    have h0 : z ⬝ᵥ u = 0 := abs_eq_zero.1 (le_antisymm (not_lt.1 h) (abs_nonneg _))
    rw [h0, zero_pow (by omega)]

/-- `E⟨ξ, u⟩^{2k} ≤ √((4k - 1)!!)` for a unit `u` (`tail_dot` at `T = 0`). -/
theorem int_unit_pow (u : Fin d → ℝ) (hu : u ⬝ᵥ u = 1) (k : ℕ) (hk : 1 ≤ k) :
    ∫ z, (z ⬝ᵥ u) ^ (2 * k) ∂(gam d) ≤ Real.sqrt ((4 * k - 1).doubleFactorial) := by
  rw [pow_eq_indicator u k hk]
  have ht := tail_dot u hu k 0 hk le_rfl
  have e : Real.exp (-(0 : ℝ) ^ 2 / 4) = 1 := by norm_num
  rw [e, mul_one] at ht
  exact ht

/-- `E⟨ξ, b⟩^{2k} ≤ √((4k - 1)!!) |b|^{2k}`. -/
theorem int_dot_pow (b : Fin d → ℝ) (k : ℕ) (hk : 1 ≤ k) :
    ∫ z, (z ⬝ᵥ b) ^ (2 * k) ∂(gam d) ≤ Real.sqrt ((4 * k - 1).doubleFactorial) * (b ⬝ᵥ b) ^ k := by
  by_cases hb : b ⬝ᵥ b = 0
  · rw [dot_self_eq_zero hb]
    simp only [dotProduct_zero, zero_pow (show 2 * k ≠ 0 by omega), zero_pow (show k ≠ 0 by omega),
      integral_zero, mul_zero, le_refl]
  set u := (Real.sqrt (b ⬝ᵥ b))⁻¹ • b with hu
  have hu1 : u ⬝ᵥ u = 1 := unit_of_ne hb
  have e1 : (fun z => (z ⬝ᵥ b) ^ (2 * k)) = fun z => (b ⬝ᵥ b) ^ k * (z ⬝ᵥ u) ^ (2 * k) := by
    funext z
    rw [pow_mul, dot_eq_unit hb z, mul_pow, ← pow_mul]
  rw [e1, integral_const_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right (int_unit_pow u hu1 k hk) (pow_nonneg (dot_self_nonneg' b) k)

/-- `E⟨ξ, b⟩⁴ ≤ √105 |b|⁴`. -/
theorem int_dot_pow_four (b : Fin d → ℝ) : ∫ z, (z ⬝ᵥ b) ^ 4 ∂(gam d) ≤ Real.sqrt 105 * (b ⬝ᵥ b) ^ 2 := by
  have h := int_dot_pow b 2 (by norm_num)
  have h7 : ((4 * 2 - 1 : ℕ)).doubleFactorial = 105 := by decide
  rw [h7] at h
  simpa using h

/-- `E⟨ξ, b⟩⁸ ≤ √2027025 |b|⁸`. -/
theorem int_dot_pow_eight (b : Fin d → ℝ) :
    ∫ z, (z ⬝ᵥ b) ^ 8 ∂(gam d) ≤ Real.sqrt 2027025 * (b ⬝ᵥ b) ^ 4 := by
  have h := int_dot_pow b 4 (by norm_num)
  have h15 : ((4 * 4 - 1 : ℕ)).doubleFactorial = 2027025 := by decide
  rw [h15] at h
  simpa using h

/-- `(a - c)⁴ ≤ a⁴ + c⁴` for `a, c ≥ 0`. -/
theorem sub_pow_four_le (a c : ℝ) (ha : 0 ≤ a) (hc : 0 ≤ c) : (a - c) ^ 4 ≤ a ^ 4 + c ^ 4 := by
  rcases le_total c a with h | h
  · have h1 : (a - c) ^ 4 ≤ a ^ 4 := pow_le_pow_left₀ (by linarith) (by linarith) 4
    nlinarith [pow_nonneg hc 4]
  · have h1 : (c - a) ^ 4 ≤ c ^ 4 := pow_le_pow_left₀ (by linarith) (by linarith) 4
    have e : (a - c) ^ 4 = (c - a) ^ 4 := by ring
    nlinarith [pow_nonneg ha 4]

/-- `E(⟨ξ, b⟩² - |b|²)⁴ ≤ (√2027025 + 1) |b|⁸`. -/
theorem int_dot_sq_sub_pow_four (b : Fin d → ℝ) :
    ∫ z, ((z ⬝ᵥ b) ^ 2 - b ⬝ᵥ b) ^ 4 ∂(gam d) ≤ (Real.sqrt 2027025 + 1) * (b ⬝ᵥ b) ^ 4 := by
  have hb0 := dot_self_nonneg' b
  have hpt : ∀ z : Fin d → ℝ, ((z ⬝ᵥ b) ^ 2 - b ⬝ᵥ b) ^ 4 ≤ (z ⬝ᵥ b) ^ 8 + (b ⬝ᵥ b) ^ 4 := by
    intro z
    have h := sub_pow_four_le ((z ⬝ᵥ b) ^ 2) (b ⬝ᵥ b) (sq_nonneg _) hb0
    calc _ ≤ ((z ⬝ᵥ b) ^ 2) ^ 4 + (b ⬝ᵥ b) ^ 4 := h
      _ = _ := by ring
  have hi8 : Integrable (fun z : Fin d → ℝ => (z ⬝ᵥ b) ^ 8) (gam d) :=
    (memLp_dot_pow b 8 1 (by norm_num)).integrable le_rfl
  have hi : Integrable (fun z : Fin d → ℝ => (z ⬝ᵥ b) ^ 8 + (b ⬝ᵥ b) ^ 4) (gam d) := hi8.add (integrable_const _)
  have hm := integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => by positivity) hi
    (Filter.Eventually.of_forall hpt)
  have hc : ∫ _ : Fin d → ℝ, (b ⬝ᵥ b) ^ 4 ∂(gam d) = (b ⬝ᵥ b) ^ 4 := by simp
  rw [integral_add hi8 (integrable_const _), hc] at hm
  have h8 := int_dot_pow_eight b
  linarith

end AdversarialBco.UW.SKp
