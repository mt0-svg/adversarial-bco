/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import Mathlib

@[expose] public section

/-!
# Gaussians from fair coins: Box-Muller at B bits

B fair coins give the cell index `j ∈ {1, ..., 2^B}` of a uniform `u ∈ (0, 1]`, that is `u` rounded up to the grid
`2^{-B}`. Box-Muller on the exact pair `(u, w)` gives an exact standard Gaussian; on the rounded pair it gives the
draw the algorithm makes. The two are coupled pathwise.

* Rounding: `dyadic_ceil`, `j = ⌈2^B u⌉` lies in `[1, 2^B]` and `0 ≤ j/2^B - u < 2^{-B}`; `dyadic_cell`, each cell
  `{u ∈ (0, 1] : ⌈2^B u⌉ = j}` has Lebesgue measure `2^{-B}`; `dyadic_law`, so `j` has the law of B fair coins.
* Exact law: `boxMuller_law2`, the map `(u, w) ↦ (R cos 2πw, R sin 2πw)` with `R = (-2 log u)^{1/2}` sends the
  uniform law on `(0, 1]²` to the standard Gaussian law on `ℝ²`; `boxMuller_law`, each coordinate is `N(0, 1)`. The
  pieces: `gauss_prod_density` (the density `e^{-|p|²/2}/(2π)` of the pair), `bm_polar` (polar coordinates),
  `bm_radius` (the substitution `ρ = (-2 log u)^{1/2}`), `bm_angle` (`θ = 2πv - π`), `bm_neg` (the law is even).
* Pathwise coupling: `boxMuller_radius`, `|R(u) - R(u')| ≤ 2^{1 - B/2}` for `u, u' ∈ [2^{-B/2}, 1]` at distance at
  most `2^{-B}`; `boxMuller_path`, `|Z - Z'| ≤ 2^{1 - B/2} + 2π B^{1/2} 2^{-B}` for both coordinates;
  `tail_volume`, the event `u < 2^{-B/2}` has probability `2^{-B/2}`; `boxMuller_coupling` (one coordinate) and
  `boxMuller_pair` (both), the exact draw and the B-bit draw differ by more than that bound with probability at most
  `2^{-B/2}`.

Each lemma sits in a namespace
`AdversarialBco.Bit.Aux_<name>` with its helpers, the lemma itself at `AdversarialBco.Bit.<name>`.
-/
open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius

namespace AdversarialBco.Bit.Aux_dyadic_ceil


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

theorem _root_.AdversarialBco.Bit.dyadic_ceil (B : ℕ) (u : ℝ) (hu0 : 0 < u) (hu1 : u ≤ 1) :
    1 ≤ ⌈(2 : ℝ) ^ B * u⌉ ∧ ⌈(2 : ℝ) ^ B * u⌉ ≤ 2 ^ B ∧ u ≤ (⌈(2 : ℝ) ^ B * u⌉ : ℝ) / 2 ^ B ∧
      (⌈(2 : ℝ) ^ B * u⌉ : ℝ) / 2 ^ B - u < (2 : ℝ) ^ (-(B : ℝ)) := by
  set N := (2 : ℝ) ^ B
  set k := ⌈N * u⌉
  have hNpos : 0 < N := pow_pos (by norm_num) B
  have hN_nonneg : 0 ≤ N := le_of_lt hNpos
  have hNu_pos : 0 < N * u := mul_pos hNpos hu0
  have hNu_le_N : N * u ≤ N := by
    nlinarith
  have hk_pos : 0 < k := by
    rw [Int.ceil_pos]
    exact hNu_pos
  have h1 : 1 ≤ k := by omega
  have h2 : k ≤ (2 ^ B : ℤ) := by
    rw [Int.ceil_le]
    -- need: N * u ≤ ((2 ^ B : ℤ) : ℝ) = N
    simpa [N, Nat.cast_pow, Nat.cast_ofNat]
  have hle_ceil : N * u ≤ (k : ℝ) := by
    -- Int.ceil_le: ⌈a⌉ ≤ z ↔ a ≤ (z : ℝ)
    exact ((Int.ceil_le (a := N * u) (z := k)).mp (le_refl k))
  have h3 : u ≤ (k : ℝ) / N := by
    calc
      u = (N * u) / N := by field_simp [hNpos.ne.symm]
      _ ≤ (k : ℝ) / N := div_le_div_of_nonneg_right hle_ceil hN_nonneg
  have hceil_lt : (k : ℝ) < N * u + 1 := by
    simpa [k] using Int.ceil_lt_add_one (N * u)
  have h4 : (k : ℝ) / N - u < (2 : ℝ) ^ (-(B : ℝ)) := by
    have hdiv : (k : ℝ) / N < u + 1 / N := by
      calc
        (k : ℝ) / N < (N * u + 1) / N := div_lt_div_of_pos_right hceil_lt hNpos
        _ = u + 1 / N := by field_simp [hNpos.ne.symm]
    have hgoal : (k : ℝ) / N - u < 1 / N := by linarith
    have hN_inv : 1 / N = (2 : ℝ) ^ (-(B : ℝ)) := by
      calc
        1 / N = N⁻¹ := by field_simp
        _ = ((2 : ℝ) ^ B)⁻¹ := rfl
        _ = ((2 : ℝ) ^ (B : ℝ))⁻¹ := by rw [Real.rpow_natCast]
        _ = (2 : ℝ) ^ (-(B : ℝ)) := by rw [Real.rpow_neg (by norm_num : 0 ≤ (2 : ℝ))]
    rw [hN_inv] at hgoal
    exact hgoal
  exact And.intro h1 (And.intro h2 (And.intro h3 h4))

end AdversarialBco.Bit.Aux_dyadic_ceil

namespace AdversarialBco.Bit.Aux_dyadic_cell


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

theorem _root_.AdversarialBco.Bit.dyadic_cell (B : ℕ) (j : ℤ) (hj1 : 1 ≤ j) (hj2 : j ≤ 2 ^ B) :
    volume {u : ℝ | u ∈ Set.Ioc 0 1 ∧ ⌈(2 : ℝ) ^ B * u⌉ = j} = ENNReal.ofReal ((2 : ℝ) ^ (-(B : ℝ))) := by
  have hNpos : 0 < (2 : ℝ) ^ B := pow_pos (by norm_num) B
  have hNpos' : 0 ≤ (2 : ℝ) ^ B := le_of_lt hNpos
  set N := (2 : ℝ) ^ B with hN
  have hNpos_set : 0 < N := hNpos
  have hNpos'_set : 0 ≤ N := hNpos'
  have hj1ℝ : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj1
  have hj2ℝ : (j : ℝ) ≤ N := by
    simpa [hN] using mod_cast hj2
  have h_lower : 0 ≤ ((j : ℝ) - 1) / N :=
    div_nonneg (by linarith) hNpos'_set
  have h_upper : (j : ℝ) / N ≤ 1 :=
    (div_le_one hNpos_set).mpr hj2ℝ
  have h_set_eq : {u : ℝ | u ∈ Set.Ioc 0 1 ∧ ⌈N * u⌉ = j} = Set.Ioc (((j : ℝ) - 1) / N) ((j : ℝ) / N) := by
    ext u
    constructor
    · intro ⟨⟨hu0, hu1⟩, hceil⟩
      have hceil' := (Int.ceil_eq_iff (a := N * u) (z := j)).mp hceil
      rcases hceil' with ⟨hlt, hle⟩
      have hlt' : ((j : ℝ) - 1) / N < u := by
        apply (div_lt_iff₀ hNpos_set).mpr
        rw [mul_comm] at hlt
        exact hlt
      have hle' : u ≤ (j : ℝ) / N := by
        apply (le_div_iff₀ hNpos_set).mpr
        rw [mul_comm]
        exact hle
      exact ⟨hlt', hle'⟩
    · intro ⟨hlt, hle⟩
      have hceil : ⌈N * u⌉ = j := by
        apply (Int.ceil_eq_iff (a := N * u) (z := j)).mpr
        constructor
        · apply (div_lt_iff₀ hNpos_set).mp at hlt
          rw [mul_comm] at hlt
          exact hlt
        · apply (le_div_iff₀ hNpos_set).mp at hle
          rw [mul_comm] at hle
          exact hle
      have hu0 : 0 < u := by
        linarith
      have hu1 : u ≤ 1 := by
        linarith
      exact ⟨⟨hu0, hu1⟩, hceil⟩
  rw [h_set_eq]
  rw [Real.volume_Ioc]
  have h_diff : ((j : ℝ) / N) - (((j : ℝ) - 1) / N) = (1 : ℝ) / N := by
    ring
  rw [h_diff]
  rw [one_div]
  calc
    ENNReal.ofReal (N⁻¹) = ENNReal.ofReal (((2 : ℝ) ^ (B : ℝ))⁻¹) := by
      rw [Real.rpow_natCast (2 : ℝ) B]
    _ = ENNReal.ofReal ((2 : ℝ) ^ (-(B : ℝ))) := by
      rw [Real.rpow_neg (show 0 ≤ (2 : ℝ) from by norm_num) (B : ℝ)]

end AdversarialBco.Bit.Aux_dyadic_cell

namespace AdversarialBco.Bit.Aux_dyadic_law


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius

theorem _root_.AdversarialBco.Bit.dyadic_law (B : ℕ) (j : ℤ) :
    (volume.restrict (Set.Ioc (0 : ℝ) 1)).map (fun u : ℝ => ⌈(2 : ℝ) ^ B * u⌉) {j} =
      if 1 ≤ j ∧ j ≤ 2 ^ B then ENNReal.ofReal ((2 : ℝ) ^ (-(B : ℝ))) else 0 := by
  let φ : ℝ → ℤ := fun u => ⌈(2 : ℝ) ^ B * u⌉
  have hφ_meas : Measurable φ :=
    Int.measurable_ceil.comp (measurable_const.mul measurable_id)
  have h_singleton_meas : MeasurableSet ({j} : Set ℤ) :=
    MeasurableSet.singleton j
  have h_Ioc_meas : MeasurableSet (Set.Ioc (0 : ℝ) 1) :=
    measurableSet_Ioc
  rw [Measure.map_apply hφ_meas h_singleton_meas]
  rw [Measure.restrict_apply' h_Ioc_meas]
  have h_set_eq : φ ⁻¹' {j} ∩ Set.Ioc (0 : ℝ) 1 =
      {u : ℝ | u ∈ Set.Ioc (0 : ℝ) 1 ∧ ⌈(2 : ℝ) ^ B * u⌉ = j} := by
    ext u; simp [φ, and_comm]
  rw [h_set_eq]
  by_cases hj : 1 ≤ j ∧ j ≤ 2 ^ B
  · rw [if_pos hj, dyadic_cell B j hj.1 hj.2]
  · rw [if_neg hj]
    have h_empty : {u : ℝ | u ∈ Set.Ioc (0 : ℝ) 1 ∧ ⌈(2 : ℝ) ^ B * u⌉ = j} = ∅ := by
      ext u
      constructor
      · intro ⟨hu, hceil⟩
        have hpos : 0 < (2 : ℝ) ^ B * u := by
          have h2pos : 0 < (2 : ℝ) ^ B := pow_pos (by norm_num) B
          exact mul_pos h2pos hu.1
        have hceil1 : 1 ≤ ⌈(2 : ℝ) ^ B * u⌉ :=
          (Int.one_le_ceil_iff.mpr hpos)
        have hceil2 : ⌈(2 : ℝ) ^ B * u⌉ ≤ 2 ^ B := by
          have hceil_le : ⌈(2 : ℝ) ^ B * u⌉ ≤ (2 ^ B : ℤ) :=
            (Int.ceil_le (a := (2 : ℝ) ^ B * u) (z := (2 ^ B : ℤ))).mpr (by
              push_cast
              have h2pos' : 0 ≤ (2 : ℝ) ^ B := pow_nonneg (by norm_num) B
              nlinarith [hu.2, h2pos'])
          exact hceil_le
        rw [hceil] at hceil1 hceil2
        exact absurd (And.intro hceil1 hceil2) hj
      · intro h; exact False.elim h
    rw [h_empty]; simp

end AdversarialBco.Bit.Aux_dyadic_law

namespace AdversarialBco.Bit.Aux_tail_volume


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

theorem _root_.AdversarialBco.Bit.tail_volume (B : ℕ) :
    volume (Set.Ioc (0 : ℝ) 1 ∩ Set.Iio ((2 : ℝ) ^ (-(B : ℝ) / 2))) = ENNReal.ofReal ((2 : ℝ) ^ (-(B : ℝ) / 2)) := by
  set c := (2 : ℝ) ^ (-(B : ℝ) / 2) with hc
  have hpos : 0 < c := by
    dsimp [c]
    exact Real.rpow_pos_of_pos (by norm_num : 0 < (2 : ℝ)) _
  have hle : c ≤ 1 := by
    dsimp [c]
    refine Real.rpow_le_one_of_one_le_of_nonpos (by norm_num : 1 ≤ (2 : ℝ)) ?_
    have hB : 0 ≤ (B : ℝ) := Nat.cast_nonneg _
    nlinarith
  have hset : Set.Ioc (0 : ℝ) 1 ∩ Set.Iio c = Set.Ioo (0 : ℝ) c := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Iio, Set.mem_Ioo]
    constructor
    · intro ⟨⟨hx1, hx2⟩, hx3⟩
      exact ⟨hx1, hx3⟩
    · intro ⟨hx1, hx2⟩
      have hx2' : x ≤ 1 := by linarith
      exact ⟨⟨hx1, hx2'⟩, hx2⟩
  calc
    volume (Set.Ioc (0 : ℝ) 1 ∩ Set.Iio c) = volume (Set.Ioo (0 : ℝ) c) := by rw [hset]
    _ = ENNReal.ofReal (c - 0) := by rw [Real.volume_Ioo]
    _ = ENNReal.ofReal c := by simp

end AdversarialBco.Bit.Aux_tail_volume

namespace AdversarialBco.Bit.Aux_boxMuller_radius


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

set_option maxHeartbeats 400000 in
theorem _root_.AdversarialBco.Bit.boxMuller_radius (B : ℕ) (u v : ℝ) (hu : (2 : ℝ) ^ (-(B : ℝ) / 2) ≤ u)
    (hv : (2 : ℝ) ^ (-(B : ℝ) / 2) ≤ v) (hu1 : u ≤ 1) (hv1 : v ≤ 1) (huv : |u - v| ≤ (2 : ℝ) ^ (-(B : ℝ))) :
    |Real.sqrt (-2 * Real.log u) - Real.sqrt (-2 * Real.log v)| ≤ (2 : ℝ) ^ (1 - (B : ℝ) / 2) := by
  set c := (2 : ℝ) ^ (-(B : ℝ) / 2) with hc_def
  set h := (2 : ℝ) ^ (-(B : ℝ)) with hh_def
  have h_two_pos : 0 < (2 : ℝ) := by norm_num
  have h_two_nonneg : 0 ≤ (2 : ℝ) := by norm_num
  have hc_pos : 0 < c := Real.rpow_pos_of_pos h_two_pos _
  have hc_nonneg : 0 ≤ c := le_of_lt hc_pos
  have hh_pos : 0 < h := Real.rpow_pos_of_pos h_two_pos _
  have hh_nonneg : 0 ≤ h := le_of_lt hh_pos
  have hpos_u : 0 < u := lt_of_lt_of_le hc_pos hu
  have hpos_v : 0 < v := lt_of_lt_of_le hc_pos hv
  -- h = c^2
  have h_sq_eq : h = c ^ 2 := by
    calc
      h = (2 : ℝ) ^ (-(B : ℝ)) := rfl
      _ = (2 : ℝ) ^ ((-(B : ℝ) / 2) * 2) := by ring
      _ = ((2 : ℝ) ^ (-(B : ℝ) / 2)) ^ (2 : ℝ) := by
        rw [Real.rpow_mul h_two_nonneg (-(B : ℝ) / 2) 2]
      _ = c ^ (2 : ℝ) := by rw [hc_def]
      _ = c ^ 2 := by norm_num
  -- RHS = 2 * c
  have h_rhs_eq : (2 : ℝ) ^ (1 - (B : ℝ) / 2) = 2 * c := by
    calc
      (2 : ℝ) ^ (1 - (B : ℝ) / 2) = (2 : ℝ) ^ ((1 : ℝ) + (-(B : ℝ) / 2)) := by ring
      _ = (2 : ℝ) ^ (1 : ℝ) * (2 : ℝ) ^ (-(B : ℝ) / 2) := by
        rw [Real.rpow_add h_two_pos (1 : ℝ) (-(B : ℝ) / 2)]
      _ = (2 : ℝ) * (2 : ℝ) ^ (-(B : ℝ) / 2) := by norm_num
      _ = 2 * c := by rw [hc_def]
  rw [h_rhs_eq]
  -- define f(x) = sqrt(-2 log x)
  set f := fun x : ℝ => Real.sqrt (-2 * Real.log x) with hf_def
  have hf_nonneg : ∀ x, 0 < x → x ≤ 1 → 0 ≤ f x := by
    intro x hx_pos hx_le_one
    dsimp [f]
    exact Real.sqrt_nonneg _
  have hf_sq_eq : ∀ x, 0 < x → x ≤ 1 → f x ^ 2 = -2 * Real.log x := by
    intro x hx_pos hx_le_one
    dsimp [f]
    have h_nonneg : 0 ≤ -2 * Real.log x := by
      have hlog_nonpos : Real.log x ≤ 0 := Real.log_nonpos (le_of_lt hx_pos) hx_le_one
      nlinarith
    rw [Real.sq_sqrt h_nonneg]
  -- set m = min u v
  set m := min u v with hm_def
  have hm_le_u : m ≤ u := min_le_left _ _
  have hm_le_v : m ≤ v := min_le_right _ _
  have hm_ge_c : c ≤ m := le_min hu hv
  have hm_pos : 0 < m := lt_of_lt_of_le hc_pos hm_ge_c
  have hm_nonneg : 0 ≤ m := le_of_lt hm_pos
  have hm_le_one : m ≤ 1 := le_trans hm_le_u hu1
  -- key lemma: |log u - log v| ≤ |u - v| / m
  have h_log_diff_bound : |Real.log u - Real.log v| ≤ |u - v| / m := by
    by_cases huv_le : u ≤ v
    · have h_div_pos : 0 < v / u := div_pos hpos_v hpos_u
      have h_log_le : Real.log (v / u) ≤ (v / u) - 1 := Real.log_le_sub_one_of_pos h_div_pos
      have h_eq : (v / u) - 1 = (v - u) / u := by field_simp [ne_of_gt hpos_u]
      rw [h_eq] at h_log_le
      have h_div_le : (v - u) / u ≤ (v - u) / m :=
        div_le_div_of_nonneg_left (sub_nonneg.mpr huv_le) hm_pos hm_le_u
      have h_log_diff_eq : |Real.log u - Real.log v| = Real.log (v / u) := by
        rw [abs_of_nonpos (sub_nonpos.mpr (Real.log_le_log hpos_u huv_le)),
          Real.log_div (ne_of_gt hpos_v) (ne_of_gt hpos_u)]
        ring
      have h_u_v_diff_eq : |u - v| = v - u := by
        rw [abs_of_nonpos (sub_nonpos.mpr huv_le)]
        ring
      rw [h_log_diff_eq, h_u_v_diff_eq]
      linarith
    · have h_lt : v < u := by linarith
      have h_div_pos : 0 < u / v := div_pos hpos_u hpos_v
      have h_log_le : Real.log (u / v) ≤ (u / v) - 1 := Real.log_le_sub_one_of_pos h_div_pos
      have h_eq : (u / v) - 1 = (u - v) / v := by field_simp [ne_of_gt hpos_v]
      rw [h_eq] at h_log_le
      have h_div_le : (u - v) / v ≤ (u - v) / m :=
        div_le_div_of_nonneg_left (sub_nonneg.mpr (le_of_lt h_lt)) hm_pos hm_le_v
      have h_log_diff_eq : |Real.log u - Real.log v| = Real.log (u / v) := by
        rw [abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log hpos_v (le_of_lt h_lt))),
          Real.log_div (ne_of_gt hpos_u) (ne_of_gt hpos_v)]
      have h_u_v_diff_eq : |u - v| = u - v := abs_of_nonneg (sub_nonneg.mpr (le_of_lt h_lt))
      rw [h_log_diff_eq, h_u_v_diff_eq]
      linarith
  by_cases hm_half : 1/2 ≤ m
  · -- Case 1: m ≥ 1/2
    have h_nonneg_f_u : 0 ≤ f u := hf_nonneg u hpos_u hu1
    have h_nonneg_f_v : 0 ≤ f v := hf_nonneg v hpos_v hv1
    -- identity: |f u - f v| * (f u + f v) = |(f u)^2 - (f v)^2|
    have h_id : |f u - f v| * (f u + f v) = |(f u) ^ 2 - (f v) ^ 2| := by
      rcases le_total (f u) (f v) with (hle | hle)
      · -- f u ≤ f v
        have h_abs : |f u - f v| = f v - f u := by
          rw [abs_of_nonpos (sub_nonpos.mpr hle)]
          ring
        rw [h_abs]
        have h_sq_le : (f u) ^ 2 ≤ (f v) ^ 2 := by
          have h_abs_le : |f u| ≤ |f v| := by rwa [abs_of_nonneg h_nonneg_f_u, abs_of_nonneg h_nonneg_f_v]
          exact (sq_le_sq.mpr h_abs_le)
        have h_sq_diff : (f v) ^ 2 - (f u) ^ 2 = (f v - f u) * (f u + f v) := by ring
        have h_abs_sq : |(f u) ^ 2 - (f v) ^ 2| = (f v) ^ 2 - (f u) ^ 2 := by
          rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr h_sq_le)]
        rw [← h_sq_diff, ← h_abs_sq]
      · -- f v ≤ f u
        have h_abs : |f u - f v| = f u - f v := abs_of_nonneg (sub_nonneg.mpr hle)
        rw [h_abs]
        have h_sq_le : (f v) ^ 2 ≤ (f u) ^ 2 := by
          have h_abs_le : |f v| ≤ |f u| := by rwa [abs_of_nonneg h_nonneg_f_v, abs_of_nonneg h_nonneg_f_u]
          exact (sq_le_sq.mpr h_abs_le)
        have h_sq_diff : (f u) ^ 2 - (f v) ^ 2 = (f u - f v) * (f u + f v) := by ring
        have h_abs_sq : |(f u) ^ 2 - (f v) ^ 2| = (f u) ^ 2 - (f v) ^ 2 :=
          abs_of_nonneg (sub_nonneg.mpr h_sq_le)
        rw [← h_sq_diff]
        exact h_abs_sq.symm
    -- |f u - f v| ≤ sqrt(|f u² - f v²|)
    have h_abs_diff_le_sqrt : |f u - f v| ≤ Real.sqrt (|(f u) ^ 2 - (f v) ^ 2|) := by
      have h_nonneg_abs : 0 ≤ |f u - f v| := abs_nonneg _
      have h_abs_le_sum : |f u - f v| ≤ f u + f v := by
        calc
          |f u - f v| ≤ |f u| + |f v| := abs_sub _ _
          _ = f u + f v := by rw [abs_of_nonneg h_nonneg_f_u, abs_of_nonneg h_nonneg_f_v]
      have h_sq_ineq : (|f u - f v|) ^ 2 ≤ |f u - f v| * (f u + f v) := by
        rw [pow_two]
        exact mul_le_mul_of_nonneg_left h_abs_le_sum h_nonneg_abs
      calc
        |f u - f v| = Real.sqrt ((|f u - f v|) ^ 2) := by
          rw [Real.sqrt_sq h_nonneg_abs]
        _ ≤ Real.sqrt (|f u - f v| * (f u + f v)) :=
          Real.sqrt_le_sqrt h_sq_ineq
        _ = Real.sqrt (|(f u) ^ 2 - (f v) ^ 2|) := by rw [h_id]
    -- bound |f u² - f v²|
    have h_sq_diff_bound : |(f u) ^ 2 - (f v) ^ 2| ≤ 4 * c ^ 2 := by
      calc
        |(f u) ^ 2 - (f v) ^ 2| = |(-2 * Real.log u) - (-2 * Real.log v)| := by
          rw [hf_sq_eq u hpos_u hu1, hf_sq_eq v hpos_v hv1]
        _ = |(-2 : ℝ) * (Real.log u - Real.log v)| := by ring
        _ = |(-2 : ℝ)| * |Real.log u - Real.log v| := by rw [abs_mul]
        _ = 2 * |Real.log u - Real.log v| := by norm_num
        _ ≤ 2 * (|u - v| / m) := by nlinarith
        _ = (2 * |u - v|) / m := by ring
        _ ≤ (2 * h) / m := by
          have h_abs_uv_le_h : |u - v| ≤ h := huv
          have h_mul : 2 * |u - v| ≤ 2 * h := by nlinarith
          exact div_le_div_of_nonneg_right h_mul hm_nonneg
        _ = (2 * (c ^ 2)) / m := by rw [h_sq_eq]
        _ ≤ (2 * (c ^ 2)) / (1/2) := by
          refine div_le_div_of_nonneg_left (by nlinarith) (by norm_num : 0 < (1/2 : ℝ)) hm_half
        _ = 4 * c ^ 2 := by norm_num; ring
    have h_sqrt_bound : Real.sqrt (|(f u) ^ 2 - (f v) ^ 2|) ≤ Real.sqrt (4 * c ^ 2) :=
      Real.sqrt_le_sqrt h_sq_diff_bound
    have h_sqrt_four_c_sq : Real.sqrt (4 * c ^ 2) = 2 * c := by
      rw [Real.sqrt_mul (by norm_num : 0 ≤ (4 : ℝ)), Real.sqrt_sq hc_nonneg]
      norm_num
    rw [h_sqrt_four_c_sq] at h_sqrt_bound
    linarith
  · -- Case 2: m < 1/2
    have hm_lt_half : m < 1/2 := by linarith
    have h_one_lt_half : u < 1/2 ∨ v < 1/2 := by
      by_contra! h
      rcases h with ⟨hu_half, hv_half⟩
      have hm_half' : 1/2 ≤ m := le_min hu_half hv_half
      linarith
    have h_f_sum_ge_one : 1 ≤ f u + f v := by
      rcases h_one_lt_half with (hu_lt_half | hv_lt_half)
      · -- u < 1/2, so f u ≥ sqrt(2 * log 2) ≥ 1
        have h_fu_ge_one : 1 ≤ f u := by
          have hlog_u_lt : Real.log u < Real.log (1/2) := Real.log_lt_log hpos_u hu_lt_half
          have hlog_half : Real.log (1/2) = -Real.log 2 := by
            rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]
            simp
          rw [hlog_half] at hlog_u_lt
          have h_neg2log_u_gt : -2 * Real.log u > 2 * Real.log 2 := by linarith
          have h_f_u_sq_gt : (f u) ^ 2 > 2 * Real.log 2 := by
            rw [hf_sq_eq u hpos_u hu1]
            linarith
          have h_one_lt_2log2 : 1 < 2 * Real.log 2 := by
            have h_log_two_gt : 0.6931471803 < Real.log 2 := Real.log_two_gt_d9
            linarith
          have h_nonneg_fu : 0 ≤ f u := hf_nonneg u hpos_u hu1
          nlinarith
        have h_fv_nonneg : 0 ≤ f v := hf_nonneg v hpos_v hv1
        linarith
      · -- v < 1/2, symmetric
        have h_fv_ge_one : 1 ≤ f v := by
          have hlog_v_lt : Real.log v < Real.log (1/2) := Real.log_lt_log hpos_v hv_lt_half
          have hlog_half : Real.log (1/2) = -Real.log 2 := by
            rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]
            simp
          rw [hlog_half] at hlog_v_lt
          have h_neg2log_v_gt : -2 * Real.log v > 2 * Real.log 2 := by linarith
          have h_f_v_sq_gt : (f v) ^ 2 > 2 * Real.log 2 := by
            rw [hf_sq_eq v hpos_v hv1]
            linarith
          have h_one_lt_2log2 : 1 < 2 * Real.log 2 := by
            have h_log_two_gt : 0.6931471803 < Real.log 2 := Real.log_two_gt_d9
            linarith
          have h_nonneg_fv : 0 ≤ f v := hf_nonneg v hpos_v hv1
          nlinarith
        have h_fu_nonneg : 0 ≤ f u := hf_nonneg u hpos_u hu1
        linarith
    -- identity: |f u - f v| = |f u² - f v²| / (f u + f v)
    have h_nonneg_f_u : 0 ≤ f u := hf_nonneg u hpos_u hu1
    have h_nonneg_f_v : 0 ≤ f v := hf_nonneg v hpos_v hv1
    have h_sum_pos : 0 < f u + f v := by linarith
    have h_abs_diff_eq : |f u - f v| = |(f u) ^ 2 - (f v) ^ 2| / (f u + f v) := by
      rcases le_total (f u) (f v) with (hle | hle)
      · -- f u ≤ f v
        have h_abs_sub : |f u - f v| = f v - f u := by
          rw [abs_of_nonpos (sub_nonpos.mpr hle)]
          ring
        have h_sq_diff : (f v) ^ 2 - (f u) ^ 2 = (f v - f u) * (f u + f v) := by ring
        have h_sq_diff_abs : |(f u) ^ 2 - (f v) ^ 2| = (f v) ^ 2 - (f u) ^ 2 := by
          have h_sq_le : (f u) ^ 2 ≤ (f v) ^ 2 := by
            have h_abs_le : |f u| ≤ |f v| := by
              rwa [abs_of_nonneg h_nonneg_f_u, abs_of_nonneg h_nonneg_f_v]
            exact (sq_le_sq.mpr h_abs_le)
          rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr h_sq_le)]
        rw [h_abs_sub, h_sq_diff_abs, h_sq_diff]
        field_simp [h_sum_pos.ne.symm]
      · -- f v ≤ f u
        have h_abs_sub : |f u - f v| = f u - f v := abs_of_nonneg (sub_nonneg.mpr hle)
        have h_sq_diff : (f u) ^ 2 - (f v) ^ 2 = (f u - f v) * (f u + f v) := by ring
        have h_sq_diff_abs : |(f u) ^ 2 - (f v) ^ 2| = (f u) ^ 2 - (f v) ^ 2 :=
          abs_of_nonneg (sub_nonneg.mpr (by
            have h_abs_le : |f v| ≤ |f u| := by
              rwa [abs_of_nonneg h_nonneg_f_v, abs_of_nonneg h_nonneg_f_u]
            exact (sq_le_sq.mpr h_abs_le)))
        rw [h_abs_sub, h_sq_diff_abs, h_sq_diff]
        field_simp [h_sum_pos.ne.symm]
    -- bound |f u² - f v²|
    have h_sq_diff_bound : |(f u) ^ 2 - (f v) ^ 2| ≤ 2 * h / m := by
      calc
        |(f u) ^ 2 - (f v) ^ 2| = |(-2 * Real.log u) - (-2 * Real.log v)| := by
          rw [hf_sq_eq u hpos_u hu1, hf_sq_eq v hpos_v hv1]
        _ = |(-2 : ℝ) * (Real.log u - Real.log v)| := by ring
        _ = |(-2 : ℝ)| * |Real.log u - Real.log v| := by rw [abs_mul]
        _ = 2 * |Real.log u - Real.log v| := by norm_num
        _ ≤ 2 * (|u - v| / m) := by nlinarith
        _ = (2 * |u - v|) / m := by ring
        _ ≤ (2 * h) / m := by
          have h_abs_uv_le_h : |u - v| ≤ h := huv
          have h_mul : 2 * |u - v| ≤ 2 * h := by nlinarith
          exact div_le_div_of_nonneg_right h_mul hm_nonneg
        _ = 2 * h / m := by ring
    -- combine
    rw [h_abs_diff_eq]
    have h_nonneg_2h_div_m : 0 ≤ 2 * h / m := by
      refine div_nonneg (by nlinarith) hm_nonneg
    calc
      |(f u) ^ 2 - (f v) ^ 2| / (f u + f v) ≤ (2 * h / m) / (f u + f v) :=
        div_le_div_of_nonneg_right h_sq_diff_bound (by linarith)
      _ ≤ (2 * h / m) / 1 := by
        refine div_le_div_of_nonneg_left h_nonneg_2h_div_m (by norm_num : 0 < (1 : ℝ)) h_f_sum_ge_one
      _ = 2 * h / m := by norm_num
      _ = 2 * (c ^ 2) / m := by rw [h_sq_eq]
      _ ≤ 2 * (c ^ 2) / c := by
        refine div_le_div_of_nonneg_left (by nlinarith) hc_pos hm_ge_c
      _ = 2 * c := by
        field_simp [hc_pos.ne.symm]

end AdversarialBco.Bit.Aux_boxMuller_radius

namespace AdversarialBco.Bit.Aux_boxMuller_path


open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

theorem _root_.AdversarialBco.Bit.boxMuller_path (B : ℕ) (u u' w w' : ℝ) (hu : (2 : ℝ) ^ (-(B : ℝ) / 2) ≤ u)
    (hu' : (2 : ℝ) ^ (-(B : ℝ) / 2) ≤ u') (hu1 : u ≤ 1) (hu1' : u' ≤ 1) (huu : |u - u'| ≤ (2 : ℝ) ^ (-(B : ℝ)))
    (hww : |w - w'| ≤ (2 : ℝ) ^ (-(B : ℝ))) :
    |Real.sqrt (-2 * Real.log u) * Real.cos (2 * Real.pi * w) - Real.sqrt (-2 * Real.log u') * Real.cos (2 * Real.pi * w')| ≤
        (2 : ℝ) ^ (1 - (B : ℝ) / 2) + 2 * Real.pi * Real.sqrt B * (2 : ℝ) ^ (-(B : ℝ)) ∧
      |Real.sqrt (-2 * Real.log u) * Real.sin (2 * Real.pi * w) - Real.sqrt (-2 * Real.log u') * Real.sin (2 * Real.pi * w')| ≤
        (2 : ℝ) ^ (1 - (B : ℝ) / 2) + 2 * Real.pi * Real.sqrt B * (2 : ℝ) ^ (-(B : ℝ)) := by
  have hpos2 : 0 < (2 : ℝ) ^ (-(B : ℝ) / 2) := by positivity
  have hu_pos : 0 < u := by linarith
  have hu'_pos : 0 < u' := by linarith
  have hB_nonneg : 0 ≤ (B : ℝ) := Nat.cast_nonneg _
  set R := Real.sqrt (-2 * Real.log u) with hR
  set R' := Real.sqrt (-2 * Real.log u') with hR'
  set C := Real.cos (2 * Real.pi * w) with hC
  set C' := Real.cos (2 * Real.pi * w') with hC'
  have hC_abs : |C| ≤ 1 := Real.abs_cos_le_one _
  have hR'_nonneg : 0 ≤ R' := Real.sqrt_nonneg _
  have hR'_abs : |R'| = R' := abs_of_nonneg hR'_nonneg
  have hR_sub : |R - R'| ≤ (2 : ℝ) ^ (1 - (B : ℝ) / 2) := by
    dsimp [R, R']
    exact AdversarialBco.Bit.boxMuller_radius B u u' hu hu' hu1 hu1' huu
  have hC_sub : |C - C'| ≤ 2 * Real.pi * (2 : ℝ) ^ (-(B : ℝ)) := by
    dsimp [C, C']
    calc
      |Real.cos (2 * Real.pi * w) - Real.cos (2 * Real.pi * w')| ≤ |(2 * Real.pi * w) - (2 * Real.pi * w')| :=
        Real.abs_cos_sub_cos_le _ _
      _ = |2 * Real.pi * (w - w')| := by ring_nf
      _ = |2 * Real.pi| * |w - w'| := by rw [abs_mul]
      _ = (2 * Real.pi) * |w - w'| := by rw [abs_of_pos (by positivity : 0 < 2 * Real.pi)]
      _ ≤ (2 * Real.pi) * (2 : ℝ) ^ (-(B : ℝ)) := by
        apply mul_le_mul_of_nonneg_left hww
        positivity
  have hR'_le_sqrtB : R' ≤ Real.sqrt (B : ℝ) := by
    dsimp [R']
    refine Real.sqrt_le_sqrt ?_
    have hlog : Real.log ((2 : ℝ) ^ (-(B : ℝ) / 2)) ≤ Real.log u' :=
      Real.log_le_log (by positivity) hu'
    have hlog2 : Real.log ((2 : ℝ) ^ (-(B : ℝ) / 2)) = (-(B : ℝ) / 2) * Real.log (2 : ℝ) := by
      rw [Real.log_rpow (by norm_num : 0 < (2 : ℝ))]
    rw [hlog2] at hlog
    have h_log2_le_one : Real.log (2 : ℝ) ≤ 1 := by
      rw [Real.log_le_iff_le_exp (by norm_num : 0 < (2 : ℝ))]
      linarith [Real.exp_one_gt_two]
    nlinarith
  have h_main_cos : |R * C - R' * C'| ≤ (2 : ℝ) ^ (1 - (B : ℝ) / 2) + 2 * Real.pi * Real.sqrt (B : ℝ) * (2 : ℝ) ^ (-(B : ℝ)) := by
    have h1 : |R * C - R' * C'| = |(R - R') * C + R' * (C - C')| := by ring_nf
    rw [h1]
    calc
      |(R - R') * C + R' * (C - C')| ≤ |(R - R') * C| + |R' * (C - C')| := abs_add_le _ _
      _ = |R - R'| * |C| + |R'| * |C - C'| := by rw [abs_mul, abs_mul]
      _ ≤ (2 : ℝ) ^ (1 - (B : ℝ) / 2) * 1 + R' * (2 * Real.pi * (2 : ℝ) ^ (-(B : ℝ))) := by
        rw [hR'_abs]
        have hterm1 : |R - R'| * |C| ≤ (2 : ℝ) ^ (1 - (B : ℝ) / 2) * 1 := by
          apply mul_le_mul hR_sub hC_abs (abs_nonneg _) (by positivity)
        have hterm2 : R' * |C - C'| ≤ R' * (2 * Real.pi * (2 : ℝ) ^ (-(B : ℝ))) := by
          apply mul_le_mul_of_nonneg_left hC_sub hR'_nonneg
        nlinarith
      _ = (2 : ℝ) ^ (1 - (B : ℝ) / 2) + 2 * Real.pi * R' * (2 : ℝ) ^ (-(B : ℝ)) := by ring
      _ ≤ (2 : ℝ) ^ (1 - (B : ℝ) / 2) + 2 * Real.pi * Real.sqrt (B : ℝ) * (2 : ℝ) ^ (-(B : ℝ)) := by
        gcongr
  set S := Real.sin (2 * Real.pi * w) with hS
  set S' := Real.sin (2 * Real.pi * w') with hS'
  have hS_abs : |S| ≤ 1 := Real.abs_sin_le_one _
  have hS_sub : |S - S'| ≤ 2 * Real.pi * (2 : ℝ) ^ (-(B : ℝ)) := by
    dsimp [S, S']
    calc
      |Real.sin (2 * Real.pi * w) - Real.sin (2 * Real.pi * w')| ≤ |(2 * Real.pi * w) - (2 * Real.pi * w')| :=
        Real.abs_sin_sub_sin_le _ _
      _ = |2 * Real.pi * (w - w')| := by ring_nf
      _ = |2 * Real.pi| * |w - w'| := by rw [abs_mul]
      _ = (2 * Real.pi) * |w - w'| := by rw [abs_of_pos (by positivity : 0 < 2 * Real.pi)]
      _ ≤ (2 * Real.pi) * (2 : ℝ) ^ (-(B : ℝ)) := by
        apply mul_le_mul_of_nonneg_left hww
        positivity
  have h_main_sin : |R * S - R' * S'| ≤ (2 : ℝ) ^ (1 - (B : ℝ) / 2) + 2 * Real.pi * Real.sqrt (B : ℝ) * (2 : ℝ) ^ (-(B : ℝ)) := by
    have h1 : |R * S - R' * S'| = |(R - R') * S + R' * (S - S')| := by ring_nf
    rw [h1]
    calc
      |(R - R') * S + R' * (S - S')| ≤ |(R - R') * S| + |R' * (S - S')| := abs_add_le _ _
      _ = |R - R'| * |S| + |R'| * |S - S'| := by rw [abs_mul, abs_mul]
      _ ≤ (2 : ℝ) ^ (1 - (B : ℝ) / 2) * 1 + R' * (2 * Real.pi * (2 : ℝ) ^ (-(B : ℝ))) := by
        rw [hR'_abs]
        have hterm1 : |R - R'| * |S| ≤ (2 : ℝ) ^ (1 - (B : ℝ) / 2) * 1 := by
          apply mul_le_mul hR_sub hS_abs (abs_nonneg _) (by positivity)
        have hterm2 : R' * |S - S'| ≤ R' * (2 * Real.pi * (2 : ℝ) ^ (-(B : ℝ))) := by
          apply mul_le_mul_of_nonneg_left hS_sub hR'_nonneg
        nlinarith
      _ = (2 : ℝ) ^ (1 - (B : ℝ) / 2) + 2 * Real.pi * R' * (2 : ℝ) ^ (-(B : ℝ)) := by ring
      _ ≤ (2 : ℝ) ^ (1 - (B : ℝ) / 2) + 2 * Real.pi * Real.sqrt (B : ℝ) * (2 : ℝ) ^ (-(B : ℝ)) := by
        gcongr
  exact And.intro h_main_cos h_main_sin

end AdversarialBco.Bit.Aux_boxMuller_path

namespace AdversarialBco.Bit.Aux_boxMuller_coupling


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius

theorem _root_.AdversarialBco.Bit.boxMuller_coupling (B : ℕ) :
    ((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod (volume.restrict (Set.Ioc (0 : ℝ) 1)))
        {p : ℝ × ℝ | (2 : ℝ) ^ (1 - (B : ℝ) / 2) + 2 * Real.pi * Real.sqrt B * (2 : ℝ) ^ (-(B : ℝ)) <
          |Real.sqrt (-2 * Real.log p.1) * Real.cos (2 * Real.pi * p.2) -
            Real.sqrt (-2 * Real.log ((⌈(2 : ℝ) ^ B * p.1⌉ : ℝ) / 2 ^ B)) *
              Real.cos (2 * Real.pi * ((⌈(2 : ℝ) ^ B * p.2⌉ : ℝ) / 2 ^ B))|} ≤
      ENNReal.ofReal ((2 : ℝ) ^ (-(B : ℝ) / 2)) := by
  set c := (2 : ℝ) ^ (-(B : ℝ) / 2) with hc
  set K := (2 : ℝ) ^ (1 - (B : ℝ) / 2) + 2 * Real.pi * Real.sqrt B * (2 : ℝ) ^ (-(B : ℝ)) with hK
  set ν := ((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod (volume.restrict (Set.Ioc (0 : ℝ) 1))) with hν
  set Bad := {p : ℝ × ℝ | K < |Real.sqrt (-2 * Real.log p.1) * Real.cos (2 * Real.pi * p.2) -
    Real.sqrt (-2 * Real.log ((⌈(2 : ℝ) ^ B * p.1⌉ : ℝ) / 2 ^ B)) *
      Real.cos (2 * Real.pi * ((⌈(2 : ℝ) ^ B * p.2⌉ : ℝ) / 2 ^ B))|} with hBad
  have hc_pos : 0 < c := by
    rw [hc]
    exact Real.rpow_pos_of_pos (by norm_num : 0 < (2 : ℝ)) _
  have hc_le_one : c ≤ 1 := by
    rw [hc]
    have h_exp : -(B : ℝ) / 2 ≤ (0 : ℝ) := by
      have hB : 0 ≤ (B : ℝ) := Nat.cast_nonneg _
      linarith
    have htemp := Real.rpow_le_rpow_of_exponent_le (by norm_num : 1 ≤ (2 : ℝ)) h_exp
    simpa [Real.rpow_zero] using htemp
  have h_sub : Bad ⊆ (Set.Iio c ×ˢ Set.univ) ∪ ((Set.Ioc (0 : ℝ) 1 ×ˢ Set.Ioc (0 : ℝ) 1)ᶜ) := by
    intro p hp
    have hp' : K < |Real.sqrt (-2 * Real.log p.1) * Real.cos (2 * Real.pi * p.2) -
      Real.sqrt (-2 * Real.log ((⌈(2 : ℝ) ^ B * p.1⌉ : ℝ) / 2 ^ B)) *
        Real.cos (2 * Real.pi * ((⌈(2 : ℝ) ^ B * p.2⌉ : ℝ) / 2 ^ B))| := by
      simpa [hBad] using hp
    by_cases h1 : p.1 ∈ Set.Ioc (0 : ℝ) 1
    · rcases h1 with ⟨h1l, h1r⟩
      by_cases h2 : p.2 ∈ Set.Ioc (0 : ℝ) 1
      · rcases h2 with ⟨h2l, h2r⟩
        by_cases hc_le : c ≤ p.1
        · set u := p.1 with hu
          set u' := ((⌈(2 : ℝ) ^ B * p.1⌉ : ℝ) / 2 ^ B) with hu'
          set w := p.2 with hw
          set w' := ((⌈(2 : ℝ) ^ B * p.2⌉ : ℝ) / 2 ^ B) with hw'
          have h_dyadic_u := AdversarialBco.Bit.dyadic_ceil B u (by linarith) (by linarith)
          rcases h_dyadic_u with ⟨hu'_ge_one, hu'_le_twoB, hu_le_u', hu'_sub_u⟩
          have hu'_le_one : u' ≤ 1 := by
            rw [hu']
            have hpos : 0 < (2 : ℝ) ^ B := by positivity
            apply (div_le_one hpos).mpr
            exact_mod_cast hu'_le_twoB
          have hu'_ge_c : c ≤ u' := by
            rw [hu']
            calc
              c ≤ u := hc_le
              _ ≤ (⌈(2 : ℝ) ^ B * u⌉ : ℝ) / (2 : ℝ) ^ B := hu_le_u'
          have hu_nonpos : u - u' ≤ 0 := by linarith
          have huu : |u - u'| ≤ (2 : ℝ) ^ (-(B : ℝ)) := by
            rw [abs_of_nonpos hu_nonpos]
            linarith
          have h_dyadic_w := AdversarialBco.Bit.dyadic_ceil B w (by linarith) (by linarith)
          rcases h_dyadic_w with ⟨hw'_ge_one, hw'_le_twoB, hw_le_w', hw'_sub_w⟩
          have hw_nonpos : w - w' ≤ 0 := by linarith
          have hww : |w - w'| ≤ (2 : ℝ) ^ (-(B : ℝ)) := by
            rw [abs_of_nonpos hw_nonpos]
            linarith
          have h_box := AdversarialBco.Bit.boxMuller_path B u u' w w' hc_le hu'_ge_c h1r hu'_le_one huu hww
          rcases h_box with ⟨h_box_cos, _⟩
          linarith
        · apply Set.mem_union_left
          exact Set.mem_prod.mpr ⟨Set.mem_Iio.mpr (by linarith), Set.mem_univ _⟩
      · apply Set.mem_union_right
        refine Set.mem_compl ?_
        intro h
        apply h2
        exact h.2
    · apply Set.mem_union_right
      refine Set.mem_compl ?_
      intro h
      apply h1
      exact h.1
  have h_meas_rect : MeasurableSet (Set.Ioc (0 : ℝ) 1 ×ˢ Set.Ioc (0 : ℝ) 1) :=
    measurableSet_Ioc.prod measurableSet_Ioc
  have h_restrict_univ_val : (volume.restrict (Set.Ioc (0 : ℝ) 1)) Set.univ = 1 := by
    rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ]
    simp [Real.volume_Ioc]
  have h_restrict_Ioc_val : (volume.restrict (Set.Ioc (0 : ℝ) 1)) (Set.Ioc (0 : ℝ) 1) = 1 := by
    rw [MeasureTheory.Measure.restrict_apply measurableSet_Ioc]
    simp [Real.volume_Ioc]
  have h_univ : ν Set.univ = 1 := by
    rw [hν, ← Set.univ_prod_univ, MeasureTheory.Measure.prod_prod]
    rw [h_restrict_univ_val]
    simp
  have h_rect : ν (Set.Ioc (0 : ℝ) 1 ×ˢ Set.Ioc (0 : ℝ) 1) = 1 := by
    rw [hν, MeasureTheory.Measure.prod_prod]
    rw [h_restrict_Ioc_val]
    simp
  have h_compl : ν ((Set.Ioc (0 : ℝ) 1 ×ˢ Set.Ioc (0 : ℝ) 1)ᶜ) = 0 := by
    have h_fin_rect : ν (Set.Ioc (0 : ℝ) 1 ×ˢ Set.Ioc (0 : ℝ) 1) ≠ ⊤ := by
      rw [h_rect]
      exact ENNReal.one_ne_top
    rw [MeasureTheory.measure_compl h_meas_rect h_fin_rect]
    rw [h_univ, h_rect]
    simp
  have h_restrict_io_val : (volume.restrict (Set.Ioc (0 : ℝ) 1)) (Set.Iio c) = ENNReal.ofReal c := by
    rw [MeasureTheory.Measure.restrict_apply measurableSet_Iio]
    rw [Set.inter_comm]
    rw [hc]
    exact AdversarialBco.Bit.tail_volume B
  have h_io_c : ν (Set.Iio c ×ˢ Set.univ) = ENNReal.ofReal c := by
    rw [hν, MeasureTheory.Measure.prod_prod, h_restrict_io_val, h_restrict_univ_val]
    simp
  calc
    ν Bad ≤ ν ((Set.Iio c ×ˢ Set.univ) ∪ ((Set.Ioc (0 : ℝ) 1 ×ˢ Set.Ioc (0 : ℝ) 1)ᶜ)) :=
      MeasureTheory.measure_mono h_sub
    _ ≤ ν (Set.Iio c ×ˢ Set.univ) + ν ((Set.Ioc (0 : ℝ) 1 ×ˢ Set.Ioc (0 : ℝ) 1)ᶜ) :=
      MeasureTheory.measure_union_le _ _
    _ = ENNReal.ofReal c + ν ((Set.Ioc (0 : ℝ) 1 ×ˢ Set.Ioc (0 : ℝ) 1)ᶜ) := by rw [h_io_c]
    _ ≤ ENNReal.ofReal c + 0 := by rw [h_compl]
    _ = ENNReal.ofReal c := by simp

end AdversarialBco.Bit.Aux_boxMuller_coupling

namespace AdversarialBco.Bit.Aux_boxMuller_pair


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius

theorem _root_.AdversarialBco.Bit.boxMuller_pair (B : ℕ) :
    ((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod (volume.restrict (Set.Ioc (0 : ℝ) 1)))
        {p : ℝ × ℝ | (2 : ℝ) ^ (1 - (B : ℝ) / 2) + 2 * Real.pi * Real.sqrt B * (2 : ℝ) ^ (-(B : ℝ)) <
          |Real.sqrt (-2 * Real.log p.1) * Real.cos (2 * Real.pi * p.2) -
            Real.sqrt (-2 * Real.log ((⌈(2 : ℝ) ^ B * p.1⌉ : ℝ) / 2 ^ B)) *
              Real.cos (2 * Real.pi * ((⌈(2 : ℝ) ^ B * p.2⌉ : ℝ) / 2 ^ B))| ∨
          (2 : ℝ) ^ (1 - (B : ℝ) / 2) + 2 * Real.pi * Real.sqrt B * (2 : ℝ) ^ (-(B : ℝ)) <
          |Real.sqrt (-2 * Real.log p.1) * Real.sin (2 * Real.pi * p.2) -
            Real.sqrt (-2 * Real.log ((⌈(2 : ℝ) ^ B * p.1⌉ : ℝ) / 2 ^ B)) *
              Real.sin (2 * Real.pi * ((⌈(2 : ℝ) ^ B * p.2⌉ : ℝ) / 2 ^ B))|} ≤
      ENNReal.ofReal ((2 : ℝ) ^ (-(B : ℝ) / 2)) := by
  set c := (2 : ℝ) ^ (-(B : ℝ) / 2) with hc
  set K := (2 : ℝ) ^ (1 - (B : ℝ) / 2) + 2 * Real.pi * Real.sqrt B * (2 : ℝ) ^ (-(B : ℝ)) with hK
  set I := Set.Ioc (0 : ℝ) 1 with hI
  set ν := (volume.restrict I).prod (volume.restrict I) with hν
  set S := {p : ℝ × ℝ | K < |Real.sqrt (-2 * Real.log p.1) * Real.cos (2 * Real.pi * p.2) -
    Real.sqrt (-2 * Real.log ((⌈(2 : ℝ) ^ B * p.1⌉ : ℝ) / 2 ^ B)) *
      Real.cos (2 * Real.pi * ((⌈(2 : ℝ) ^ B * p.2⌉ : ℝ) / 2 ^ B))| ∨
    K < |Real.sqrt (-2 * Real.log p.1) * Real.sin (2 * Real.pi * p.2) -
    Real.sqrt (-2 * Real.log ((⌈(2 : ℝ) ^ B * p.1⌉ : ℝ) / 2 ^ B)) *
      Real.sin (2 * Real.pi * ((⌈(2 : ℝ) ^ B * p.2⌉ : ℝ) / 2 ^ B))|} with hS
  have hc_nonneg : 0 ≤ c := by
    rw [hc]
    apply Real.rpow_nonneg
    norm_num
  have hc_le_one : c ≤ 1 := by
    rw [hc]
    have h_exp : -(B : ℝ) / 2 ≤ (0 : ℝ) := by
      have hB : (0 : ℝ) ≤ B := by exact mod_cast Nat.zero_le B
      nlinarith
    have h2 : (1 : ℝ) ≤ (2 : ℝ) := by norm_num
    have h_rpow := Real.rpow_le_rpow_of_exponent_le h2 h_exp
    -- h_rpow : 2^(-B/2) ≤ 2^0
    simpa [Real.rpow_zero (2 : ℝ)] using h_rpow
  have h_good : ∀ (p : ℝ × ℝ), p ∈ I ×ˢ I → c ≤ p.1 → p ∉ S := by
    intro p hp hc_le
    rcases hp with ⟨hp1, hp2⟩
    have hp1l : 0 < p.1 := hp1.1
    have hp1u : p.1 ≤ 1 := hp1.2
    have hp2l : 0 < p.2 := hp2.1
    have hp2u : p.2 ≤ 1 := hp2.2
    set u := p.1 with hu
    set v := p.2 with hv
    set u' := (⌈(2 : ℝ) ^ B * u⌉ : ℝ) / (2 : ℝ) ^ B with hu'
    set v' := (⌈(2 : ℝ) ^ B * v⌉ : ℝ) / (2 : ℝ) ^ B with hv'
    have h_dyadic_u := dyadic_ceil B u hp1l hp1u
    have h_dyadic_v := dyadic_ceil B v hp2l hp2u
    rcases h_dyadic_u with ⟨h_u_ceil_ge_one, h_u_ceil_le_two_pow, h_u_le_u', h_u'_sub_u_lt⟩
    rcases h_dyadic_v with ⟨h_v_ceil_ge_one, h_v_ceil_le_two_pow, h_v_le_v', h_v'_sub_v_lt⟩
    have hu'_le_one : u' ≤ 1 := by
      rw [hu']
      have h_ceil_le : (⌈(2 : ℝ) ^ B * u⌉ : ℝ) ≤ (2 : ℝ) ^ B := by
        exact mod_cast h_u_ceil_le_two_pow
      have h_pos : 0 < (2 : ℝ) ^ B := by positivity
      calc
        (⌈(2 : ℝ) ^ B * u⌉ : ℝ) / (2 : ℝ) ^ B ≤ (2 : ℝ) ^ B / (2 : ℝ) ^ B := by
          refine (div_le_div_of_nonneg_right h_ceil_le (by positivity : 0 ≤ (2 : ℝ) ^ B))
        _ = 1 := by field_simp [h_pos.ne']
    have hu'_sub_u_le : |u - u'| ≤ (2 : ℝ) ^ (-(B : ℝ)) := by
      have h_nonpos : u - u' ≤ 0 := by
        have : u ≤ u' := h_u_le_u'
        linarith
      rw [abs_of_nonpos h_nonpos]
      -- |u - u'| = -(u - u') = u' - u
      -- we know u' - u < 2^(-B)
      have : u' - u < (2 : ℝ) ^ (-(B : ℝ)) := h_u'_sub_u_lt
      linarith
    have hv'_sub_v_le : |v - v'| ≤ (2 : ℝ) ^ (-(B : ℝ)) := by
      have h_nonpos : v - v' ≤ 0 := by
        have : v ≤ v' := h_v_le_v'
        linarith
      rw [abs_of_nonpos h_nonpos]
      have : v' - v < (2 : ℝ) ^ (-(B : ℝ)) := h_v'_sub_v_lt
      linarith
    have hc_le_u' : c ≤ u' := by
      have h_u_le_u' : u ≤ u' := h_u_le_u'
      linarith
    have h_box := boxMuller_path B u u' v v' hc_le hc_le_u' hp1u hu'_le_one hu'_sub_u_le hv'_sub_v_le
    rcases h_box with ⟨h_cos, h_sin⟩
    intro hpS
    rw [hS] at hpS
    simp only [Set.mem_ofPred_eq] at hpS
    rcases hpS with (h | h)
    · linarith
    · linarith
  have h_cover : S ⊆ (I ×ˢ I)ᶜ ∪ {p : ℝ × ℝ | p.1 < c} := by
    intro p hpS
    by_cases hp_mem_prod : p ∈ I ×ˢ I
    · by_cases hp1_lt_c : p.1 < c
      · apply Set.mem_union_right
        exact hp1_lt_c
      · have hp1_ge_c : c ≤ p.1 := by linarith
        have hp_not_S := h_good p hp_mem_prod hp1_ge_c
        exact absurd hpS hp_not_S
    · apply Set.mem_union_left
      rw [Set.mem_compl_iff]
      exact hp_mem_prod
  have h_meas_I : MeasurableSet I := measurableSet_Ioc
  have h_meas_prod : MeasurableSet (I ×ˢ I) := h_meas_I.prod h_meas_I
  have h_meas_prod_compl : MeasurableSet ((I ×ˢ I)ᶜ) := h_meas_prod.compl
  have h_meas_setOf : MeasurableSet {p : ℝ × ℝ | p.1 < c} :=
    measurable_fst measurableSet_Iio
  have h_measure_compl : ν ((I ×ˢ I)ᶜ) = 0 := by
    rw [hν, MeasureTheory.Measure.prod_restrict]
    rw [MeasureTheory.Measure.restrict_apply h_meas_prod_compl]
    simp
  have h_measure_lt : ν {p : ℝ × ℝ | p.1 < c} = ENNReal.ofReal c := by
    rw [hν, MeasureTheory.Measure.prod_restrict]
    rw [MeasureTheory.Measure.restrict_apply h_meas_setOf]
    -- ((vol.prod vol) ({p | p.1 < c} ∩ (I ×ˢ I)))
    have h_inter : {p : ℝ × ℝ | p.1 < c} ∩ (I ×ˢ I) = (I ∩ Set.Iio c) ×ˢ I := by
      ext ⟨x, y⟩
      simp [I, Set.mem_prod, Set.mem_Ioc, Set.mem_Iio, and_comm, and_assoc, and_left_comm]
    rw [h_inter]
    rw [MeasureTheory.Measure.prod_prod (μ := volume) (ν := volume) (s := I ∩ Set.Iio c) (t := I)]
    have h_vol_I : volume I = ENNReal.ofReal 1 := by
      rw [hI, Real.volume_Ioc]
      simp
    have h_vol_inter : volume (I ∩ Set.Iio c) = ENNReal.ofReal c := by
      rw [hI]
      have h_eq : Set.Ioc (0 : ℝ) 1 ∩ Set.Iio c = Set.Ioc (0 : ℝ) c \ {c} := by
        ext x
        constructor
        · rintro ⟨⟨hx0, hx1⟩, hx_mem⟩
          have hx_lt_c : x < c := Set.mem_Iio.mp hx_mem
          refine ⟨⟨hx0, hx_lt_c.le⟩, ?_⟩
          intro hx_eq_c
          have hx_eq_c' : x = c := hx_eq_c
          rw [hx_eq_c'] at hx_lt_c
          linarith
        · rintro ⟨⟨hx0, hx_le_c⟩, hx_not_eq_c⟩
          have hx_lt_c : x < c := hx_le_c.lt_of_ne hx_not_eq_c
          have hx1 : x ≤ 1 := by linarith
          exact ⟨⟨hx0, hx1⟩, hx_lt_c⟩
      rw [h_eq, measure_sdiff_null (by simp), Real.volume_Ioc]
      simp
    rw [h_vol_inter, h_vol_I]
    simp
  calc
    ν S ≤ ν ((I ×ˢ I)ᶜ ∪ {p : ℝ × ℝ | p.1 < c}) := MeasureTheory.measure_mono h_cover
    _ ≤ ν ((I ×ˢ I)ᶜ) + ν {p : ℝ × ℝ | p.1 < c} := MeasureTheory.measure_union_le _ _
    _ = 0 + ENNReal.ofReal c := by rw [h_measure_compl, h_measure_lt]
    _ = ENNReal.ofReal c := by simp

end AdversarialBco.Bit.Aux_boxMuller_pair

namespace AdversarialBco.Bit.Aux_gauss_prod_density


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius

theorem _root_.AdversarialBco.Bit.gauss_prod_density :
    (gaussianReal 0 1).prod (gaussianReal 0 1) =
      volume.withDensity (fun p : ℝ × ℝ => ENNReal.ofReal (Real.exp (-(p.1 ^ 2 + p.2 ^ 2) / 2) / (2 * Real.pi))) := by
  have h1 : (1 : ℝ≥0) ≠ 0 := by norm_num
  have hgauss := gaussianReal_of_var_ne_zero 0 h1
  calc
    (gaussianReal 0 1).prod (gaussianReal 0 1)
        = (volume.withDensity (gaussianPDF 0 1)).prod (volume.withDensity (gaussianPDF 0 1)) := by
      simp [hgauss]
    _ = (volume.prod volume).withDensity (fun z => gaussianPDF 0 1 z.1 * gaussianPDF 0 1 z.2) := by
      rw [MeasureTheory.prod_withDensity (measurable_gaussianPDF 0 1) (measurable_gaussianPDF 0 1)]
    _ = volume.withDensity (fun z => gaussianPDF 0 1 z.1 * gaussianPDF 0 1 z.2) := by
      rw [MeasureTheory.Measure.volume_eq_prod ℝ ℝ]
    _ = volume.withDensity (fun p : ℝ × ℝ => ENNReal.ofReal (Real.exp (-(p.1 ^ 2 + p.2 ^ 2) / 2) / (2 * Real.pi))) := by
      refine congrArg (fun f => volume.withDensity f) ?_
      ext ⟨x, y⟩
      simp only [gaussianPDF, gaussianPDFReal, NNReal.coe_one, sub_zero, mul_one]
      have hx : 0 ≤ (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(x ^ 2) / 2) := by positivity
      have hprod : ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(x ^ 2) / 2)) * ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(y ^ 2) / 2)) =
          Real.exp (-(x ^ 2 + y ^ 2) / 2) / (2 * Real.pi) := by
        have hpos : 0 ≤ 2 * Real.pi := by positivity
        have hsq : ((Real.sqrt (2 * Real.pi))⁻¹) ^ 2 = (2 * Real.pi)⁻¹ := by
          calc
            ((Real.sqrt (2 * Real.pi))⁻¹) ^ 2 = ((Real.sqrt (2 * Real.pi)) ^ 2)⁻¹ := by rw [inv_pow]
            _ = (2 * Real.pi)⁻¹ := by rw [Real.sq_sqrt hpos]
        calc
          ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(x ^ 2) / 2)) * ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(y ^ 2) / 2))
              = ((Real.sqrt (2 * Real.pi))⁻¹) ^ 2 * (Real.exp (-(x ^ 2) / 2) * Real.exp (-(y ^ 2) / 2)) := by ring
          _ = (2 * Real.pi)⁻¹ * (Real.exp (-(x ^ 2) / 2) * Real.exp (-(y ^ 2) / 2)) := by rw [hsq]
          _ = (2 * Real.pi)⁻¹ * Real.exp ((-(x ^ 2) / 2) + (-(y ^ 2) / 2)) := by rw [Real.exp_add]
          _ = Real.exp (-(x ^ 2 + y ^ 2) / 2) / (2 * Real.pi) := by ring
      calc
        ENNReal.ofReal ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(x ^ 2) / 2)) *
          ENNReal.ofReal ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(y ^ 2) / 2))
            = ENNReal.ofReal (((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(x ^ 2) / 2)) *
              ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(y ^ 2) / 2))) := by
          rw [← ENNReal.ofReal_mul hx]
        _ = ENNReal.ofReal (Real.exp (-(x ^ 2 + y ^ 2) / 2) / (2 * Real.pi)) := by rw [hprod]

end AdversarialBco.Bit.Aux_gauss_prod_density

namespace AdversarialBco.Bit.Aux_bm_polar


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius

theorem _root_.AdversarialBco.Bit.bm_polar (g : ℝ × ℝ → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ p, g p ∂((gaussianReal 0 1).prod (gaussianReal 0 1)) =
      ∫⁻ p in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi,
        ENNReal.ofReal (p.1 * Real.exp (-p.1 ^ 2 / 2) / (2 * Real.pi)) * g (p.1 * Real.cos p.2, p.1 * Real.sin p.2) := by
  have h_density : (gaussianReal 0 1).prod (gaussianReal 0 1) =
      volume.withDensity (fun p : ℝ × ℝ => ENNReal.ofReal (Real.exp (-(p.1 ^ 2 + p.2 ^ 2) / 2) / (2 * Real.pi))) :=
    gauss_prod_density
  rw [h_density]
  have h_meas : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal (Real.exp (-(p.1 ^ 2 + p.2 ^ 2) / 2) / (2 * Real.pi))) := by
    measurability
  rw [lintegral_withDensity_eq_lintegral_mul volume h_meas hg]
  simp_rw [Pi.mul_apply]
  rw [← lintegral_comp_polarCoord_symm]
  have h_target : polarCoord.target = Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi := polarCoord_target
  rw [h_target]
  refine setLIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) ?_
  intro p hp
  rcases hp with ⟨hp₁, hp₂⟩
  have hp₁_nonneg : 0 ≤ p.1 := le_of_lt hp₁
  simp_rw [polarCoord_symm_apply]
  simp_rw [smul_eq_mul]
  have h_sq : (p.1 * Real.cos p.2) ^ 2 + (p.1 * Real.sin p.2) ^ 2 = p.1 ^ 2 := by
    calc
      (p.1 * Real.cos p.2) ^ 2 + (p.1 * Real.sin p.2) ^ 2 = p.1 ^ 2 * (Real.cos p.2 ^ 2 + Real.sin p.2 ^ 2) := by ring
      _ = p.1 ^ 2 * 1 := by rw [Real.cos_sq_add_sin_sq p.2]
      _ = p.1 ^ 2 := by ring
  rw [h_sq]
  have h_mul : ENNReal.ofReal p.1 * ENNReal.ofReal (Real.exp (-p.1 ^ 2 / 2) / (2 * Real.pi)) =
      ENNReal.ofReal (p.1 * Real.exp (-p.1 ^ 2 / 2) / (2 * Real.pi)) := by
    rw [← ENNReal.ofReal_mul hp₁_nonneg]
    congr 1
    ring
  calc
    ENNReal.ofReal p.1 * (ENNReal.ofReal (Real.exp (-p.1 ^ 2 / 2) / (2 * Real.pi)) * g (p.1 * Real.cos p.2, p.1 * Real.sin p.2))
        = (ENNReal.ofReal p.1 * ENNReal.ofReal (Real.exp (-p.1 ^ 2 / 2) / (2 * Real.pi))) * g (p.1 * Real.cos p.2, p.1 * Real.sin p.2) := by ring
    _ = ENNReal.ofReal (p.1 * Real.exp (-p.1 ^ 2 / 2) / (2 * Real.pi)) * g (p.1 * Real.cos p.2, p.1 * Real.sin p.2) := by rw [h_mul]

end AdversarialBco.Bit.Aux_bm_polar

namespace AdversarialBco.Bit.Aux_bm_radius


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius

theorem _root_.AdversarialBco.Bit.bm_radius (h : ℝ → ℝ≥0∞) :
    ∫⁻ u in Set.Ioc (0 : ℝ) 1, h (Real.sqrt (-2 * Real.log u)) =
      ∫⁻ ρ in Set.Ioi (0 : ℝ), ENNReal.ofReal (ρ * Real.exp (-ρ ^ 2 / 2)) * h ρ := by
  set f := fun (ρ : ℝ) => Real.exp (-ρ ^ 2 / 2) with hf_def
  set f' := fun (ρ : ℝ) => -ρ * Real.exp (-ρ ^ 2 / 2) with hf'_def
  set g := fun (u : ℝ) => h (Real.sqrt (-2 * Real.log u)) with hg_def
  have h_meas : MeasurableSet (Set.Ioi (0 : ℝ)) := measurableSet_Ioi
  -- derivative of f on Ioi 0
  have h_deriv : ∀ x ∈ Set.Ioi (0 : ℝ), HasDerivWithinAt f (f' x) (Set.Ioi (0 : ℝ)) x := by
    intro x hx
    have h_inner : HasDerivWithinAt (fun (ρ : ℝ) => -ρ ^ 2 / 2) (-x) (Set.Ioi (0 : ℝ)) x := by
      have h_sq : HasDerivWithinAt (fun (ρ : ℝ) => ρ ^ 2) (2 * x) (Set.Ioi (0 : ℝ)) x := by
        simpa [pow_one] using (hasDerivAt_pow 2 x).hasDerivWithinAt
      have h_neg : HasDerivWithinAt (fun (ρ : ℝ) => -(ρ ^ 2)) (-(2 * x)) (Set.Ioi (0 : ℝ)) x :=
        HasDerivWithinAt.neg h_sq
      have h_div : HasDerivWithinAt (fun (ρ : ℝ) => -(ρ ^ 2) / 2) (-(2 * x) / 2) (Set.Ioi (0 : ℝ)) x :=
        HasDerivWithinAt.div_const h_neg 2
      simpa [show (-(2 * x) / 2 : ℝ) = -x by ring] using h_div
    have h_exp : HasDerivWithinAt (fun (ρ : ℝ) => Real.exp (-ρ ^ 2 / 2))
        (Real.exp (-x ^ 2 / 2) * (-x)) (Set.Ioi (0 : ℝ)) x :=
      HasDerivWithinAt.exp h_inner
    simpa [f', f, mul_comm] using h_exp
  -- f is injective on Ioi 0
  have h_inj : Set.InjOn f (Set.Ioi (0 : ℝ)) := by
    intro x hx y hy hxy
    have hxpos : x > 0 := hx
    have hypos : y > 0 := hy
    have h_exp_eq : Real.exp (-x ^ 2 / 2) = Real.exp (-y ^ 2 / 2) := hxy
    have h_eq : -x ^ 2 / 2 = -y ^ 2 / 2 := Real.exp_injective h_exp_eq
    have hsq : x ^ 2 = y ^ 2 := by linarith
    have hx_nonneg : 0 ≤ x := le_of_lt hxpos
    have hy_nonneg : 0 ≤ y := le_of_lt hypos
    nlinarith
  -- image of Ioi 0 under f is Ioo 0 1
  have h_image : f '' Set.Ioi (0 : ℝ) = Set.Ioo (0 : ℝ) 1 := by
    ext u
    constructor
    · intro ⟨ρ, hρ, h_eq⟩
      rw [← h_eq]
      have hρpos : ρ > 0 := hρ
      have h_sq_pos : ρ ^ 2 > 0 := pow_pos hρpos 2
      have h_neg_div_two_neg : -ρ ^ 2 / 2 < 0 := by nlinarith
      have h_exp_pos : 0 < Real.exp (-ρ ^ 2 / 2) := Real.exp_pos _
      have h_exp_lt_one : Real.exp (-ρ ^ 2 / 2) < 1 := by
        rw [Real.exp_lt_one_iff]
        exact h_neg_div_two_neg
      exact ⟨h_exp_pos, h_exp_lt_one⟩
    · intro ⟨hu_pos, hu_lt_one⟩
      have hu_pos' : 0 < u := hu_pos
      have hu_lt_one' : u < 1 := hu_lt_one
      have h_log_neg : Real.log u < 0 := Real.log_neg hu_pos' hu_lt_one'
      have h_arg_pos : 0 < -2 * Real.log u := by nlinarith
      set ρ := Real.sqrt (-2 * Real.log u) with hρ_def
      have hρ_pos : ρ > 0 := Real.sqrt_pos.mpr h_arg_pos
      have h_sq : ρ ^ 2 = -2 * Real.log u := Real.sq_sqrt (by nlinarith)
      have h_f_ρ : f ρ = u := by
        dsimp [f]
        calc
          Real.exp (-ρ ^ 2 / 2) = Real.exp (-((-2 * Real.log u)) / 2) := by rw [h_sq]
          _ = Real.exp (Real.log u) := by ring_nf
          _ = u := Real.exp_log hu_pos'
      exact ⟨ρ, hρ_pos, h_f_ρ⟩
  -- |f' x| = x * exp(-x^2/2) on Ioi 0
  have h_abs : ∀ x ∈ Set.Ioi (0 : ℝ), ENNReal.ofReal |f' x| = ENNReal.ofReal (x * Real.exp (-x ^ 2 / 2)) := by
    intro x hx
    have hxpos : x > 0 := hx
    have h_f'_neg : f' x < 0 := by
      dsimp [f']
      have h_exp_pos : 0 < Real.exp (-x ^ 2 / 2) := Real.exp_pos _
      nlinarith
    have h_abs_val : |f' x| = x * Real.exp (-x ^ 2 / 2) := by
      rw [abs_of_neg h_f'_neg]
      dsimp [f']
      ring
    rw [h_abs_val]
  -- g(f x) = h x on Ioi 0
  have h_g_f : ∀ x ∈ Set.Ioi (0 : ℝ), g (f x) = h x := by
    intro x hx
    have hxpos : x > 0 := hx
    dsimp [g, f]
    have h_log_exp : Real.log (Real.exp (-x ^ 2 / 2)) = -x ^ 2 / 2 := Real.log_exp _
    calc
      h (Real.sqrt (-2 * Real.log (Real.exp (-x ^ 2 / 2)))) =
          h (Real.sqrt (-2 * (-x ^ 2 / 2))) := by rw [h_log_exp]
      _ = h (Real.sqrt (x ^ 2)) := by ring_nf
      _ = h x := by rw [Real.sqrt_sq (le_of_lt hxpos)]
  -- Ioo 0 1 and Ioc 0 1 are ae equal
  have h_ae_eq : Set.Ioo (0 : ℝ) (1 : ℝ) =ᵐ[volume] Set.Ioc (0 : ℝ) (1 : ℝ) :=
    MeasureTheory.Ioo_ae_eq_Ioc
  have h_eq_on : Set.EqOn (fun (ρ : ℝ) => ENNReal.ofReal |f' ρ| * g (f ρ))
      (fun (ρ : ℝ) => ENNReal.ofReal (ρ * Real.exp (-ρ ^ 2 / 2)) * h ρ) (Set.Ioi (0 : ℝ)) := by
    intro ρ hρ
    simp [h_abs ρ hρ, h_g_f ρ hρ]
  calc
    ∫⁻ u in Set.Ioc (0 : ℝ) 1, h (Real.sqrt (-2 * Real.log u)) =
        ∫⁻ u in Set.Ioo (0 : ℝ) 1, h (Real.sqrt (-2 * Real.log u)) := by
      rw [← MeasureTheory.setLIntegral_congr h_ae_eq]
    _ = ∫⁻ u in f '' Set.Ioi (0 : ℝ), g u := by rw [h_image]
    _ = ∫⁻ ρ in Set.Ioi (0 : ℝ), ENNReal.ofReal |f' ρ| * g (f ρ) :=
      MeasureTheory.lintegral_image_eq_lintegral_abs_deriv_mul h_meas h_deriv h_inj g
    _ = ∫⁻ ρ in Set.Ioi (0 : ℝ), ENNReal.ofReal (ρ * Real.exp (-ρ ^ 2 / 2)) * h ρ := by
      rw [MeasureTheory.setLIntegral_congr_fun measurableSet_Ioi h_eq_on]

end AdversarialBco.Bit.Aux_bm_radius

namespace AdversarialBco.Bit.Aux_bm_angle


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius

theorem _root_.AdversarialBco.Bit.bm_angle (k : ℝ → ℝ≥0∞) :
    ∫⁻ v in Set.Ioc (0 : ℝ) 1, k (2 * Real.pi * v - Real.pi) =
      ∫⁻ θ in Set.Ioo (-Real.pi) Real.pi, ENNReal.ofReal (1 / (2 * Real.pi)) * k θ := by
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have hpi_mul_pos : 0 < 2 * Real.pi := by nlinarith
  set f := fun (v : ℝ) => 2 * Real.pi * v + (-Real.pi) with hf_def
  have h_meas : MeasurableSet (Set.Ioo (0 : ℝ) 1) := measurableSet_Ioo
  have h_deriv : ∀ x ∈ Set.Ioo (0 : ℝ) 1, HasDerivWithinAt f (2 * Real.pi) (Set.Ioo (0 : ℝ) 1) x := by
    intro x hx
    dsimp [f]
    have h1 : HasDerivAt (fun (v : ℝ) => 2 * Real.pi * v) (2 * Real.pi) x := by
      have : HasDerivAt (fun (v : ℝ) => v) 1 x := hasDerivAt_id x
      simpa [mul_comm] using (HasDerivAt.const_mul (2 * Real.pi) this)
    have h2 : HasDerivAt (fun (_ : ℝ) => Real.pi) 0 x := hasDerivAt_const x Real.pi
    have hsub : HasDerivAt (fun (v : ℝ) => (2 * Real.pi * v) - Real.pi) (2 * Real.pi - 0) x :=
      HasDerivAt.sub h1 h2
    simpa [sub_zero] using hsub.hasDerivWithinAt
  have h_inj : Set.InjOn f (Set.Ioo (0 : ℝ) 1) := by
    intro x hx y hy h
    dsimp [f] at h
    have h2 : 2 * Real.pi * x = 2 * Real.pi * y := by linarith
    have hxy : x = y := by
      calc
        x = (2 * Real.pi * x) / (2 * Real.pi) := by field_simp [ne_of_gt hpi_mul_pos]
        _ = (2 * Real.pi * y) / (2 * Real.pi) := by rw [h2]
        _ = y := by field_simp [ne_of_gt hpi_mul_pos]
    exact hxy
  have h_image : f '' Set.Ioo (0 : ℝ) 1 = Set.Ioo (-Real.pi) Real.pi := by
    dsimp [f]
    calc
      (fun (v : ℝ) => 2 * Real.pi * v + (-Real.pi)) '' Set.Ioo (0 : ℝ) 1 =
        Set.Ioo ((2 * Real.pi) * (0 : ℝ) + (-Real.pi)) ((2 * Real.pi) * 1 + (-Real.pi)) := by
        rw [Set.image_affine_Ioo hpi_mul_pos (-Real.pi)]
      _ = Set.Ioo (-Real.pi) (2 * Real.pi - Real.pi) := by ring_nf
      _ = Set.Ioo (-Real.pi) Real.pi := by ring_nf
  have h_eq : ∫⁻ θ in Set.Ioo (-Real.pi) Real.pi, k θ =
             ∫⁻ v in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal (2 * Real.pi) * k (f v) := by
    calc
      ∫⁻ θ in Set.Ioo (-Real.pi) Real.pi, k θ = ∫⁻ θ in f '' Set.Ioo (0 : ℝ) 1, k θ := by rw [h_image]
      _ = ∫⁻ v in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal |(2 * Real.pi : ℝ)| * k (f v) := by
        rw [MeasureTheory.lintegral_image_eq_lintegral_abs_deriv_mul h_meas h_deriv h_inj k]
      _ = ∫⁻ v in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal (2 * Real.pi) * k (f v) := by
        refine lintegral_congr (fun x => ?_)
        have : |(2 * Real.pi : ℝ)| = 2 * Real.pi := abs_of_pos hpi_mul_pos
        simp [this]
  have h_ioc_ae : Set.Ioc (0 : ℝ) 1 =ᵐ[MeasureTheory.volume] Set.Ioo (0 : ℝ) 1 :=
    (MeasureTheory.Ioo_ae_eq_Ioc (a := 0) (b := 1)).symm
  calc
    ∫⁻ v in Set.Ioc (0 : ℝ) 1, k (f v) = ∫⁻ v in Set.Ioo (0 : ℝ) 1, k (f v) := by
      rw [setLIntegral_congr h_ioc_ae]
    _ = ∫⁻ v in Set.Ioo (0 : ℝ) 1, 1 * k (f v) := by
      refine lintegral_congr (fun x => ?_)
      simp
    _ = ∫⁻ v in Set.Ioo (0 : ℝ) 1, (ENNReal.ofReal (1 / (2 * Real.pi)) * ENNReal.ofReal (2 * Real.pi)) * k (f v) := by
      have h_mul : ENNReal.ofReal (1 / (2 * Real.pi)) * ENNReal.ofReal (2 * Real.pi) = 1 := by
        calc
          ENNReal.ofReal (1 / (2 * Real.pi)) * ENNReal.ofReal (2 * Real.pi) =
            ENNReal.ofReal ((1 / (2 * Real.pi)) * (2 * Real.pi)) := by
            rw [ENNReal.ofReal_mul (by positivity : 0 ≤ 1 / (2 * Real.pi))]
          _ = ENNReal.ofReal 1 := by
            field_simp [ne_of_gt hpi_mul_pos]
          _ = 1 := ENNReal.ofReal_one
      rw [h_mul]
    _ = ∫⁻ v in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal (1 / (2 * Real.pi)) * (ENNReal.ofReal (2 * Real.pi) * k (f v)) := by
      refine lintegral_congr (fun x => ?_)
      ring
    _ = ENNReal.ofReal (1 / (2 * Real.pi)) * ∫⁻ v in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal (2 * Real.pi) * k (f v) := by
      rw [lintegral_const_mul' (ENNReal.ofReal (1 / (2 * Real.pi))) (fun v => ENNReal.ofReal (2 * Real.pi) * k (f v)) ENNReal.ofReal_ne_top]
    _ = ENNReal.ofReal (1 / (2 * Real.pi)) * ∫⁻ θ in Set.Ioo (-Real.pi) Real.pi, k θ := by rw [h_eq]
    _ = ∫⁻ θ in Set.Ioo (-Real.pi) Real.pi, ENNReal.ofReal (1 / (2 * Real.pi)) * k θ := by
      rw [lintegral_const_mul' (ENNReal.ofReal (1 / (2 * Real.pi))) k ENNReal.ofReal_ne_top]

end AdversarialBco.Bit.Aux_bm_angle

namespace AdversarialBco.Bit.Aux_bm_neg


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius

theorem _root_.AdversarialBco.Bit.bm_neg :
    ((gaussianReal 0 1).prod (gaussianReal 0 1)).map (fun p : ℝ × ℝ => (-p.1, -p.2)) =
      (gaussianReal 0 1).prod (gaussianReal 0 1) := by
  calc
    ((gaussianReal 0 1).prod (gaussianReal 0 1)).map (fun p : ℝ × ℝ => (-p.1, -p.2))
        = ((gaussianReal 0 1).prod (gaussianReal 0 1)).map (Prod.map (fun x : ℝ => -x) (fun x : ℝ => -x)) := by
      rfl
    _ = (((gaussianReal 0 1).map (fun x : ℝ => -x)).prod ((gaussianReal 0 1).map (fun x : ℝ => -x))) := by
      rw [MeasureTheory.Measure.map_prod_map (gaussianReal 0 1) (gaussianReal 0 1) measurable_neg measurable_neg]
    _ = ((gaussianReal (-0 : ℝ) 1).prod (gaussianReal (-0 : ℝ) 1)) := by
      simp [ProbabilityTheory.gaussianReal_map_neg]
    _ = ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by simp

end AdversarialBco.Bit.Aux_bm_neg

namespace AdversarialBco.Bit.Aux_boxMuller_law2


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius

theorem _root_.AdversarialBco.Bit.boxMuller_law2 :
    ((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod (volume.restrict (Set.Ioc (0 : ℝ) 1))).map
        (fun p : ℝ × ℝ => (Real.sqrt (-2 * Real.log p.1) * Real.cos (2 * Real.pi * p.2),
          Real.sqrt (-2 * Real.log p.1) * Real.sin (2 * Real.pi * p.2))) =
      (gaussianReal 0 1).prod (gaussianReal 0 1) := by
  refine MeasureTheory.Measure.ext_of_lintegral _ ?_
  intro g hg
  set T := (fun p : ℝ × ℝ => (Real.sqrt (-2 * Real.log p.1) * Real.cos (2 * Real.pi * p.2),
    Real.sqrt (-2 * Real.log p.1) * Real.sin (2 * Real.pi * p.2))) with hT_def
  have hT_meas : Measurable T := by
    unfold T
    fun_prop
  rw [MeasureTheory.lintegral_map hg hT_meas]
  rw [MeasureTheory.Measure.prod_restrict (Set.Ioc (0 : ℝ) 1) (Set.Ioc (0 : ℝ) 1)]
  have hGT_meas : Measurable (g ∘ T) := hg.comp hT_meas
  have h_aemeas : AEMeasurable (g ∘ T) ((volume.prod volume).restrict (Set.Ioc (0 : ℝ) 1 ×ˢ Set.Ioc (0 : ℝ) 1)) :=
    hGT_meas.aemeasurable.restrict (s := Set.Ioc (0 : ℝ) 1 ×ˢ Set.Ioc (0 : ℝ) 1)
  have h_split := MeasureTheory.setLIntegral_prod (g ∘ T) h_aemeas
  have h_lhs_eq : (∫⁻ (a : ℝ × ℝ) in Set.Ioc (0 : ℝ) 1 ×ˢ Set.Ioc (0 : ℝ) 1, g (T a) ∂(volume.prod volume)) =
                 (∫⁻ (a : ℝ × ℝ) in Set.Ioc (0 : ℝ) 1 ×ˢ Set.Ioc (0 : ℝ) 1, (g ∘ T) a ∂(volume.prod volume)) := by
    rfl
  rw [h_lhs_eq, h_split]
  simp only [Function.comp_apply]
  unfold T

  -- Define G(p) = g(-p.1, -p.2)
  set G := (fun p : ℝ × ℝ => g (-p.1, -p.2)) with hG_def
  have hG_meas : Measurable G :=
    hg.comp (Measurable.prodMk (Measurable.neg measurable_fst) (Measurable.neg measurable_snd))

  -- Trig identities
  have h_cos (y : ℝ) : Real.cos (2 * Real.pi * y) = -Real.cos (2 * Real.pi * y - Real.pi) := by
    rw [Real.cos_sub_pi, neg_neg]
  have h_sin (y : ℝ) : Real.sin (2 * Real.pi * y) = -Real.sin (2 * Real.pi * y - Real.pi) := by
    rw [Real.sin_sub_pi, neg_neg]

  -- For each x,y: g(R cos(2πy), R sin(2πy)) = G(R cos(2πy-π), R sin(2πy-π))
  have h_integrand (x y : ℝ) : g (Real.sqrt (-2 * Real.log x) * Real.cos (2 * Real.pi * y),
      Real.sqrt (-2 * Real.log x) * Real.sin (2 * Real.pi * y)) =
      G (Real.sqrt (-2 * Real.log x) * Real.cos (2 * Real.pi * y - Real.pi),
        Real.sqrt (-2 * Real.log x) * Real.sin (2 * Real.pi * y - Real.pi)) := by
    dsimp [G]
    rw [h_cos y, h_sin y]
    ring_nf

  -- Helper function F
  set F := (fun (p : ℝ × ℝ) => g (Real.sqrt (-2 * Real.log p.1) * Real.cos (2 * Real.pi * p.2),
    Real.sqrt (-2 * Real.log p.1) * Real.sin (2 * Real.pi * p.2))) with hF_def
  have hF_meas : Measurable F := by
    unfold F; fun_prop

  -- Rewrite the integrand
  have h_inner (y : ℝ) : (∫⁻ (x : ℝ) in Set.Ioc (0 : ℝ) 1, g (Real.sqrt (-2 * Real.log x) * Real.cos (2 * Real.pi * y),
      Real.sqrt (-2 * Real.log x) * Real.sin (2 * Real.pi * y))) =
      (∫⁻ (x : ℝ) in Set.Ioc (0 : ℝ) 1, G (Real.sqrt (-2 * Real.log x) * Real.cos (2 * Real.pi * y - Real.pi),
        Real.sqrt (-2 * Real.log x) * Real.sin (2 * Real.pi * y - Real.pi))) := by
    refine setLIntegral_congr_fun (measurableSet_Ioc (a := (0 : ℝ)) (b := 1)) (fun x hx => ?_)
    rw [h_integrand x y]

  -- Swap integrals
  have h_swap := lintegral_lintegral_swap (μ := volume.restrict (Set.Ioc (0 : ℝ) 1))
    (ν := volume.restrict (Set.Ioc (0 : ℝ) 1)) (f := fun x y => F (x, y))
    (by
      have : Function.uncurry (fun x y => F (x, y)) = F := by rfl
      rw [this]
      exact hF_meas.aemeasurable)
  rw [h_swap]

  -- Apply h_inner
  have h_outer : (∫⁻ (y : ℝ) in Set.Ioc (0 : ℝ) 1, ∫⁻ (x : ℝ) in Set.Ioc (0 : ℝ) 1, F (x, y)) =
                (∫⁻ (y : ℝ) in Set.Ioc (0 : ℝ) 1, ∫⁻ (x : ℝ) in Set.Ioc (0 : ℝ) 1, G (Real.sqrt (-2 * Real.log x) * Real.cos (2 * Real.pi * y - Real.pi),
                  Real.sqrt (-2 * Real.log x) * Real.sin (2 * Real.pi * y - Real.pi))) := by
    refine setLIntegral_congr_fun (measurableSet_Ioc (a := (0 : ℝ)) (b := 1)) (fun y hy => ?_)
    rw [h_inner y]
  rw [h_outer]

  -- Apply bm_radius
  have h_bm_radius (y : ℝ) : (∫⁻ (x : ℝ) in Set.Ioc (0 : ℝ) 1, G (Real.sqrt (-2 * Real.log x) * Real.cos (2 * Real.pi * y - Real.pi),
      Real.sqrt (-2 * Real.log x) * Real.sin (2 * Real.pi * y - Real.pi))) =
      (∫⁻ (ρ : ℝ) in Set.Ioi (0 : ℝ), ENNReal.ofReal (ρ * Real.exp (-ρ ^ 2 / 2)) * G (ρ * Real.cos (2 * Real.pi * y - Real.pi),
        ρ * Real.sin (2 * Real.pi * y - Real.pi))) := by
    simpa using AdversarialBco.Bit.bm_radius (fun ρ => G (ρ * Real.cos (2 * Real.pi * y - Real.pi),
      ρ * Real.sin (2 * Real.pi * y - Real.pi)))

  have h_outer2 : (∫⁻ (y : ℝ) in Set.Ioc (0 : ℝ) 1, ∫⁻ (x : ℝ) in Set.Ioc (0 : ℝ) 1, G (Real.sqrt (-2 * Real.log x) * Real.cos (2 * Real.pi * y - Real.pi),
      Real.sqrt (-2 * Real.log x) * Real.sin (2 * Real.pi * y - Real.pi))) =
      (∫⁻ (y : ℝ) in Set.Ioc (0 : ℝ) 1, ∫⁻ (ρ : ℝ) in Set.Ioi (0 : ℝ), ENNReal.ofReal (ρ * Real.exp (-ρ ^ 2 / 2)) * G (ρ * Real.cos (2 * Real.pi * y - Real.pi),
        ρ * Real.sin (2 * Real.pi * y - Real.pi))) := by
    refine setLIntegral_congr_fun (measurableSet_Ioc (a := (0 : ℝ)) (b := 1)) (fun y hy => ?_)
    rw [h_bm_radius y]
  rw [h_outer2]

  -- Define k(θ)
  set k := (fun (θ : ℝ) => ∫⁻ (ρ : ℝ) in Set.Ioi (0 : ℝ), ENNReal.ofReal (ρ * Real.exp (-ρ ^ 2 / 2)) * G (ρ * Real.cos θ,
    ρ * Real.sin θ)) with hk_def

  have h_bm_angle : (∫⁻ (y : ℝ) in Set.Ioc (0 : ℝ) 1, k (2 * Real.pi * y - Real.pi)) =
      (∫⁻ (θ : ℝ) in Set.Ioo (-Real.pi) Real.pi, ENNReal.ofReal (1 / (2 * Real.pi)) * k θ) := by
    simpa using AdversarialBco.Bit.bm_angle k

  have h_goal_eq : (∫⁻ (y : ℝ) in Set.Ioc (0 : ℝ) 1, ∫⁻ (ρ : ℝ) in Set.Ioi (0 : ℝ),
      ENNReal.ofReal (ρ * Real.exp (-ρ ^ 2 / 2)) * G (ρ * Real.cos (2 * Real.pi * y - Real.pi),
        ρ * Real.sin (2 * Real.pi * y - Real.pi))) =
      (∫⁻ (y : ℝ) in Set.Ioc (0 : ℝ) 1, k (2 * Real.pi * y - Real.pi)) := by
    rfl
  rw [h_goal_eq, h_bm_angle]

  -- Now goal: ∫⁻ θ in Ioo (-π) π, ENNReal.ofReal(1/(2π)) * k(θ) = ∫⁻ a, g a ∂ν
  --
  -- RHS = ∫⁻ a, G a ∂ν  (by bm_neg and lintegral_map)
  --     = ∫⁻ p in Ioi×Ioo, ...  (by bm_polar)
  --
  -- So we need to show LHS equals this

  -- Let's use the key lemma: for any measurable G,
  -- ∫⁻ θ in Ioo (-π) π, ENNReal.ofReal(1/(2π)) * (∫⁻ ρ in Ioi 0, ENNReal.ofReal(ρ*exp(-ρ²/2)) * G(ρ*cos θ, ρ*sin θ))
  -- = ∫⁻ p, G p ∂ν

  -- This is the Box-Muller formula. Let's prove it as a separate claim.

  have h_final : (∫⁻ (θ : ℝ) in Set.Ioo (-Real.pi) Real.pi, ENNReal.ofReal (1 / (2 * Real.pi)) * k θ) =
      (∫⁻ (p : ℝ × ℝ), G p ∂((gaussianReal 0 1).prod (gaussianReal 0 1))) := by
    -- Expand k
    unfold k
    -- Goal: ∫⁻ θ in Ioo (-π) π, ENNReal.ofReal(1/(2π)) * (∫⁻ ρ in Ioi 0, ENNReal.ofReal(ρ*exp(-ρ²/2)) * G(ρ*cos θ, ρ*sin θ))
    -- = ∫⁻ p, G p ∂ν

    -- Use the chain of equalities
    calc
      (∫⁻ (θ : ℝ) in Set.Ioo (-Real.pi) Real.pi, ENNReal.ofReal (1 / (2 * Real.pi)) *
          (∫⁻ (ρ : ℝ) in Set.Ioi (0 : ℝ), ENNReal.ofReal (ρ * Real.exp (-ρ ^ 2 / 2)) * G (ρ * Real.cos θ, ρ * Real.sin θ))) =
          (∫⁻ (θ : ℝ) in Set.Ioo (-Real.pi) Real.pi,
            (∫⁻ (ρ : ℝ) in Set.Ioi (0 : ℝ), ENNReal.ofReal (1 / (2 * Real.pi)) *
              (ENNReal.ofReal (ρ * Real.exp (-ρ ^ 2 / 2)) * G (ρ * Real.cos θ, ρ * Real.sin θ)))) := by
        refine setLIntegral_congr_fun (measurableSet_Ioo (a := -Real.pi) (b := Real.pi)) (fun θ hθ => ?_)
        -- Pull constant inside: c * ∫⁻ f = ∫⁻ (c * f)
        -- lintegral_const_mul: ∫⁻ x, c * f x ∂μ = c * ∫⁻ x, f x ∂μ
        -- We need the reverse: c * ∫⁻ f = ∫⁻ (c * f)
        rw [← lintegral_const_mul (ENNReal.ofReal (1 / (2 * Real.pi))) ?_]
        fun_prop
      _ = (∫⁻ (θ : ℝ) in Set.Ioo (-Real.pi) Real.pi,
            (∫⁻ (ρ : ℝ) in Set.Ioi (0 : ℝ),
              (ENNReal.ofReal (1 / (2 * Real.pi)) * ENNReal.ofReal (ρ * Real.exp (-ρ ^ 2 / 2))) * G (ρ * Real.cos θ, ρ * Real.sin θ))) := by
        refine setLIntegral_congr_fun (measurableSet_Ioo (a := -Real.pi) (b := Real.pi)) (fun θ hθ => ?_)
        refine setLIntegral_congr_fun measurableSet_Ioi (fun ρ hρ => ?_)
        ring
      _ = (∫⁻ (θ : ℝ) in Set.Ioo (-Real.pi) Real.pi,
            (∫⁻ (ρ : ℝ) in Set.Ioi (0 : ℝ),
              ENNReal.ofReal ((ρ * Real.exp (-ρ ^ 2 / 2)) / (2 * Real.pi)) * G (ρ * Real.cos θ, ρ * Real.sin θ))) := by
        refine setLIntegral_congr_fun (measurableSet_Ioo (a := -Real.pi) (b := Real.pi)) (fun θ hθ => ?_)
        refine setLIntegral_congr_fun measurableSet_Ioi (fun ρ hρ => ?_)
        -- ENNReal.ofReal(a) * ENNReal.ofReal(b) = ENNReal.ofReal(a * b) for a,b ≥ 0
        have h_nonneg : 0 ≤ ρ * Real.exp (-ρ ^ 2 / 2) :=
          mul_nonneg (le_of_lt (Set.mem_Ioi.mp hρ)) (Real.exp_pos _).le
        have h_nonneg2 : 0 ≤ 1 / (2 * Real.pi) := by positivity
        rw [← ENNReal.ofReal_mul h_nonneg2]
        congr 2
        ring
      _ = (∫⁻ (p : ℝ × ℝ) in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi,
            ENNReal.ofReal ((p.1 * Real.exp (-p.1 ^ 2 / 2)) / (2 * Real.pi)) * G (p.1 * Real.cos p.2, p.1 * Real.sin p.2)) := by
        -- Use lintegral_lintegral_swap and setLIntegral_prod
        -- The integrand is f(θ,ρ) = ENNReal.ofReal((ρ*exp(-ρ²/2))/(2π)) * G(ρ*cos θ, ρ*sin θ)
        -- We have ∫⁻ θ in Ioo, ∫⁻ ρ in Ioi, f(θ,ρ)
        -- = ∫⁻ ρ in Ioi, ∫⁻ θ in Ioo, f(θ,ρ)  (by lintegral_lintegral_swap)
        -- = ∫⁻ (ρ,θ) in Ioi×Ioo, f(θ,ρ)  (by setLIntegral_prod)

        -- But note: in the target, p.1 = ρ, p.2 = θ
        -- In our integrand, the first argument (ρ) is the inner variable, second (θ) is outer
        -- So f(θ,ρ) with p.1=ρ, p.2=θ gives the target integrand

        -- Let's use lintegral_lintegral_swap
        have h_swap' := lintegral_lintegral_swap (μ := volume.restrict (Set.Ioi (0 : ℝ)))
          (ν := volume.restrict (Set.Ioo (-Real.pi) Real.pi))
          (f := fun ρ θ => ENNReal.ofReal ((ρ * Real.exp (-ρ ^ 2 / 2)) / (2 * Real.pi)) * G (ρ * Real.cos θ, ρ * Real.sin θ))
          (by
            have h_meas : Measurable (fun (p : ℝ × ℝ) => ENNReal.ofReal ((p.1 * Real.exp (-p.1 ^ 2 / 2)) / (2 * Real.pi)) * G (p.1 * Real.cos p.2, p.1 * Real.sin p.2)) := by
              fun_prop
            exact h_meas.aemeasurable)

        -- h_swap': ∫⁻ ρ in Ioi, ∫⁻ θ in Ioo, f(ρ,θ) = ∫⁻ θ in Ioo, ∫⁻ ρ in Ioi, f(ρ,θ)

        -- Our current integral is ∫⁻ θ in Ioo, ∫⁻ ρ in Ioi, f(ρ,θ) where f(ρ,θ) = ENNReal.ofReal((ρ*exp(-ρ²/2))/(2π)) * G(ρ*cos θ, ρ*sin θ)
        -- This equals the RHS of h_swap'
        -- So we can rewrite using h_swap'.symm to get ∫⁻ ρ in Ioi, ∫⁻ θ in Ioo, f(ρ,θ)

        rw [← h_swap']

        -- Now use setLIntegral_prod to combine
        have h_aemeas2 : AEMeasurable (fun (p : ℝ × ℝ) =>
            ENNReal.ofReal ((p.1 * Real.exp (-p.1 ^ 2 / 2)) / (2 * Real.pi)) * G (p.1 * Real.cos p.2, p.1 * Real.sin p.2))
          ((volume.prod volume).restrict (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi)) := by
          refine (Measurable.aemeasurable ?_).restrict (s := Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi)
          fun_prop

        have h_prod2 := MeasureTheory.setLIntegral_prod
          (fun (p : ℝ × ℝ) => ENNReal.ofReal ((p.1 * Real.exp (-p.1 ^ 2 / 2)) / (2 * Real.pi)) * G (p.1 * Real.cos p.2, p.1 * Real.sin p.2)) h_aemeas2

        -- h_prod2: ∫⁻ z in Ioi×Ioo, f(z) = ∫⁻ ρ in Ioi, ∫⁻ θ in Ioo, f(ρ,θ)
        -- We need the reverse
        rw [← h_prod2]
        rfl
      _ = (∫⁻ (p : ℝ × ℝ), G p ∂((gaussianReal 0 1).prod (gaussianReal 0 1))) := by
        rw [AdversarialBco.Bit.bm_polar G hG_meas]

  rw [h_final]

  -- the substitution p -> -p and Lemma bm_neg
  conv_rhs => rw [← AdversarialBco.Bit.bm_neg]
  rw [lintegral_map hg (by fun_prop : Measurable (fun p : ℝ × ℝ => (-p.1, -p.2)))]

end AdversarialBco.Bit.Aux_boxMuller_law2

namespace AdversarialBco.Bit.Aux_boxMuller_law


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius

theorem _root_.AdversarialBco.Bit.boxMuller_law :
    ((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod (volume.restrict (Set.Ioc (0 : ℝ) 1))).map
        (fun p : ℝ × ℝ => Real.sqrt (-2 * Real.log p.1) * Real.cos (2 * Real.pi * p.2)) = gaussianReal 0 1 ∧
      ((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod (volume.restrict (Set.Ioc (0 : ℝ) 1))).map
        (fun p : ℝ × ℝ => Real.sqrt (-2 * Real.log p.1) * Real.sin (2 * Real.pi * p.2)) = gaussianReal 0 1 := by
  set μ := (volume.restrict (Set.Ioc (0 : ℝ) 1)).prod (volume.restrict (Set.Ioc (0 : ℝ) 1)) with hμ
  set f : ℝ × ℝ → ℝ × ℝ := fun p => (Real.sqrt (-2 * Real.log p.1) * Real.cos (2 * Real.pi * p.2),
    Real.sqrt (-2 * Real.log p.1) * Real.sin (2 * Real.pi * p.2)) with hf
  have hjoint : μ.map f = (gaussianReal 0 1).prod (gaussianReal 0 1) := AdversarialBco.Bit.boxMuller_law2
  have hmeas_f : Measurable f := by
    unfold f
    apply Measurable.prodMk
    · refine Measurable.mul ?_ ?_
      · refine Measurable.sqrt ?_
        refine Measurable.mul ?_ ?_
        · exact measurable_const
        · exact Real.measurable_log.comp measurable_fst
      · refine Real.measurable_cos.comp ?_
        exact (measurable_snd.const_mul (2 * Real.pi))
    · refine Measurable.mul ?_ ?_
      · refine Measurable.sqrt ?_
        refine Measurable.mul ?_ ?_
        · exact measurable_const
        · exact Real.measurable_log.comp measurable_fst
      · refine Real.measurable_sin.comp ?_
        exact (measurable_snd.const_mul (2 * Real.pi))
  have huniv : (gaussianReal 0 1) Set.univ = 1 :=
    MeasureTheory.IsProbabilityMeasure.measure_univ
  have hg1_eq : (fun p : ℝ × ℝ => Real.sqrt (-2 * Real.log p.1) * Real.cos (2 * Real.pi * p.2)) = Prod.fst ∘ f := by
    ext p; rfl
  have hg2_eq : (fun p : ℝ × ℝ => Real.sqrt (-2 * Real.log p.1) * Real.sin (2 * Real.pi * p.2)) = Prod.snd ∘ f := by
    ext p; rfl
  constructor
  · calc
      μ.map (fun p : ℝ × ℝ => Real.sqrt (-2 * Real.log p.1) * Real.cos (2 * Real.pi * p.2))
          = μ.map (Prod.fst ∘ f) := by rw [hg1_eq]
      _ = (μ.map f).map Prod.fst := by rw [MeasureTheory.Measure.map_map measurable_fst hmeas_f]
      _ = ((gaussianReal 0 1).prod (gaussianReal 0 1)).map Prod.fst := by rw [hjoint]
      _ = (gaussianReal 0 1) Set.univ • (gaussianReal 0 1) := by rw [MeasureTheory.Measure.map_fst_prod]
      _ = gaussianReal 0 1 := by simpa [huniv]
  · calc
      μ.map (fun p : ℝ × ℝ => Real.sqrt (-2 * Real.log p.1) * Real.sin (2 * Real.pi * p.2))
          = μ.map (Prod.snd ∘ f) := by rw [hg2_eq]
      _ = (μ.map f).map Prod.snd := by rw [MeasureTheory.Measure.map_map measurable_snd hmeas_f]
      _ = ((gaussianReal 0 1).prod (gaussianReal 0 1)).map Prod.snd := by rw [hjoint]
      _ = (gaussianReal 0 1) Set.univ • (gaussianReal 0 1) := by rw [MeasureTheory.Measure.map_snd_prod]
      _ = gaussianReal 0 1 := by simpa [huniv]

end AdversarialBco.Bit.Aux_boxMuller_law
