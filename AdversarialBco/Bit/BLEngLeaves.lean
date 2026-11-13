/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import Mathlib

@[expose] public section

/-!
# The analytic leaves of the engine

The play scale `pt_ε(X) = max(1, gauge_K(X)/(1 - ε))` and the extension `ext_ε(X) = pt_ε(X) F(X/pt_ε(X))/2 +
2 (pt_ε(X) - 1)/ε` of the learner on a convex body `K ⊇ B̄(0, 1)`: the gauge and `pt` are Lipschitz (`gauge_lip1`,
`pt_lip`); Lemma MPAR (`pt_eps`, `ext_eps`); the shift of a coupled round (`ext_lip_shift`,
with `tv_le` and `mpar_le` the bound of the coupling lemma by `κ0`); the regret transfer of one round (`play_gap`); the
norm of
a scalar matrix (`opN_smul_one`, BL's first state).
-/

namespace AdversarialBco.Bit.BLP.EngL

/-- Euclidean space. -/
abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- `pt_ε(X) = max(1, gauge_K(X)/(1 - ε))`. -/
noncomputable def ptE {d : ℕ} (K : Set (E d)) (ε : ℝ) (X : E d) : ℝ := max 1 (gauge K X / (1 - ε))

/-- `ext_ε(X) = pt_ε(X) F(X/pt_ε(X))/2 + 2 (pt_ε(X) - 1)/ε`. -/
noncomputable def extE {d : ℕ} (K : Set (E d)) (ε : ℝ) (F : E d → ℝ) (X : E d) : ℝ :=
  ptE K ε X * F ((ptE K ε X)⁻¹ • X) / 2 + 2 * (ptE K ε X - 1) / ε

/-- The bound of the total variation between two Gaussians, `(|r - 1| + |m|)/min(r, 1)`. -/
noncomputable def tvB (m r : ℝ) : ℝ := (|r - 1| + |m|) / min r 1

theorem gauge_lip1 {d : ℕ} (K : Set (E d)) (hK : Convex ℝ K)
    (h1 : Metric.closedBall (0 : E d) 1 ⊆ K) (x y : E d) : |gauge K x - gauge K y| ≤ ‖x - y‖ := by
  have h_ball_mem_nhds : Metric.closedBall (0 : E d) 1 ∈ nhds (0 : E d) :=
    Metric.closedBall_mem_nhds (0 : E d) (by norm_num : 0 < (1 : ℝ))
  have h_absorb_ball : Absorbent ℝ (Metric.closedBall (0 : E d) 1) :=
    absorbent_nhds_zero h_ball_mem_nhds
  have h_K_mem_nhds : K ∈ nhds (0 : E d) :=
    Filter.mem_of_superset h_ball_mem_nhds h1
  have h_absorb_K : Absorbent ℝ K :=
    absorbent_nhds_zero h_K_mem_nhds
  have h_gauge_sub : ∀ z : E d, gauge K z ≤ ‖z‖ := by
    intro z
    have h_closedBall_gauge : gauge (Metric.closedBall (0 : E d) 1) z = ‖z‖ := by
      rw [gauge_closedBall (by norm_num : 0 ≤ (1 : ℝ)) z]
      norm_num
    have h_mono : gauge K z ≤ gauge (Metric.closedBall (0 : E d) 1) z :=
      gauge_mono h_absorb_ball h1 z
    rw [h_closedBall_gauge] at h_mono
    exact h_mono
  have h_add_yx : gauge K x ≤ gauge K y + gauge K (x - y) := by
    have := gauge_add_le hK h_absorb_K y (x - y)
    simpa [sub_add_cancel] using this
  have h_add_xy : gauge K y ≤ gauge K x + gauge K (y - x) := by
    have := gauge_add_le hK h_absorb_K x (y - x)
    simpa [sub_add_cancel] using this
  have h_bound1 : gauge K x ≤ gauge K y + ‖x - y‖ := by
    refine h_add_yx.trans ?_
    have h_gz : gauge K (x - y) ≤ ‖x - y‖ := h_gauge_sub (x - y)
    nlinarith
  have h_bound2 : gauge K y ≤ gauge K x + ‖x - y‖ := by
    refine h_add_xy.trans ?_
    have h_gz : gauge K (y - x) ≤ ‖y - x‖ := h_gauge_sub (y - x)
    have h_norm : ‖y - x‖ = ‖x - y‖ := by rw [norm_sub_rev]
    rw [h_norm] at h_gz
    nlinarith
  rw [abs_sub_le_iff]
  constructor
  · linarith
  · linarith

theorem pt_lip {d : ℕ} (K : Set (E d)) (hK : Convex ℝ K)
    (h1 : Metric.closedBall (0 : E d) 1 ⊆ K) (ε : ℝ) (hε1 : ε < 1) (x y : E d) :
    |ptE K ε x - ptE K ε y| ≤ ‖x - y‖ / (1 - ε) := by
  have hpos : 0 < 1 - ε := by linarith
  have hball_mem_nhds : Metric.closedBall (0 : E d) 1 ∈ nhds (0 : E d) :=
    Metric.closedBall_mem_nhds (0 : E d) (by norm_num : (0 : ℝ) < 1)
  have hK_mem_nhds : K ∈ nhds (0 : E d) :=
    Filter.mem_of_superset hball_mem_nhds h1
  have h_absorbent : Absorbent ℝ K :=
    absorbent_nhds_zero hK_mem_nhds
  have h_ball_subset : Metric.ball (0 : E d) 1 ⊆ K := by
    intro z hz
    apply h1
    exact Metric.ball_subset_closedBall hz
  have h_lip_gauge : LipschitzWith ((1 : NNReal)⁻¹) (gauge K) :=
    Convex.lipschitzWith_gauge hK (by norm_num : (0 : NNReal) < 1) h_ball_subset
  have h_gauge_lip (a b : E d) : |gauge K a - gauge K b| ≤ ‖a - b‖ := by
    have h := h_lip_gauge.dist_le_mul a b
    simpa [Real.dist_eq, dist_eq_norm_sub, NNReal.coe_one, one_mul] using h
  calc
    |ptE K ε x - ptE K ε y| = |max 1 (gauge K x / (1 - ε)) - max 1 (gauge K y / (1 - ε))| := rfl
    _ = |max (gauge K x / (1 - ε)) 1 - max (gauge K y / (1 - ε)) 1| := by simp [max_comm]
    _ ≤ |gauge K x / (1 - ε) - gauge K y / (1 - ε)| := abs_max_sub_max_le_abs _ _ _
    _ = |(gauge K x - gauge K y) / (1 - ε)| := by rw [sub_div]
    _ = |gauge K x - gauge K y| / |1 - ε| := by rw [abs_div]
    _ = |gauge K x - gauge K y| / (1 - ε) := by rw [abs_of_pos hpos]
    _ ≤ ‖x - y‖ / (1 - ε) := div_le_div_of_nonneg_right (h_gauge_lip x y) (by linarith)

theorem pt_eps {d : ℕ} (K : Set (E d)) (ε ε' : ℝ) (hε : ε ≤ ε') (hε' : ε' ≤ 1 / 2)
    (X : E d) : 0 ≤ ptE K ε' X - ptE K ε X ∧ ptE K ε' X - ptE K ε X ≤ 4 * gauge K X * (ε' - ε) := by
  have hπ : 0 ≤ gauge K X := gauge_nonneg _
  have hεpos : 0 < 1 - ε := by
    have : ε ≤ 1 / 2 := le_trans hε hε'
    linarith
  have hεpos' : 0 < 1 - ε' := by
    linarith
  have h_denom : 1 - ε' ≤ 1 - ε := by
    linarith
  have h_one_div : 1 / (1 - ε) ≤ 1 / (1 - ε') :=
    one_div_le_one_div_of_le hεpos' h_denom
  have h_div : gauge K X / (1 - ε) ≤ gauge K X / (1 - ε') := by
    -- gauge K X / (1 - ε) = gauge K X * (1/(1-ε))
    -- and similarly for ε'
    calc
      gauge K X / (1 - ε) = gauge K X * (1 / (1 - ε)) := by ring
      _ ≤ gauge K X * (1 / (1 - ε')) := by
        nlinarith [hπ, h_one_div]
      _ = gauge K X / (1 - ε') := by ring
  have h_pt_mono : ptE K ε X ≤ ptE K ε' X := by
    dsimp [ptE]
    refine max_le_max ?_ h_div
    rfl
  have h_nonneg : 0 ≤ ptE K ε' X - ptE K ε X := by
    linarith
  have h_upper : ptE K ε' X - ptE K ε X ≤ 4 * gauge K X * (ε' - ε) := by
    dsimp [ptE]
    set a := gauge K X / (1 - ε')
    set b := gauge K X / (1 - ε)
    have hab : b ≤ a := h_div
    have h_max_sub : max 1 a - max 1 b ≤ max (1 - 1) (a - b) :=
      max_sub_max_le_max 1 a 1 b
    have h_one_sub_one : (1 : ℝ) - 1 = 0 := by ring
    rw [h_one_sub_one] at h_max_sub
    have h_nonneg_diff : 0 ≤ a - b := by linarith
    have h_max_eq : max (0 : ℝ) (a - b) = a - b := by
      exact max_eq_right h_nonneg_diff
    rw [h_max_eq] at h_max_sub
    have h_diff_eq : a - b = gauge K X * (1 / (1 - ε') - 1 / (1 - ε)) := by
      dsimp [a, b]
      ring
    rw [h_diff_eq] at h_max_sub
    have h_denom_prod : (1 - ε) * (1 - ε') ≥ 1/4 := by
      have hε_half : ε ≤ 1/2 := le_trans hε hε'
      have hε'_half : ε' ≤ 1/2 := hε'
      nlinarith
    have h_diff_bound : gauge K X * (1 / (1 - ε') - 1 / (1 - ε)) ≤ 4 * gauge K X * (ε' - ε) := by
      have h_eq : 1 / (1 - ε') - 1 / (1 - ε) = (ε' - ε) / ((1 - ε) * (1 - ε')) := by
        field_simp [hεpos.ne.symm, hεpos'.ne.symm]
        ring
      rw [h_eq]
      have h_nonneg_ε_diff : 0 ≤ ε' - ε := by linarith
      have h_nonneg_gauge : 0 ≤ gauge K X := hπ
      have h_nonneg_prod : 0 ≤ (1 - ε) * (1 - ε') := by nlinarith
      -- We have: gauge * (ε'-ε) / ((1-ε)*(1-ε')) ≤ 4 * gauge * (ε'-ε)
      -- Since (1-ε)*(1-ε') ≥ 1/4, dividing by it gives ≤ 4
      -- More precisely: x / d ≤ 4x when d ≥ 1/4 and x ≥ 0
      -- Actually: x/d ≤ 4x  iff  x*(1/d - 4) ≤ 0  iff  x=0 or 1/d ≤ 4  iff  d ≥ 1/4
      -- Since x ≥ 0, we can divide both sides by x (if x > 0)
      -- Let's use: a / d ≤ a * 4  when d ≥ 1/4 and a ≥ 0
      -- Equivalent: a/d ≤ 4a  ↔  a*(1/d - 4) ≤ 0
      -- Since a ≥ 0, we need 1/d - 4 ≤ 0, i.e., d ≥ 1/4
      -- So: a/d = a * (1/d) ≤ a * 4 = 4a
      -- Using field_simp and nlinarith
      have h_prod_pos : 0 < (1 - ε) * (1 - ε') := by nlinarith
      have h_num_nonneg : 0 ≤ gauge K X * (ε' - ε) := by nlinarith
      calc
        gauge K X * ((ε' - ε) / ((1 - ε) * (1 - ε'))) = (gauge K X * (ε' - ε)) / ((1 - ε) * (1 - ε')) := by ring
        _ ≤ (gauge K X * (ε' - ε)) / (1/4) :=
          div_le_div_of_nonneg_left h_num_nonneg (by norm_num) h_denom_prod
        _ = 4 * gauge K X * (ε' - ε) := by ring
    linarith
  exact And.intro h_nonneg h_upper

/-- The arithmetic of Lemma MPAR: the two extensions at `ε ≤ ε'` differ by at most `π (R + 9)(ε' - ε)/ε²`. -/
theorem ext_eps_arith (p p' F0 F1 ε ε' g R pib : ℝ) (hε0 : 0 < ε) (hε : ε ≤ ε') (hε' : ε' ≤ 1 / 2)
    (hp1 : 1 ≤ p) (hpp : 0 ≤ p' - p) (hpp' : p' - p ≤ 4 * g * (ε' - ε)) (hp1g : p - 1 ≤ 2 * g)
    (hF1 : 0 ≤ F1 ∧ F1 ≤ 1) (hpF : p * |F1 - F0| ≤ (p' - p) * R / ε) (hg : g ≤ pib) (hg0 : 0 ≤ g)
    (hR0 : 0 ≤ R) :
    |(p' * F1 / 2 + 2 * (p' - 1) / ε') - (p * F0 / 2 + 2 * (p - 1) / ε)| ≤ pib * (R + 9) * (ε' - ε) / ε ^ 2 := by
  have hε'0 : 0 < ε' := by linarith
  have hw : 0 ≤ ε' - ε := by linarith
  have e : (p' * F1 / 2 + 2 * (p' - 1) / ε') - (p * F0 / 2 + 2 * (p - 1) / ε) =
      (p' - p) * F1 / 2 + p * (F1 - F0) / 2 + 2 * (p' - p) / ε' - 2 * (p - 1) * (ε' - ε) / (ε * ε') := by
    field_simp; ring
  rw [e]
  have t1 : |(p' - p) * F1 / 2| ≤ 2 * g * (ε' - ε) := by
    rw [abs_div, abs_mul, abs_of_nonneg hpp, abs_of_nonneg hF1.1, abs_two]
    nlinarith
  have t2 : |p * (F1 - F0) / 2| ≤ 2 * g * (ε' - ε) * R / ε := by
    rw [abs_div, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ p), abs_two]
    have h4 : (p' - p) * R / ε ≤ 4 * g * (ε' - ε) * R / ε :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hpp' hR0) hε0.le
    have h5 : 4 * g * (ε' - ε) * R / ε = 2 * (2 * g * (ε' - ε) * R / ε) := by ring
    linarith
  have t3 : |2 * (p' - p) / ε'| ≤ 8 * g * (ε' - ε) / ε := by
    rw [abs_of_nonneg (div_nonneg (by linarith) hε'0.le)]
    calc 2 * (p' - p) / ε' ≤ 2 * (p' - p) / ε := div_le_div_of_nonneg_left (by linarith) hε0 hε
      _ ≤ 8 * g * (ε' - ε) / ε := div_le_div_of_nonneg_right (by linarith) hε0.le
  have hq : 0 ≤ 2 * (p - 1) * (ε' - ε) := mul_nonneg (mul_nonneg zero_le_two (by linarith)) hw
  have t4 : |2 * (p - 1) * (ε' - ε) / (ε * ε')| ≤ 4 * g * (ε' - ε) / ε ^ 2 := by
    rw [abs_of_nonneg (div_nonneg hq (by positivity))]
    calc 2 * (p - 1) * (ε' - ε) / (ε * ε') ≤ 2 * (p - 1) * (ε' - ε) / (ε * ε) :=
          div_le_div_of_nonneg_left hq (by positivity) (mul_le_mul_of_nonneg_left hε hε0.le)
      _ ≤ 4 * g * (ε' - ε) / ε ^ 2 := by
          rw [← sq]
          exact div_le_div_of_nonneg_right (by nlinarith) (by positivity)
  have hsum : |(p' - p) * F1 / 2 + p * (F1 - F0) / 2 + 2 * (p' - p) / ε' - 2 * (p - 1) * (ε' - ε) / (ε * ε')| ≤
      2 * g * (ε' - ε) + 2 * g * (ε' - ε) * R / ε + 8 * g * (ε' - ε) / ε + 4 * g * (ε' - ε) / ε ^ 2 := by
    have a1 := abs_sub ((p' - p) * F1 / 2 + p * (F1 - F0) / 2 + 2 * (p' - p) / ε')
      (2 * (p - 1) * (ε' - ε) / (ε * ε'))
    have a2 := abs_add_le ((p' - p) * F1 / 2 + p * (F1 - F0) / 2) (2 * (p' - p) / ε')
    have a3 := abs_add_le ((p' - p) * F1 / 2) (p * (F1 - F0) / 2)
    linarith
  have key : 2 + 2 * R / ε + 8 / ε + 4 / ε ^ 2 ≤ (R + 9) / ε ^ 2 := by
    rw [show (2 : ℝ) + 2 * R / ε + 8 / ε + 4 / ε ^ 2 = (2 * ε ^ 2 + 2 * R * ε + 8 * ε + 4) / ε ^ 2 by
      field_simp]
    exact div_le_div_of_nonneg_right (by nlinarith) (by positivity)
  calc _ ≤ 2 * g * (ε' - ε) + 2 * g * (ε' - ε) * R / ε + 8 * g * (ε' - ε) / ε + 4 * g * (ε' - ε) / ε ^ 2 := hsum
    _ = g * (ε' - ε) * (2 + 2 * R / ε + 8 / ε + 4 / ε ^ 2) := by ring
    _ ≤ g * (ε' - ε) * ((R + 9) / ε ^ 2) := mul_le_mul_of_nonneg_left key (mul_nonneg hg0 hw)
    _ ≤ pib * (ε' - ε) * ((R + 9) / ε ^ 2) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hg hw) (div_nonneg (by linarith) (by positivity))
    _ = pib * (R + 9) * (ε' - ε) / ε ^ 2 := by ring

theorem ext_eps {d : ℕ} (K : Set (E d)) (hK : Convex ℝ K) (hKc : IsClosed K)
    (h1 : Metric.closedBall (0 : E d) 1 ⊆ K) (R : ℝ) (hR : K ⊆ Metric.closedBall 0 R) (F : E d → ℝ)
    (hF01 : ∀ x ∈ K, F x ∈ Set.Icc (0 : ℝ) 1) (ε ε' : ℝ) (hε0 : 0 < ε) (hε : ε ≤ ε') (hε' : ε' ≤ 1 / 2)
    (hlip : ∀ a b : E d, (1 - ε)⁻¹ • a ∈ K → (1 - ε)⁻¹ • b ∈ K → F b - F a ≤ ‖b - a‖ / ε)
    (pib : ℝ) (X : E d) (hX : gauge K X ≤ pib) :
    |extE K ε' F X - extE K ε F X| ≤ pib * (R + 9) * (ε' - ε) / ε ^ 2 := by
  have hε1 : ε < 1 := by linarith
  have hKn : K ∈ nhds (0 : E d) :=
    Filter.mem_of_superset (Metric.closedBall_mem_nhds (0 : E d) one_pos) h1
  have hR0 : 0 ≤ R := by
    have h := hR (h1 (Metric.mem_closedBall_self zero_le_one))
    simpa using h
  have hmemK : ∀ y : E d, gauge K y ≤ 1 → y ∈ K := by
    intro y hy
    have hc : y ∈ closure K := (gauge_le_one_iff_mem_closure hK hKn).1 hy
    rwa [hKc.closure_eq] at hc
  have hmem : ∀ y : E d, gauge K y ≤ 1 - ε → (1 - ε)⁻¹ • y ∈ K := by
    intro y hy
    refine hmemK _ ?_
    rw [gauge_smul_of_nonneg (inv_nonneg.2 (by linarith)), smul_eq_mul, inv_mul_le_iff₀ (by linarith)]
    linarith
  have hgy : ∀ e : ℝ, e < 1 → gauge K ((ptE K e X)⁻¹ • X) ≤ 1 - e := by
    intro e he
    have hp : 1 ≤ ptE K e X := le_max_left _ _
    have hq : gauge K X / (1 - e) ≤ ptE K e X := le_max_right _ _
    rw [div_le_iff₀ (by linarith)] at hq
    rw [gauge_smul_of_nonneg (inv_nonneg.2 (by linarith)), smul_eq_mul, inv_mul_le_iff₀ (by linarith)]
    linarith
  have hp1 : 1 ≤ ptE K ε X := le_max_left _ _
  have hp'1 : 1 ≤ ptE K ε' X := le_max_left _ _
  have hA := pt_eps K ε ε' hε hε' X
  have hm0 := hmem _ (hgy ε hε1)
  have hm1 := hmem _ ((hgy ε' (by linarith)).trans (by linarith))
  have hy1K : (ptE K ε' X)⁻¹ • X ∈ K := hmemK _ ((hgy ε' (by linarith)).trans (by linarith))
  have hFd : |F ((ptE K ε' X)⁻¹ • X) - F ((ptE K ε X)⁻¹ • X)| ≤
      ‖(ptE K ε' X)⁻¹ • X - (ptE K ε X)⁻¹ • X‖ / ε := by
    rw [abs_le]
    constructor
    · have h := hlip _ _ hm1 hm0
      rw [norm_sub_rev] at h
      linarith
    · exact hlip _ _ hm0 hm1
  have hXn : ‖X‖ ≤ ptE K ε' X * R := by
    have h := hR hy1K
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_inv,
      abs_of_pos (by linarith : (0 : ℝ) < ptE K ε' X), inv_mul_le_iff₀ (by linarith)] at h
    exact h
  have hnd : ptE K ε X * ‖(ptE K ε' X)⁻¹ • X - (ptE K ε X)⁻¹ • X‖ ≤ (ptE K ε' X - ptE K ε X) * R := by
    rw [← sub_smul, norm_smul, Real.norm_eq_abs, inv_sub_inv (by linarith) (by linarith), abs_div,
      abs_of_nonpos (by linarith [hA.1] : ptE K ε X - ptE K ε' X ≤ 0), abs_of_pos (by nlinarith)]
    rw [show ptE K ε X * (-(ptE K ε X - ptE K ε' X) / (ptE K ε' X * ptE K ε X) * ‖X‖) =
        (ptE K ε' X - ptE K ε X) * (‖X‖ / ptE K ε' X) by field_simp; ring]
    exact mul_le_mul_of_nonneg_left (by rw [div_le_iff₀ (by linarith)]; linarith) hA.1
  have hpF : ptE K ε X * |F ((ptE K ε' X)⁻¹ • X) - F ((ptE K ε X)⁻¹ • X)| ≤
      (ptE K ε' X - ptE K ε X) * R / ε := by
    calc _ ≤ ptE K ε X * (‖(ptE K ε' X)⁻¹ • X - (ptE K ε X)⁻¹ • X‖ / ε) :=
          mul_le_mul_of_nonneg_left hFd (by linarith)
      _ = ptE K ε X * ‖(ptE K ε' X)⁻¹ • X - (ptE K ε X)⁻¹ • X‖ / ε := by ring
      _ ≤ _ := div_le_div_of_nonneg_right hnd hε0.le
  have hp1g : ptE K ε X - 1 ≤ 2 * gauge K X := by
    have hg0 : 0 ≤ gauge K X := gauge_nonneg _
    unfold ptE
    rcases le_total 1 (gauge K X / (1 - ε)) with h | h
    · rw [max_eq_right h]
      have : gauge K X / (1 - ε) ≤ 2 * gauge K X := by
        rw [div_le_iff₀ (by linarith)]; nlinarith
      linarith
    · rw [max_eq_left h]; linarith
  unfold extE
  exact ext_eps_arith _ _ _ _ ε ε' (gauge K X) R pib hε0 hε hε' hp1 hA.1 hA.2 hp1g
    ⟨(hF01 _ hy1K).1, (hF01 _ hy1K).2⟩ hpF hX (gauge_nonneg _) hR0

theorem ext_lip_shift {d : ℕ} (K : Set (E d)) (hK : Convex ℝ K) (hKc : IsClosed K)
    (h1 : Metric.closedBall (0 : E d) 1 ⊆ K) (R : ℝ) (hR : K ⊆ Metric.closedBall 0 R) (F : E d → ℝ)
    (hF01 : ∀ x ∈ K, F x ∈ Set.Icc (0 : ℝ) 1) (ε ε' : ℝ) (hε0 : 0 < ε) (hε : ε ≤ ε') (hε' : ε' ≤ 1 / 2)
    (hlip : ∀ a b : E d, (1 - ε)⁻¹ • a ∈ K → (1 - ε)⁻¹ • b ∈ K → F b - F a ≤ ‖b - a‖ / ε)
    (hext : ∀ x y : E d, |extE K ε F x - extE K ε F y| ≤ 8 / ε * ‖x - y‖)
    (Le Xb : ℝ) (hLe : 0 ≤ Le) (hXb : Xb ≤ 1 / 16) (X1 X0 : E d) (hX0 : gauge K X0 ≤ Real.sqrt Le)
    (hX : ‖X1 - X0‖ ≤ Xb) :
    |ptE K ε' X1 / ptE K ε X0 - 1| +
        |2 * (extE K ε' F X1 - extE K ε F X0) / ptE K ε X0| ≤
      (2 + 16 / ε) * Xb + (4 * (Real.sqrt Le + 1 / 8) * (ε' - ε) +
        2 * (Real.sqrt Le + 1 / 8) * (R + 9) * (ε' - ε) / ε ^ 2) := by
  have hw : 0 ≤ ε' - ε := sub_nonneg.2 hε
  have hε1 : ε < 1 := by linarith
  have hp0 : 1 ≤ ptE K ε X0 := le_max_left _ _
  have hp0' : 0 < ptE K ε X0 := by linarith
  have hXn : 0 ≤ ‖X1 - X0‖ := norm_nonneg _
  have hg1 : gauge K X1 ≤ Real.sqrt Le + 1 / 8 := by
    have := (abs_le.mp (gauge_lip1 K hK h1 X1 X0)).2
    linarith
  have hA := pt_eps K ε ε' hε hε' X1
  have hB := pt_lip K hK h1 ε hε1 X1 X0
  have hB' : ‖X1 - X0‖ / (1 - ε) ≤ 2 * Xb := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith [mul_nonneg (hXn.trans hX) (by linarith : (0 : ℝ) ≤ 1 / 2 - ε)]
  have hfirst : |ptE K ε' X1 - ptE K ε X0| ≤ 2 * Xb + 4 * (Real.sqrt Le + 1 / 8) * (ε' - ε) := by
    have h4 : 4 * gauge K X1 * (ε' - ε) ≤ 4 * (Real.sqrt Le + 1 / 8) * (ε' - ε) :=
      mul_le_mul_of_nonneg_right (by linarith) hw
    calc |ptE K ε' X1 - ptE K ε X0| = |(ptE K ε' X1 - ptE K ε X1) + (ptE K ε X1 - ptE K ε X0)| := by
          rw [sub_add_sub_cancel]
      _ ≤ |ptE K ε' X1 - ptE K ε X1| + |ptE K ε X1 - ptE K ε X0| := abs_add_le _ _
      _ ≤ _ := by rw [abs_of_nonneg hA.1]; linarith [hA.2]
  have h1st : |ptE K ε' X1 / ptE K ε X0 - 1| ≤ 2 * Xb + 4 * (Real.sqrt Le + 1 / 8) * (ε' - ε) := by
    rw [div_sub_one hp0'.ne', abs_div, abs_of_pos hp0']
    exact (div_le_self (abs_nonneg _) hp0).trans hfirst
  have hC := ext_eps K hK hKc h1 R hR F hF01 ε ε' hε0 hε hε' hlip (Real.sqrt Le + 1 / 8) X1 hg1
  have hD := hext X1 X0
  have h8 : 8 / ε * ‖X1 - X0‖ ≤ 8 / ε * Xb := mul_le_mul_of_nonneg_left hX (by positivity)
  have hE : |extE K ε' F X1 - extE K ε F X0| ≤
      |extE K ε' F X1 - extE K ε F X1| + |extE K ε F X1 - extE K ε F X0| := by
    calc |extE K ε' F X1 - extE K ε F X0| =
        |(extE K ε' F X1 - extE K ε F X1) + (extE K ε F X1 - extE K ε F X0)| := by rw [sub_add_sub_cancel]
      _ ≤ _ := abs_add_le _ _
  have h2nd : |2 * (extE K ε' F X1 - extE K ε F X0) / ptE K ε X0| ≤
      2 * ((Real.sqrt Le + 1 / 8) * (R + 9) * (ε' - ε) / ε ^ 2 + 8 / ε * Xb) := by
    rw [abs_div, abs_of_pos hp0', abs_mul, abs_two]
    refine (div_le_self (by positivity) hp0).trans ?_
    linarith
  have heq : 2 * ((Real.sqrt Le + 1 / 8) * (R + 9) * (ε' - ε) / ε ^ 2 + 8 / ε * Xb) =
      16 / ε * Xb + 2 * (Real.sqrt Le + 1 / 8) * (R + 9) * (ε' - ε) / ε ^ 2 := by ring
  linarith

theorem play_gap {d : ℕ} (K : Set (E d)) (hK : Convex ℝ K) (hKc : IsClosed K)
    (h1 : Metric.closedBall (0 : E d) 1 ⊆ K) (R : ℝ) (hR : K ⊆ Metric.closedBall 0 R) (F : E d → ℝ)
    (ε ε' : ℝ) (hε0 : 0 < ε) (hε : ε ≤ ε') (hε' : ε' ≤ 1 / 2)
    (hlip : ∀ a b : E d, (1 - ε)⁻¹ • a ∈ K → (1 - ε)⁻¹ • b ∈ K → F b - F a ≤ ‖b - a‖ / ε)
    (Le Xb : ℝ) (hLe : 0 ≤ Le) (hXb : Xb ≤ 1 / 16) (X1 X0 : E d) (hX0 : gauge K X0 ≤ Real.sqrt Le)
    (hX : ‖X1 - X0‖ ≤ Xb) :
    |F ((ptE K ε' X1)⁻¹ • X1) - F ((ptE K ε X0)⁻¹ • X0)| ≤
      ((1 + 2 * R) * Xb + 4 * R * (Real.sqrt Le + 1 / 8) * (ε' - ε)) / ε := by
  have hw : 0 ≤ ε' - ε := sub_nonneg.2 hε
  have hε1 : ε < 1 := by linarith
  have hKn : K ∈ nhds (0 : E d) :=
    Filter.mem_of_superset (Metric.closedBall_mem_nhds (0 : E d) one_pos) h1
  have hR0 : 0 ≤ R := by
    have h := hR (h1 (Metric.mem_closedBall_self zero_le_one))
    simpa using h
  have hmem : ∀ y : E d, gauge K y ≤ 1 - ε → (1 - ε)⁻¹ • y ∈ K := by
    intro y hy
    have hc : (1 - ε)⁻¹ • y ∈ closure K := by
      rw [← gauge_le_one_iff_mem_closure hK hKn, gauge_smul_of_nonneg (inv_nonneg.2 (by linarith)),
        smul_eq_mul, inv_mul_le_iff₀ (by linarith)]
      linarith
    rwa [hKc.closure_eq] at hc
  have hgy : ∀ (e : ℝ) (X : E d), e < 1 → gauge K ((ptE K e X)⁻¹ • X) ≤ 1 - e := by
    intro e X he
    have hp : 1 ≤ ptE K e X := le_max_left _ _
    have hq : gauge K X / (1 - e) ≤ ptE K e X := le_max_right _ _
    rw [div_le_iff₀ (by linarith)] at hq
    rw [gauge_smul_of_nonneg (inv_nonneg.2 (by linarith)), smul_eq_mul, inv_mul_le_iff₀ (by linarith)]
    linarith
  have hm0 := hmem _ (hgy ε X0 hε1)
  have hm1 := hmem _ ((hgy ε' X1 (by linarith)).trans (by linarith))
  have hF : |F ((ptE K ε' X1)⁻¹ • X1) - F ((ptE K ε X0)⁻¹ • X0)| ≤
      ‖(ptE K ε' X1)⁻¹ • X1 - (ptE K ε X0)⁻¹ • X0‖ / ε := by
    rw [abs_le]
    constructor
    · have h := hlip _ _ hm1 hm0
      rw [norm_sub_rev] at h
      linarith
    · exact hlip _ _ hm0 hm1
  have hy0 : ‖(ptE K ε X0)⁻¹ • X0‖ ≤ R := by
    have h := hR hm0
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_inv,
      abs_of_pos (by linarith : (0 : ℝ) < 1 - ε), inv_mul_le_iff₀ (by linarith)] at h
    nlinarith [mul_nonneg hε0.le hR0]
  have hp1 : 1 ≤ ptE K ε' X1 := le_max_left _ _
  have hp0 : 1 ≤ ptE K ε X0 := le_max_left _ _
  have hdec : (ptE K ε' X1)⁻¹ • X1 - (ptE K ε X0)⁻¹ • X0 =
      (ptE K ε' X1)⁻¹ • (X1 - X0) + ((ptE K ε' X1)⁻¹ * ptE K ε X0 - 1) • ((ptE K ε X0)⁻¹ • X0) := by
    rw [smul_sub, sub_smul, one_smul, mul_smul, smul_inv_smul₀ (by linarith : ptE K ε X0 ≠ 0)]
    abel
  have hXn : 0 ≤ ‖X1 - X0‖ := norm_nonneg _
  have hg1 : gauge K X1 ≤ Real.sqrt Le + 1 / 8 := by
    have := (abs_le.mp (gauge_lip1 K hK h1 X1 X0)).2
    linarith
  have hA := pt_eps K ε ε' hε hε' X1
  have hB := pt_lip K hK h1 ε hε1 X1 X0
  have hB' : ‖X1 - X0‖ / (1 - ε) ≤ 2 * Xb := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith [mul_nonneg (hXn.trans hX) (by linarith : (0 : ℝ) ≤ 1 / 2 - ε)]
  have hfirst : |ptE K ε' X1 - ptE K ε X0| ≤ 2 * Xb + 4 * (Real.sqrt Le + 1 / 8) * (ε' - ε) := by
    have h4 : 4 * gauge K X1 * (ε' - ε) ≤ 4 * (Real.sqrt Le + 1 / 8) * (ε' - ε) :=
      mul_le_mul_of_nonneg_right (by linarith) hw
    calc |ptE K ε' X1 - ptE K ε X0| = |(ptE K ε' X1 - ptE K ε X1) + (ptE K ε X1 - ptE K ε X0)| := by
          rw [sub_add_sub_cancel]
      _ ≤ |ptE K ε' X1 - ptE K ε X1| + |ptE K ε X1 - ptE K ε X0| := abs_add_le _ _
      _ ≤ _ := by rw [abs_of_nonneg hA.1]; linarith [hA.2]
  have hq1 : ‖(ptE K ε' X1)⁻¹ • (X1 - X0)‖ ≤ Xb := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos (by linarith : (0 : ℝ) < ptE K ε' X1)]
    exact (inv_mul_le_of_le_mul₀ (by linarith) (by linarith) (by nlinarith)).trans hX
  have hq2 : |(ptE K ε' X1)⁻¹ * ptE K ε X0 - 1| ≤ |ptE K ε' X1 - ptE K ε X0| := by
    rw [show (ptE K ε' X1)⁻¹ * ptE K ε X0 - 1 = -((ptE K ε' X1 - ptE K ε X0) / ptE K ε' X1) by
        field_simp; ring, abs_neg, abs_div, abs_of_pos (by linarith : (0 : ℝ) < ptE K ε' X1)]
    exact div_le_self (abs_nonneg _) hp1
  have hnorm : ‖(ptE K ε' X1)⁻¹ • X1 - (ptE K ε X0)⁻¹ • X0‖ ≤
      (1 + 2 * R) * Xb + 4 * R * (Real.sqrt Le + 1 / 8) * (ε' - ε) := by
    rw [hdec]
    refine (norm_add_le _ _).trans ?_
    have h3 : ‖((ptE K ε' X1)⁻¹ * ptE K ε X0 - 1) • ((ptE K ε X0)⁻¹ • X0)‖ ≤
        (2 * Xb + 4 * (Real.sqrt Le + 1 / 8) * (ε' - ε)) * R := by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul (hq2.trans hfirst) hy0 (norm_nonneg _)
        (by linarith [abs_nonneg (ptE K ε' X1 - ptE K ε X0)])
    nlinarith [hq1, h3]
  exact hF.trans (div_le_div_of_nonneg_right hnorm hε0.le)

theorem tv_le (m r κ : ℝ) (hκ : κ ≤ 1 / 4) (h : |r - 1| + |m| ≤ 3 / 4 * κ) :
    0 < r ∧ tvB m r ≤ κ := by
  have h_nonneg_abs : 0 ≤ |r - 1| + |m| := by
    positivity
  have h_nonneg_κ : 0 ≤ κ := by
    linarith
  have h_abs_le : |r - 1| ≤ 3/16 := by
    have : |r - 1| ≤ |r - 1| + |m| := by
      have hm : 0 ≤ |m| := abs_nonneg _
      linarith
    linarith
  have hr_pos : 0 < r := by
    have h' := (abs_le.mp h_abs_le).left
    linarith
  have h_min_ge : 3/4 ≤ min r 1 := by
    have h13 : (13/16 : ℝ) ≤ r := by
      have h' := (abs_le.mp h_abs_le).left
      linarith
    have h_min : (13/16 : ℝ) ≤ min r 1 :=
      le_min h13 (by norm_num : (13/16 : ℝ) ≤ 1)
    linarith
  have h_tvB : tvB m r ≤ κ := by
    dsimp [tvB]
    have h_denom_pos : 0 < min r 1 := by
      linarith
    rw [div_le_iff₀ h_denom_pos]
    calc
      |r - 1| + |m| ≤ 3/4 * κ := h
      _ ≤ κ * min r 1 := by
        nlinarith
  exact And.intro hr_pos h_tvB

theorem mpar_le (pib R ε w tp : ℝ) (hpib : 0 ≤ pib) (hR : 0 ≤ R) (hε0 : 0 < ε)
    (hε : ε ≤ 1 / 2) (hw0 : 0 ≤ w) (hw : w ≤ tp / 16 * ε) :
    4 * pib * w + 2 * pib * (R + 9) * w / ε ^ 2 ≤ tp / 4 * pib * (R + 10) / ε := by
  have htp : 0 ≤ tp := by
    have h := le_trans hw0 hw
    nlinarith
  have hεsq : ε ^ 2 ≤ 1 / 4 := by
    nlinarith
  have hA : 0 ≤ 4 * ε ^ 2 + 2 * (R + 9) := by
    nlinarith
  have h_nonneg_prod : 0 ≤ pib * ε * tp := by
    have hε_nonneg : 0 ≤ ε := by linarith
    have h := mul_nonneg (mul_nonneg hpib hε_nonneg) htp
    exact h
  have h_main : (4 * ε ^ 2 + 2 * (R + 9)) / 4 ≤ R + 10 := by
    nlinarith
  field_simp [hε0.ne.symm]
  calc
    4 * pib * w * (4 * ε ^ 2 + 2 * (R + 9)) ≤ 4 * pib * (tp / 16 * ε) * (4 * ε ^ 2 + 2 * (R + 9)) := by
      have htemp : 4 * pib * w ≤ 4 * pib * (tp / 16 * ε) := by
        have : 0 ≤ 4 * pib := by nlinarith
        nlinarith
      exact mul_le_mul_of_nonneg_right htemp hA
    _ = pib * ε * tp * ((4 * ε ^ 2 + 2 * (R + 9)) / 4) := by ring
    _ ≤ pib * ε * tp * (R + 10) :=
      mul_le_mul_of_nonneg_left h_main h_nonneg_prod

theorem opN_smul_one (d : ℕ) (c : ℝ) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (c • (1 : Matrix (Fin d) (Fin d) ℝ))‖ ≤ |c| := by
  have h_smul : Matrix.toEuclideanCLM (𝕜 := ℝ) (c • (1 : Matrix (Fin d) (Fin d) ℝ)) =
      c • Matrix.toEuclideanCLM (𝕜 := ℝ) (1 : Matrix (Fin d) (Fin d) ℝ) := by
    simpa using (Matrix.toEuclideanCLM (𝕜 := ℝ)).map_smul c (1 : Matrix (Fin d) (Fin d) ℝ)
  have h_one : Matrix.toEuclideanCLM (𝕜 := ℝ) (1 : Matrix (Fin d) (Fin d) ℝ) =
      ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d)) := by
    exact (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d)).toRingEquiv.map_one
  rw [h_smul, h_one]
  calc
    ‖c • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d))‖ ≤ ‖c‖ * ‖ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d))‖ :=
      ContinuousLinearMap.opNorm_smul_le (c : ℝ) (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d)))
    _ = |c| * ‖ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d))‖ := by simp
    _ ≤ |c| * 1 := by
      have h_norm_id : ‖ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d))‖ ≤ 1 :=
        ContinuousLinearMap.norm_id_le (E := EuclideanSpace ℝ (Fin d))
      have h_abs_nonneg : 0 ≤ |c| := abs_nonneg _
      nlinarith
    _ = |c| := by simp

end AdversarialBco.Bit.BLP.EngL
