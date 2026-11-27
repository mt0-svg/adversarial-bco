/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import Mathlib
public import AdversarialBco.Statement

@[expose] public section

/-!
# Leaves of the unified route: certified membership by one weak query

UNI-CM and UNI-GAUGE (a) (the paper's certified questions), in the form the proof uses: one query of the weak
membership oracle at `y' = a + (1 + 2ε/r₀)(y - a)`, `ε = 2^{-k}`; an accept puts `y` in the interior of `K`, a reject
puts the gauge of `y` about `a` above `1 - 3ε/r₀`, and a point deep enough in `K` is accepted. Here `ε > 0` is any
precision, and the gauge is written out, `π_a(y) = sInf {t | 0 < t ∧ a + t⁻¹ (y - a) ∈ K}`, so that a frozen
definition of it unfolds to these statements. `K` is convex with `B(a, r₀) ⊆ K`; it need not be closed.

* `uni_worc_accept` (UNI-CM (a)): `dist(y', K) ≤ ε` puts `y` in the interior of `K`.
* `uni_cm_reject` (UNI-CM (b)): if the ball `B(y', ε)` leaves `K`, then `π_a(y) > 1 - 3ε/r₀`. The core is
  `uni_cm_ball_sub`: a point of `K` on the ray at gauge `t` with `t (1 + 2ε/r₀) ≤ 1 - ε/r₀` puts `B(y', ε)` in `K`.
* `uni_cm_deep` (UNI-CM (c)): if `B(y, ρ) ⊆ K`, `|y - a| ≤ R₀` and `ε + 2εR₀/r₀ ≤ ρ`, then `B(y', ε) ⊆ K`, so the oracle
  must accept.
-/

open Metric

namespace AdversarialBco.Uni

variable {d : ℕ}

/-- The ray set of the gauge is closed upwards: past a point of `K` on the ray from `a`, the ray stays in `K`. -/
theorem uni_ray_mem_of_le {K : Set (E d)} (hK : Convex ℝ K) {a y : E d} (ha : a ∈ K) {t t' : ℝ} (ht : 0 < t)
    (htt' : t ≤ t') (hmem : a + t⁻¹ • (y - a) ∈ K) : a + t'⁻¹ • (y - a) ∈ K := by
  have ht' : 0 < t' := ht.trans_le htt'
  have h := hK.add_smul_sub_mem ha hmem (t := t / t') ⟨by positivity, (div_le_one ht').2 htt'⟩
  have heq : a + t'⁻¹ • (y - a) = a + (t / t') • (a + t⁻¹ • (y - a) - a) := by
    rw [add_sub_cancel_left, smul_smul]
    congr 2
    field_simp
  rw [heq]
  exact h

/-- The ray set of the gauge is nonempty when `B(a, r₀) ⊆ K`. -/
theorem uni_ray_nonempty {K : Set (E d)} {a : E d} {r0 : ℝ} (hr0 : 0 < r0) (hball : closedBall a r0 ⊆ K) (y : E d) :
    {t : ℝ | 0 < t ∧ a + t⁻¹ • (y - a) ∈ K}.Nonempty := by
  have hn := norm_nonneg (y - a)
  refine ⟨(‖y - a‖ + r0) / r0, by positivity, hball ?_⟩
  rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.2 (by positivity : (0 : ℝ) < (‖y - a‖ + r0) / r0)), inv_div,
    div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  nlinarith

/-- The gauge is nonnegative. -/
theorem uni_gauge_nonneg (K : Set (E d)) (a y : E d) : 0 ≤ sInf {t : ℝ | 0 < t ∧ a + t⁻¹ • (y - a) ∈ K} :=
  Real.sInf_nonneg fun _ ht => ht.1.le

/-- Above the gauge, the ray is in `K`. -/
theorem uni_ray_mem_of_gauge_lt {K : Set (E d)} (hK : Convex ℝ K) {a : E d} {r0 : ℝ} (hr0 : 0 < r0)
    (hball : closedBall a r0 ⊆ K) {y : E d} {t : ℝ}
    (ht : sInf {t : ℝ | 0 < t ∧ a + t⁻¹ • (y - a) ∈ K} < t) : a + t⁻¹ • (y - a) ∈ K := by
  obtain ⟨t', ⟨ht'0, ht'K⟩, ht't⟩ := exists_lt_of_csInf_lt (uni_ray_nonempty hr0 hball y) ht
  exact uni_ray_mem_of_le hK (hball (mem_closedBall_self hr0.le)) ht'0 ht't.le ht'K

/-- UNI-CM (a): if the query point `y' = a + (1 + 2ε/r₀)(y - a)` is within `ε` of `K` (the oracle's accept), then `y`
is in the interior of `K`. -/
theorem uni_worc_accept (K : Set (E d)) (hK : Convex ℝ K) (a y : E d) (r0 ε : ℝ) (hr0 : 0 < r0) (hε : 0 < ε)
    (hball : closedBall a r0 ⊆ K) (hacc : infDist (a + (1 + 2 * ε / r0) • (y - a)) K ≤ ε) :
    y ∈ interior K := by
  have hKne : K.Nonempty := ⟨a, hball (mem_closedBall_self hr0.le)⟩
  obtain ⟨z, hzK, hz⟩ :=
    (infDist_lt_iff hKne).1 (show infDist (a + (1 + 2 * ε / r0) • (y - a)) K < 2 * ε by linarith)
  -- `y = (1 - s) b + s z` with `s = 1/(1 + 2ε/r₀)` and `b = a + (r₀/(2ε)) (y' - z)`, `|b - a| < r₀`.
  have hc : 1 < 1 + 2 * ε / r0 := by
    have : 0 < 2 * ε / r0 := by positivity
    linarith
  have hs0 : 0 < (1 + 2 * ε / r0)⁻¹ := inv_pos.2 (by linarith)
  have hs1 : (1 + 2 * ε / r0)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hc
  have hbball : a + (r0 / (2 * ε)) • (a + (1 + 2 * ε / r0) • (y - a) - z) ∈ ball a r0 := by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by positivity : (0 : ℝ) < r0 / (2 * ε))]
    rw [dist_eq_norm] at hz
    calc r0 / (2 * ε) * ‖a + (1 + 2 * ε / r0) • (y - a) - z‖ < r0 / (2 * ε) * (2 * ε) :=
          mul_lt_mul_of_pos_left hz (by positivity)
      _ = r0 := by field_simp
  have hbint := interior_mono hball (ball_subset_interior_closedBall hbball)
  have k1 : (1 - (1 + 2 * ε / r0)⁻¹) * (r0 / (2 * ε)) = (1 + 2 * ε / r0)⁻¹ := by
    have hr : r0 + 2 * ε ≠ 0 := by positivity
    field_simp
    ring
  have k2 : (1 + 2 * ε / r0)⁻¹ * (1 + 2 * ε / r0) = 1 := inv_mul_cancel₀ (by linarith)
  have hcombo : (1 - (1 + 2 * ε / r0)⁻¹) • (a + (r0 / (2 * ε)) • (a + (1 + 2 * ε / r0) • (y - a) - z)) +
      (1 + 2 * ε / r0)⁻¹ • z = y := by
    rw [smul_add, smul_smul, k1, smul_sub, smul_add, smul_smul, k2]
    module
  rw [← hcombo]
  exact hK.combo_interior_self_mem_interior hbint hzK (by linarith) hs0.le (by ring)

/-- The core of UNI-CM (b): a point of `K` on the ray at `t > 0` with `t (1 + 2ε/r₀) ≤ 1 - ε/r₀` puts the ball
`B(y', ε)` about the query point inside `K`. -/
theorem uni_cm_ball_sub (K : Set (E d)) (hK : Convex ℝ K) (a y : E d) (r0 ε t : ℝ) (hr0 : 0 < r0) (hε : 0 < ε)
    (hball : closedBall a r0 ⊆ K) (ht : 0 < t) (hts : t * (1 + 2 * ε / r0) ≤ 1 - ε / r0)
    (hmem : a + t⁻¹ • (y - a) ∈ K) : closedBall (a + (1 + 2 * ε / r0) • (y - a)) ε ⊆ K := by
  intro w hw
  have hx : 0 < ε / r0 := div_pos hε hr0
  have h1s : ε / r0 ≤ 1 - t * (1 + 2 * ε / r0) := by linarith
  have h1s0 : 0 < 1 - t * (1 + 2 * ε / r0) := by linarith
  have hs10 : 0 ≤ t * (1 + 2 * ε / r0) := by positivity
  have hcball : a + (1 - t * (1 + 2 * ε / r0))⁻¹ • (w - (a + (1 + 2 * ε / r0) • (y - a))) ∈ closedBall a r0 := by
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_inv,
      abs_of_pos h1s0, inv_mul_le_iff₀ h1s0]
    rw [mem_closedBall, dist_eq_norm] at hw
    calc ‖w - (a + (1 + 2 * ε / r0) • (y - a))‖ ≤ ε := hw
      _ = ε / r0 * r0 := by field_simp
      _ ≤ (1 - t * (1 + 2 * ε / r0)) * r0 := mul_le_mul_of_nonneg_right h1s hr0.le
  have k1 : t * (1 + 2 * ε / r0) * t⁻¹ = 1 + 2 * ε / r0 := by field_simp
  have k2 : (1 - t * (1 + 2 * ε / r0)) * (1 - t * (1 + 2 * ε / r0))⁻¹ = 1 := mul_inv_cancel₀ h1s0.ne'
  have hw' : (t * (1 + 2 * ε / r0)) • (a + t⁻¹ • (y - a)) +
      (1 - t * (1 + 2 * ε / r0)) • (a + (1 - t * (1 + 2 * ε / r0))⁻¹ • (w - (a + (1 + 2 * ε / r0) • (y - a)))) =
      w := by
    rw [smul_add, smul_smul, k1, smul_add, smul_smul, k2]
    module
  rw [← hw']
  exact hK hmem (hball hcball) hs10 h1s0.le (by ring)

/-- UNI-CM (b): if the ball `B(y', ε)` about the query point `y' = a + (1 + 2ε/r₀)(y - a)` leaves `K` (the oracle's
reject), then the gauge of `y` about `a` exceeds `1 - 3ε/r₀`. -/
theorem uni_cm_reject (K : Set (E d)) (hK : Convex ℝ K) (a y : E d) (r0 ε : ℝ) (hr0 : 0 < r0) (hε : 0 < ε)
    (hball : closedBall a r0 ⊆ K) (hrej : ¬ closedBall (a + (1 + 2 * ε / r0) • (y - a)) ε ⊆ K) :
    1 - 3 * ε / r0 < sInf {t : ℝ | 0 < t ∧ a + t⁻¹ • (y - a) ∈ K} := by
  by_contra hle
  rw [not_lt] at hle
  have hπ0 := uni_gauge_nonneg K a y
  have hx : 0 < ε / r0 := div_pos hε hr0
  have e3 : 3 * ε / r0 = 3 * (ε / r0) := by ring
  have e2 : 2 * ε / r0 = 2 * (ε / r0) := by ring
  rw [e3] at hle
  have hx1 : ε / r0 < 1 := by
    by_contra h
    rw [not_lt] at h
    linarith
  have hc : 0 < 1 + 2 * (ε / r0) := by linarith
  have ht0 : 0 < (1 - ε / r0) / (1 + 2 * (ε / r0)) := div_pos (by linarith) hc
  have hts : (1 - ε / r0) / (1 + 2 * (ε / r0)) * (1 + 2 * (ε / r0)) = 1 - ε / r0 := div_mul_cancel₀ _ hc.ne'
  have hlt : 1 - 3 * (ε / r0) < (1 - ε / r0) / (1 + 2 * (ε / r0)) := by
    rw [lt_div_iff₀ hc]
    nlinarith
  have hmem := uni_ray_mem_of_gauge_lt hK hr0 hball (lt_of_le_of_lt hle hlt)
  apply hrej
  apply uni_cm_ball_sub K hK a y r0 ε _ hr0 hε hball ht0 _ hmem
  rw [e2, hts]

/-- UNI-CM (c): a point `y` with `B(y, ρ) ⊆ K`, `|y - a| ≤ R₀` and `ε + 2εR₀/r₀ ≤ ρ` has `B(y', ε) ⊆ K`, so the weak
oracle may not reject the query. -/
theorem uni_cm_deep (K : Set (E d)) (a y : E d) (r0 R0 ε ρ : ℝ) (hr0 : 0 < r0) (hε : 0 ≤ ε)
    (hy : closedBall y ρ ⊆ K) (hyR : dist y a ≤ R0) (hρ : ε + 2 * ε * R0 / r0 ≤ ρ) :
    closedBall (a + (1 + 2 * ε / r0) • (y - a)) ε ⊆ K := by
  intro w hw
  apply hy
  rw [mem_closedBall] at hw ⊢
  have h1 : dist (a + (1 + 2 * ε / r0) • (y - a)) y = 2 * ε / r0 * dist y a := by
    rw [dist_eq_norm, dist_eq_norm]
    have : a + (1 + 2 * ε / r0) • (y - a) - y = (2 * ε / r0) • (y - a) := by module
    rw [this, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have h2 : 2 * ε / r0 * dist y a ≤ 2 * ε / r0 * R0 := mul_le_mul_of_nonneg_left hyR (by positivity)
  calc dist w y ≤ dist w (a + (1 + 2 * ε / r0) • (y - a)) + dist (a + (1 + 2 * ε / r0) • (y - a)) y :=
        dist_triangle _ _ _
    _ ≤ ε + 2 * ε / r0 * R0 := by rw [h1]; linarith
    _ = ε + 2 * ε * R0 / r0 := by ring
    _ ≤ ρ := hρ

end AdversarialBco.Uni
