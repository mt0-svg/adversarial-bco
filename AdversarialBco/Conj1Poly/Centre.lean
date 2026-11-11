/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Conj1Poly.Geom
public import AdversarialBco.Poly.Df2OracleProof

@[expose] public section

/-!
# Theorem 1.3, Procedure CENTRE-cap and the doubling radii

The mathematical iteration that the prefix PRE of the program computes, on vectors `Fin d → ℝ` (the type of
`Poly.ccUpdate`, `Poly.ellIn`, `Poly.oBall` of Df2Oracle.lean).

* `RowOK Am bv ρ a i`: the row `i` passes the test at `a` with margin `ρ`, `⟨a_i, a⟩ + ρ |a_i| ≤ b_i`; `shrunk` is
  the set `K_ρ` of the points where every row passes; `firstFail` the first row that fails.
* `cutUpdate`: the central cut, `Poly.ccUpdate` for `d ≥ 2` and the halving of the interval for `d = 1`
  (`A' = A/4`, same centre update).
* `centreRun Am bv ρ N E a`: at most `N` tests; at a test, `some a` if every row passes, `none` on a failing zero
  row, else the cut by the first failing row. `centreCap Am bv R ρ N` starts from `E(R² I, 0)`.
* Proposition CENTRE-cap: (a) a returned point is certified (`centreRun_sound`, `rowOK_ball`); (b) if the polytope lies
  in `B(0, R)` and contains a ball of radius `2ρ`, then `N > 2 d (d + 1) log (R/ρ)` tests suffice (`centreCap_some`,
  from `centreRun_none`, `cutUpdate_spec` (Lemma E.4, and `cutUpdate_one` for `d = 1`) and Lemma E.5).
* Form (b): the stages `R_j = 2^{2^j}`, `ρ = 1/2`, with `stageN d j = ⌈2 d (d + 1) log (2 R_j)⌉ + 1` tests each
  (`stageRes`); under the hypotheses the stage `jStarOf R` (the first with `R ≤ R_j`) returns (`stage_some`), and the
  tests of the stages up to it number at most `40 d² (log (2 R) + 1)` (`stages_count`).
-/

open MeasureTheory Matrix

namespace AdversarialBco.Conj1Poly

open AdversarialBco.RealRAM AdversarialBco.Poly

variable {d m : ℕ}

/-! ## The test -/

/-- The Euclidean norm of the row `i`. -/
noncomputable def rowNorm (Am : Matrix (Fin m) (Fin d) ℚ) (i : Fin m) : ℝ := Real.sqrt (∑ j, (Am i j : ℝ) ^ 2)

/-- The row `i` as a real vector. -/
def rowR (Am : Matrix (Fin m) (Fin d) ℚ) (i : Fin m) : Fin d → ℝ := fun j => (Am i j : ℝ)

/-- The row `i` passes the test at `a` with margin `ρ`: `⟨a_i, a⟩ + ρ |a_i| ≤ b_i`. -/
def RowOK (Am : Matrix (Fin m) (Fin d) ℚ) (bv : Fin m → ℚ) (ρ : ℝ) (a : Fin d → ℝ) (i : Fin m) : Prop :=
  ∑ j, (Am i j : ℝ) * a j + ρ * rowNorm Am i ≤ (bv i : ℝ)

/-- `K_ρ`: the points where every row passes. -/
def shrunk (Am : Matrix (Fin m) (Fin d) ℚ) (bv : Fin m → ℚ) (ρ : ℝ) : Set (Fin d → ℝ) :=
  {a | ∀ i, RowOK Am bv ρ a i}

open Classical in
/-- The first row that fails at `a` (`none` if every row passes). -/
noncomputable def firstFail (Am : Matrix (Fin m) (Fin d) ℚ) (bv : Fin m → ℚ) (ρ : ℝ) (a : Fin d → ℝ) :
    Option (Fin m) :=
  if h : ∃ i, ¬ RowOK Am bv ρ a i then some (Fin.find _ h) else none

theorem firstFail_none {Am : Matrix (Fin m) (Fin d) ℚ} {bv : Fin m → ℚ} {ρ : ℝ} {a : Fin d → ℝ}
    (h : firstFail Am bv ρ a = none) : ∀ i, RowOK Am bv ρ a i := by
  unfold firstFail at h
  split_ifs at h with hex
  simp only [not_exists, not_not] at hex
  exact hex

theorem firstFail_some {Am : Matrix (Fin m) (Fin d) ℚ} {bv : Fin m → ℚ} {ρ : ℝ} {a : Fin d → ℝ} {i : Fin m}
    (h : firstFail Am bv ρ a = some i) : ¬ RowOK Am bv ρ a i ∧ ∀ j < i, RowOK Am bv ρ a j := by
  classical
  unfold firstFail at h
  split_ifs at h with hex
  cases h
  exact ⟨Fin.find_spec hex, fun j hj => not_not.1 (Fin.find_min hex hj)⟩

/-- C1a: a point where every row passes with margin `ρ` is the centre of a closed ball of radius `ρ` in the
polytope (Cauchy and Schwarz). -/
theorem rowOK_ball (Am : Matrix (Fin m) (Fin d) ℚ) (bv : Fin m → ℚ) {ρ : ℝ} (hρ : 0 ≤ ρ) {a : Fin d → ℝ}
    (ha : ∀ i, RowOK Am bv ρ a i) : Metric.closedBall (WithLp.toLp 2 a : E d) ρ ⊆ polytope Am bv := by
  intro y hy
  have hdist : dist y (WithLp.toLp 2 a) ≤ ρ := hy
  intro i
  have hnorm : ‖y - (WithLp.toLp 2 a)‖ ≤ ρ := by
    rwa [dist_eq_norm] at hdist
  have ha_i := ha i
  unfold RowOK at ha_i
  -- ha_i : ∑ j, (Am i j : ℝ) * a j + ρ * rowNorm Am i ≤ (bv i : ℝ)
  have h_sum_split : (∑ j : Fin d, (Am i j : ℝ) * y.ofLp j) =
      (∑ j : Fin d, (Am i j : ℝ) * a j) + (∑ j : Fin d, (Am i j : ℝ) * (y.ofLp j - a j)) := by
    calc
      (∑ j : Fin d, (Am i j : ℝ) * y.ofLp j) = (∑ j : Fin d, (Am i j : ℝ) * (a j + (y.ofLp j - a j))) := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        ring
      _ = (∑ j : Fin d, ((Am i j : ℝ) * a j + (Am i j : ℝ) * (y.ofLp j - a j))) := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        ring
      _ = (∑ j : Fin d, (Am i j : ℝ) * a j) + (∑ j : Fin d, (Am i j : ℝ) * (y.ofLp j - a j)) := by
        simp [Finset.sum_add_distrib]
  rw [h_sum_split]
  have h_cauchy : (∑ j : Fin d, (Am i j : ℝ) * (y.ofLp j - a j)) ^ 2 ≤
      (∑ j : Fin d, ((Am i j : ℝ) ^ 2)) * (∑ j : Fin d, ((y.ofLp j - a j) ^ 2)) := by
    simpa using Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin d))
      (fun j => (Am i j : ℝ)) (fun j => (y.ofLp j - a j))
  have h_norm_sq : ‖y - (WithLp.toLp 2 a)‖ ^ 2 = ∑ j : Fin d, ((y.ofLp j - a j) ^ 2) := by
    calc
      ‖y - (WithLp.toLp 2 a)‖ ^ 2 = ∑ j : Fin d, ((y - (WithLp.toLp 2 a)) j) ^ 2 := by
        simpa using EuclideanSpace.real_norm_sq_eq (y - (WithLp.toLp 2 a))
      _ = ∑ j : Fin d, ((y.ofLp j - a j) ^ 2) := by simp
  have h_rowNorm_sq : (rowNorm Am i) ^ 2 = ∑ j : Fin d, ((Am i j : ℝ) ^ 2) := by
    unfold rowNorm
    have h_nonneg : 0 ≤ ∑ j : Fin d, ((Am i j : ℝ) ^ 2) := by
      refine Finset.sum_nonneg (fun j _ => ?_)
      apply pow_two_nonneg
    rw [Real.sq_sqrt h_nonneg]
  have h_nonneg_sqrt : 0 ≤ rowNorm Am i := Real.sqrt_nonneg _
  have h_norm_nonneg : 0 ≤ ‖y - (WithLp.toLp 2 a)‖ := norm_nonneg _
  have h_sq_bound : (∑ j : Fin d, (Am i j : ℝ) * (y.ofLp j - a j)) ^ 2 ≤
      ((rowNorm Am i) * ρ) ^ 2 := by
    calc
      (∑ j : Fin d, (Am i j : ℝ) * (y.ofLp j - a j)) ^ 2 ≤
          (∑ j : Fin d, ((Am i j : ℝ) ^ 2)) * (∑ j : Fin d, ((y.ofLp j - a j) ^ 2)) := h_cauchy
      _ = (rowNorm Am i) ^ 2 * ‖y - (WithLp.toLp 2 a)‖ ^ 2 := by
        rw [h_rowNorm_sq, h_norm_sq]
      _ ≤ (rowNorm Am i) ^ 2 * ρ ^ 2 := by
        have h_sq_le : ‖y - (WithLp.toLp 2 a)‖ ^ 2 ≤ ρ ^ 2 := by
          nlinarith [mul_self_le_mul_self h_norm_nonneg hnorm]
        nlinarith
      _ = ((rowNorm Am i) * ρ) ^ 2 := by ring
  have h_nonneg_rowNorm_mul_ρ : 0 ≤ rowNorm Am i * ρ := mul_nonneg h_nonneg_sqrt hρ
  have h_abs_le : |∑ j : Fin d, (Am i j : ℝ) * (y.ofLp j - a j)| ≤ rowNorm Am i * ρ :=
    abs_le_of_sq_le_sq h_sq_bound h_nonneg_rowNorm_mul_ρ
  have h_sum_le : (∑ j : Fin d, (Am i j : ℝ) * (y.ofLp j - a j)) ≤ rowNorm Am i * ρ :=
    (abs_le.mp h_abs_le).right
  nlinarith

/-! ## The cut -/

/-- The central cut: `Poly.ccUpdate` for `d ≠ 1`, and for `d = 1` the halving `A' = A/4` with the same centre. -/
noncomputable def cutUpdate (E : Matrix (Fin d) (Fin d) ℝ) (a g : Fin d → ℝ) :
    Matrix (Fin d) (Fin d) ℝ × (Fin d → ℝ) :=
  if d = 1 then ((1 / 4 : ℝ) • E, (ccUpdate E a g).2) else ccUpdate E a g

/-- C1c: the cut in dimension `1`. -/
theorem cutUpdate_one (E : Matrix (Fin 1) (Fin 1) ℝ) (a g : Fin 1 → ℝ) (hE : E.PosDef) (hg : g ≠ 0) :
    (cutUpdate E a g).1.PosDef ∧
      (∀ x, ellIn E a x → g ⬝ᵥ (x - a) ≤ 0 → ellIn (cutUpdate E a g).1 (cutUpdate E a g).2 x) ∧
      (cutUpdate E a g).1.det ≤ E.det * Real.exp (-1 / 2) := by
  have hpos : 0 < E 0 0 := Matrix.PosDef.diag_pos hE
  have hcut : cutUpdate E a g = ((1/4 : ℝ) • E, (ccUpdate E a g).2) := by
    unfold cutUpdate; simp
  have hPD : ((1/4 : ℝ) • E).PosDef :=
    Matrix.PosDef.smul hE (by norm_num : 0 < (1/4 : ℝ))
  rw [hcut]
  refine ⟨hPD, ?_, ?_⟩
  · intro x hx ellIn_x
    have hx_sq : (x 0 - a 0)^2 ≤ E 0 0 := by
      unfold ellIn at hx
      rw [Matrix.inv_subsingleton E] at hx
      simp [dotProduct, Matrix.mulVec] at hx
      have hE00_ne : E 0 0 ≠ 0 := by linarith
      field_simp [hE00_ne] at hx
      nlinarith
    have hgx : g 0 * (x 0 - a 0) ≤ 0 := by
      simp [dotProduct] at ellIn_x
      exact ellIn_x
    unfold ellIn
    rw [Matrix.inv_subsingleton ((1/4 : ℝ) • E)]
    simp [dotProduct, Matrix.mulVec]
    have h_cc2 : (ccUpdate E a g).2 0 = a 0 - (1/2) * ((Real.sqrt (g 0 * E 0 0 * g 0))⁻¹ * (E 0 0 * g 0)) := by
      unfold ccUpdate
      simp [Matrix.mulVec, dotProduct]
      ring_nf
    rw [h_cc2]
    set e := E 0 0 with he
    set γ := g 0 with hγ
    have he_pos : 0 < e := hpos
    have he_ne : e ≠ 0 := by linarith
    have hγ_ne : γ ≠ 0 := by
      intro hzero
      apply hg
      ext i; fin_cases i; exact hzero
    have h_sqrt_arg : γ * e * γ = e * (γ * γ) := by ring
    rw [h_sqrt_arg]
    rw [Real.sqrt_mul (by linarith : 0 ≤ e)]
    set t := x 0 - a 0 with ht
    have hgoal : (x 0 - (a 0 - (1/2) * ((Real.sqrt e * Real.sqrt (γ * γ))⁻¹ * (e * γ)))) = t + (1/2) * ((Real.sqrt e * Real.sqrt (γ * γ))⁻¹ * (e * γ)) := by
      rw [ht]
      ring
    rw [hgoal]
    by_cases hγ_pos : 0 < γ
    · have h_sqrt_sq : Real.sqrt (γ * γ) = γ := by
        rw [show γ * γ = γ ^ 2 by ring, Real.sqrt_sq (by linarith : 0 ≤ γ)]
      rw [h_sqrt_sq]
      have h_simp : (Real.sqrt e * γ)⁻¹ * (e * γ) = Real.sqrt e := by
        have hsq_pos : Real.sqrt e ≠ 0 := by
          intro hzero
          have : e = 0 := by nlinarith [Real.sq_sqrt (by linarith : 0 ≤ e)]
          linarith
        field_simp [hsq_pos]
        nlinarith [Real.sq_sqrt (by linarith : 0 ≤ e)]
      rw [h_simp]
      set s := Real.sqrt e with hs_def
      have hs_pos : 0 < s := Real.sqrt_pos.mpr he_pos
      have hs_sq : s ^ 2 = e := Real.sq_sqrt (by linarith : 0 ≤ e)
      rw [← hs_sq]
      have h_bound : t ≤ 0 := by
        rw [ht] at hgx
        nlinarith
      have h_lower : -s ≤ t := by
        rw [ht] at hx_sq
        have h_abs : t^2 ≤ s^2 := by rw [hs_sq]; exact hx_sq
        nlinarith
      field_simp [show s ≠ 0 from by linarith]
      nlinarith
    · have hγ_neg : γ < 0 := by
        by_contra! h
        have h' : γ = 0 := by linarith
        exact hγ_ne h'
      have h_sqrt_sq : Real.sqrt (γ * γ) = -γ := by
        rw [show γ * γ = (-γ) * (-γ) by ring, show (-γ) * (-γ) = (-γ) ^ 2 by ring, Real.sqrt_sq (by linarith : 0 ≤ -γ)]
      rw [h_sqrt_sq]
      have h_simp : (Real.sqrt e * (-γ))⁻¹ * (e * γ) = -Real.sqrt e := by
        have hsq_pos : Real.sqrt e ≠ 0 := by
          intro hzero
          have : e = 0 := by nlinarith [Real.sq_sqrt (by linarith : 0 ≤ e)]
          linarith
        field_simp [hsq_pos]
        nlinarith [Real.sq_sqrt (by linarith : 0 ≤ e)]
      rw [h_simp]
      set s := Real.sqrt e with hs_def
      have hs_pos : 0 < s := Real.sqrt_pos.mpr he_pos
      have hs_sq : s ^ 2 = e := Real.sq_sqrt (by linarith : 0 ≤ e)
      rw [← hs_sq]
      have h_bound : 0 ≤ t := by
        rw [ht] at hgx
        nlinarith
      have h_upper : t ≤ s := by
        rw [ht] at hx_sq
        have h_abs : t^2 ≤ s^2 := by rw [hs_sq]; exact hx_sq
        nlinarith
      field_simp [show s ≠ 0 from by linarith]
      nlinarith
  · simp
    have h_exp : 1/2 ≤ Real.exp (-1/2) := by
      have := Real.add_one_le_exp (-1/2)
      linarith
    nlinarith [hpos, h_exp]

/-- Lemma E.4 for the cut in every dimension `d ≥ 1`. -/
theorem cutUpdate_spec (hd : 1 ≤ d) (E : Matrix (Fin d) (Fin d) ℝ) (a g : Fin d → ℝ) (hE : E.PosDef) (hg : g ≠ 0) :
    (cutUpdate E a g).1.PosDef ∧
      (∀ x, ellIn E a x → g ⬝ᵥ (x - a) ≤ 0 → ellIn (cutUpdate E a g).1 (cutUpdate E a g).2 x) ∧
      (cutUpdate E a g).1.det ≤ E.det * Real.exp (-1 / ((d : ℝ) + 1)) := by
  rcases Nat.lt_or_ge d 2 with h | h
  · obtain rfl : d = 1 := by omega
    have := cutUpdate_one E a g hE hg
    norm_num at this ⊢
    exact this
  · have hcc := lemmaCC d E a g h hE hg
    have hne : d ≠ 1 := by omega
    simp only [cutUpdate, hne, ↓reduceIte]
    exact ⟨hcc.1, hcc.2.1, hcc.2.2.2⟩

/-! ## The iteration -/

/-- At most `N` tests from the ellipsoid `E(E, a)`. -/
noncomputable def centreRun (Am : Matrix (Fin m) (Fin d) ℚ) (bv : Fin m → ℚ) (ρ : ℝ) :
    ℕ → Matrix (Fin d) (Fin d) ℝ → (Fin d → ℝ) → Option (Fin d → ℝ)
  | 0, _, _ => none
  | N + 1, E, a =>
    match firstFail Am bv ρ a with
    | none => some a
    | some i =>
      if rowR Am i = 0 then none
      else centreRun Am bv ρ N (cutUpdate E a (rowR Am i)).1 (cutUpdate E a (rowR Am i)).2

/-- CENTRE-cap: `N` tests from `E(R² I, 0)`. -/
noncomputable def centreCap (Am : Matrix (Fin m) (Fin d) ℚ) (bv : Fin m → ℚ) (R ρ : ℝ) (N : ℕ) :
    Option (Fin d → ℝ) :=
  centreRun Am bv ρ N ((R ^ 2) • (1 : Matrix (Fin d) (Fin d) ℝ)) 0

/-- C1b, Proposition CENTRE-cap (a): a returned point passes every test. -/
theorem centreRun_sound (Am : Matrix (Fin m) (Fin d) ℚ) (bv : Fin m → ℚ) (ρ : ℝ) :
    ∀ (N : ℕ) (E : Matrix (Fin d) (Fin d) ℝ) (a a0 : Fin d → ℝ), centreRun Am bv ρ N E a = some a0 →
      ∀ i, RowOK Am bv ρ a0 i := by
  intro N E a a0 h
  induction' N with N ih generalizing E a a0
  · simp [centreRun] at h
  · simp [centreRun] at h
    cases hfirst : firstFail Am bv ρ a with
    | none =>
      simp [hfirst] at h
      rw [← h]
      exact firstFail_none hfirst
    | some i =>
      simp [hfirst] at h
      rcases h with ⟨hrow, h⟩
      apply ih (cutUpdate E a (rowR Am i)).1 (cutUpdate E a (rowR Am i)).2 a0
      exact h

theorem oNorm_eq_norm_toLp (v : Fin d → ℝ) : oNorm v = ‖WithLp.toLp 2 v‖ := by
  rw [oNorm, PiLp.norm_eq_of_L2 (β := fun _ : Fin d => ℝ)]
  simp [dotProduct, sq]

/-- A ball of radius `2ρ` in the polytope gives a ball of radius `ρ` in `K_ρ`. -/
theorem shrunk_ball (Am : Matrix (Fin m) (Fin d) ℚ) (bv : Fin m → ℚ) {ρ : ℝ} (hρ : 0 ≤ ρ) (z : E d)
    (hz : Metric.closedBall z (2 * ρ) ⊆ polytope Am bv) : ∀ x ∈ oBall (WithLp.ofLp z) ρ, x ∈ shrunk Am bv ρ := by
  intro x hx
  have hx_ball : oNorm (x - WithLp.ofLp z) ≤ ρ := hx
  intro i
  by_cases hni : rowNorm Am i = 0
  · -- rowNorm Am i = 0, so all entries in row i are zero
    have hzero : ∀ j, (Am i j : ℝ) = 0 := by
      intro j
      have hsum : ∑ j : Fin d, (Am i j : ℝ) ^ 2 = 0 := by
        rw [rowNorm] at hni
        have hnonneg : 0 ≤ ∑ j : Fin d, (Am i j : ℝ) ^ 2 := Finset.sum_nonneg (fun j _ => by positivity)
        exact ((Real.sqrt_eq_zero hnonneg).mp hni)
      have hterm : (Am i j : ℝ) ^ 2 ≤ ∑ j : Fin d, (Am i j : ℝ) ^ 2 :=
        Finset.single_le_sum (f := fun k => (Am i k : ℝ) ^ 2) (fun k _ => by positivity) (Finset.mem_univ j)
      nlinarith
    have hzpoly : z ∈ polytope Am bv := by
      have hz_closed : z ∈ Metric.closedBall z (2 * ρ) := by
        rw [Metric.mem_closedBall, dist_self]
        nlinarith
      exact hz hz_closed
    have hbvi : 0 ≤ (bv i : ℝ) := by
      have hrow := hzpoly i
      simp [hzero] at hrow
      exact_mod_cast hrow
    rw [RowOK, hni]
    simp [hzero, hbvi]
  · -- rowNorm Am i > 0
    have hni_pos : 0 < rowNorm Am i := by
      have hnonneg : 0 ≤ rowNorm Am i := Real.sqrt_nonneg _
      exact lt_of_le_of_ne hnonneg (Ne.symm hni)
    set n_i := rowNorm Am i with hn_i_def
    set a_i := rowR Am i with ha_i_def
    have hy_in_ball : WithLp.toLp 2 (x + (ρ / n_i) • a_i) ∈ Metric.closedBall z (2 * ρ) := by
      rw [Metric.mem_closedBall, dist_eq_norm]
      calc
        ‖WithLp.toLp 2 (x + (ρ / n_i) • a_i) - z‖
            = ‖(WithLp.toLp 2 x - z) + (ρ / n_i) • WithLp.toLp 2 a_i‖ := by
          have h : WithLp.toLp 2 (x + (ρ / n_i) • a_i) - z = (WithLp.toLp 2 x - z) + (ρ / n_i) • WithLp.toLp 2 a_i := by
            simp [WithLp.toLp_add, WithLp.toLp_smul, add_sub_right_comm]
          rw [h]
        _ ≤ ‖WithLp.toLp 2 x - z‖ + ‖(ρ / n_i) • WithLp.toLp 2 a_i‖ := norm_add_le _ _
        _ = oNorm (x - WithLp.ofLp z) + ‖(ρ / n_i) • WithLp.toLp 2 a_i‖ := by
          simp [oNorm_eq_norm_toLp]
        _ = oNorm (x - WithLp.ofLp z) + |ρ / n_i| * ‖WithLp.toLp 2 a_i‖ := by
          rw [norm_smul, Real.norm_eq_abs]
        _ = oNorm (x - WithLp.ofLp z) + (ρ / n_i) * ‖WithLp.toLp 2 a_i‖ := by
          rw [abs_of_nonneg (div_nonneg hρ (by nlinarith))]
        _ = oNorm (x - WithLp.ofLp z) + (ρ / n_i) * oNorm a_i := by rw [← oNorm_eq_norm_toLp]
        _ = oNorm (x - WithLp.ofLp z) + (ρ / n_i) * rowNorm Am i := by
          rw [ha_i_def]
          have htemp : oNorm (rowR Am i) = rowNorm Am i := by
            dsimp [oNorm, rowNorm, dotProduct, rowR]
            simp [sq]
          rw [htemp]
        _ = oNorm (x - WithLp.ofLp z) + ρ := by
          rw [hn_i_def]
          have hni' : rowNorm Am i ≠ 0 := by
            intro hzero
            apply hni
            rw [hn_i_def, hzero]
          field_simp [hni']
        _ ≤ ρ + ρ := by nlinarith
        _ = 2 * ρ := by ring
    have hy_poly : WithLp.toLp 2 (x + (ρ / n_i) • a_i) ∈ polytope Am bv := hz hy_in_ball
    have hrow := hy_poly i
    have hsum_eq : (∑ j : Fin d, (Am i j : ℝ) * (x j + (ρ / rowNorm Am i) * (Am i j : ℝ))) =
                   (∑ j : Fin d, (Am i j : ℝ) * x j) + ρ * rowNorm Am i := by
      calc
        (∑ j : Fin d, (Am i j : ℝ) * (x j + (ρ / rowNorm Am i) * (Am i j : ℝ)))
            = (∑ j : Fin d, (Am i j : ℝ) * x j) + (∑ j : Fin d, (Am i j : ℝ) * ((ρ / rowNorm Am i) * (Am i j : ℝ))) := by
          simp [Finset.sum_add_distrib, mul_add]
        _ = (∑ j : Fin d, (Am i j : ℝ) * x j) + (ρ / rowNorm Am i) * (∑ j : Fin d, (Am i j : ℝ) * (Am i j : ℝ)) := by
          simp [Finset.mul_sum, mul_assoc, mul_comm]
        _ = (∑ j : Fin d, (Am i j : ℝ) * x j) + (ρ / rowNorm Am i) * (∑ j : Fin d, (Am i j : ℝ) ^ 2) := by
          simp [sq]
        _ = (∑ j : Fin d, (Am i j : ℝ) * x j) + (ρ / rowNorm Am i) * (rowNorm Am i ^ 2) := by
          rw [rowNorm, Real.sq_sqrt (Finset.sum_nonneg (fun j _ => by positivity))]
        _ = (∑ j : Fin d, (Am i j : ℝ) * x j) + ρ * rowNorm Am i := by
          field_simp [hni]
    rw [RowOK]
    -- goal: (∑ j, (Am i j : ℝ) * x j) + ρ * rowNorm Am i ≤ (bv i : ℝ)
    -- hrow: (∑ j, (Am i j : ℝ) * (x j + (ρ / rowNorm Am i) * (Am i j : ℝ))) ≤ (bv i : ℝ)
    -- hsum_eq: the two LHS are equal
    rw [← hsum_eq]
    exact hrow

theorem rowNorm_nonneg {d m : ℕ} (Am : Matrix (Fin m) (Fin d) ℚ) (i : Fin m) : 0 ≤ rowNorm Am i := by
  dsimp [rowNorm]
  exact Real.sqrt_nonneg _

theorem mem_polytope_of_shrunk {d m : ℕ} (Am : Matrix (Fin m) (Fin d) ℚ) (bv : Fin m → ℚ) {ρ : ℝ} (hρ : 0 ≤ ρ)
    {x : Fin d → ℝ} (hx : x ∈ shrunk Am bv ρ) : (WithLp.toLp 2 x) ∈ polytope Am bv := by
  intro i
  have h := hx i
  dsimp [shrunk, RowOK] at h
  have h_nonneg : 0 ≤ ρ * rowNorm Am i := by
    nlinarith [rowNorm_nonneg Am i, hρ]
  nlinarith

theorem norm_sq_le_of_mem_closedBall {d : ℕ} {R : ℝ} (hR : 0 < R) (x : EuclideanSpace ℝ (Fin d))
    (hx : x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) R) : ‖x‖ ^ 2 ≤ R ^ 2 := by
  rw [Metric.mem_closedBall, dist_eq_norm] at hx
  have h_norm_nonneg : 0 ≤ ‖x‖ := norm_nonneg _
  have hR_nonneg : 0 ≤ R := hR.le
  have h_sq' : ‖x - 0‖ ^ 2 ≤ R ^ 2 := by
    have h_nonneg_sq : 0 ≤ ‖x - 0‖ := norm_nonneg _
    nlinarith
  simpa [sub_zero] using h_sq'

theorem ellIn_smul_one_inv {d : ℕ} (R : ℝ) (hR : 0 < R) (x : Fin d → ℝ) :
    ellIn ((R ^ 2) • (1 : Matrix (Fin d) (Fin d) ℝ)) 0 x ↔ (∑ j, x j ^ 2) / (R ^ 2) ≤ 1 := by
  have hR_sq_pos : 0 < R ^ 2 := pow_pos hR 2
  have hR_sq_ne_zero : R ^ 2 ≠ 0 := by nlinarith
  have h_inv_smul : Invertible (R ^ 2) := by
    exact Units.invertible (Units.mk0 (R ^ 2) hR_sq_ne_zero)
  have h_det_one : IsUnit (1 : Matrix (Fin d) (Fin d) ℝ).det := by
    rw [Matrix.det_one]
    exact isUnit_one
  have h_inv_eq : ((R ^ 2) • (1 : Matrix (Fin d) (Fin d) ℝ))⁻¹ = ((R ^ 2)⁻¹) • (1 : Matrix (Fin d) (Fin d) ℝ) := by
    rw [Matrix.inv_smul (1 : Matrix (Fin d) (Fin d) ℝ) (R ^ 2) h_det_one]
    simp
  have hcalc : x ⬝ᵥ (((R ^ 2) • (1 : Matrix (Fin d) (Fin d) ℝ))⁻¹ *ᵥ x) = (∑ j, x j ^ 2) / (R ^ 2) := by
    rw [h_inv_eq]
    -- Now: x ⬝ᵥ (((R ^ 2)⁻¹) • 1 *ᵥ x) = (∑ j, x j ^ 2) / (R ^ 2)
    -- Note: ((R ^ 2)⁻¹) • 1 *ᵥ x = (R ^ 2)⁻¹ • (1 *ᵥ x) = (R ^ 2)⁻¹ • x
    have h1 : ((R ^ 2)⁻¹ • (1 : Matrix (Fin d) (Fin d) ℝ)) *ᵥ x = (R ^ 2)⁻¹ • x := by
      calc
        ((R ^ 2)⁻¹ • (1 : Matrix (Fin d) (Fin d) ℝ)) *ᵥ x
            = (R ^ 2)⁻¹ • ((1 : Matrix (Fin d) (Fin d) ℝ) *ᵥ x) := by rw [Matrix.smul_mulVec]
        _ = (R ^ 2)⁻¹ • x := by rw [Matrix.one_mulVec]
    rw [h1]
    -- Now: x ⬝ᵥ ((R ^ 2)⁻¹ • x) = (∑ j, x j ^ 2) / (R ^ 2)
    rw [dotProduct_smul, smul_eq_mul]
    -- Now: (R ^ 2)⁻¹ * (x ⬝ᵥ x) = (∑ j, x j ^ 2) / (R ^ 2)
    rw [dotProduct]
    -- Now: (R ^ 2)⁻¹ * (∑ j, x j * x j) = (∑ j, x j ^ 2) / (R ^ 2)
    rw [div_eq_mul_inv, Finset.mul_sum]
    -- Now: (∑ j, (R ^ 2)⁻¹ * (x j * x j)) = (∑ j, x j ^ 2) * (R ^ 2)⁻¹
    simp [Finset.mul_sum, mul_comm, mul_assoc, pow_two]
  dsimp [ellIn]
  simp
  rw [hcalc]

theorem sum_sq_le_R_sq {d : ℕ} {R : ℝ} (hR : 0 < R) (x : Fin d → ℝ)
    (hx : (WithLp.toLp 2 x) ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) R) : (∑ j, x j ^ 2) ≤ R ^ 2 := by
  have h_norm_sq : ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin d))‖ ^ 2 ≤ R ^ 2 :=
    norm_sq_le_of_mem_closedBall hR _ hx
  have h_norm_eq : ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin d))‖ ^ 2 = ∑ j, x j ^ 2 := by
    calc
      ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin d))‖ ^ 2
          = (Real.sqrt (∑ j, ‖(WithLp.toLp 2 x).ofLp j‖ ^ 2)) ^ 2 := by rw [EuclideanSpace.norm_eq]
      _ = ∑ j, ‖(WithLp.toLp 2 x).ofLp j‖ ^ 2 := by
        have h_nonneg : 0 ≤ ∑ j, ‖(WithLp.toLp 2 x).ofLp j‖ ^ 2 := by
          apply Finset.sum_nonneg; intro j _; apply pow_two_nonneg
        rw [Real.sq_sqrt h_nonneg]
      _ = ∑ j, |x j| ^ 2 := by simp
      _ = ∑ j, x j ^ 2 := by
        refine Finset.sum_congr rfl fun j _ => ?_
        simp
  rw [h_norm_eq] at h_norm_sq
  exact h_norm_sq

/-- `K_ρ` lies in the starting ellipsoid `E(R² I, 0)` when the polytope lies in `B(0, R)`. -/
theorem shrunk_sub_ell0 (Am : Matrix (Fin m) (Fin d) ℚ) (bv : Fin m → ℚ) {ρ R : ℝ} (hρ : 0 ≤ ρ) (hR : 0 < R)
    (hK : polytope Am bv ⊆ Metric.closedBall 0 R) :
    ∀ x ∈ shrunk Am bv ρ, ellIn ((R ^ 2) • (1 : Matrix (Fin d) (Fin d) ℝ)) 0 x := by
  intro x hx
  have hx_polytope : (WithLp.toLp 2 x) ∈ polytope Am bv := mem_polytope_of_shrunk Am bv hρ hx
  have hx_ball : (WithLp.toLp 2 x) ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) R := hK hx_polytope
  have h_sum_sq : (∑ j, x j ^ 2) ≤ R ^ 2 := sum_sq_le_R_sq hR x hx_ball
  rw [ellIn_smul_one_inv R hR x]
  exact ((div_le_one (by nlinarith)).mpr h_sum_sq)

/-- C1e, the induction of Proposition CENTRE-cap (b): if the `N` tests all fail, the ellipsoid kept `K_ρ` and its
determinant fell by `e^{-1/(d+1)}` at each cut, while Lemma E.5 bounds it below. -/
theorem centreRun_none (hd : 1 ≤ d) (Am : Matrix (Fin m) (Fin d) ℚ) (bv : Fin m → ℚ) {ρ : ℝ} (hρ : 0 < ρ)
    (z : Fin d → ℝ) (hz : ∀ x ∈ oBall z ρ, x ∈ shrunk Am bv ρ) :
    ∀ (N : ℕ) (E : Matrix (Fin d) (Fin d) ℝ) (a : Fin d → ℝ), E.PosDef → (∀ x ∈ shrunk Am bv ρ, ellIn E a x) →
      centreRun Am bv ρ N E a = none → ρ ^ (2 * d) ≤ E.det * Real.exp (-(N : ℝ) / ((d : ℝ) + 1)) := by
  intro N
  induction' N with N ih
  · -- N = 0
    intro E a hE h_shrunk h_centreRun
    have h_shrunk_oBall : ∀ x ∈ oBall z ρ, ellIn E a x := by
      intro x hx
      exact h_shrunk x (hz x hx)
    have h_det : ρ ^ (2 * d) ≤ E.det := lemmaBALL d E a z ρ hE hρ.le h_shrunk_oBall
    simpa [Real.exp_zero] using h_det
  · -- N+1
    intro E a hE h_shrunk h_centreRun
    -- Expand centreRun definition
    simp [centreRun] at h_centreRun
    -- h_centreRun : (match firstFail Am bv ρ a with
    --   | none => some a
    --   | some i => if rowR Am i = 0 then none
    --     else centreRun Am bv ρ N (cutUpdate E a (rowR Am i)).1 (cutUpdate E a (rowR Am i)).2) = none
    cases h_firstFail : firstFail Am bv ρ a with
    | none =>
      -- h_centreRun : some a = none, contradiction
      simp [h_firstFail] at h_centreRun
    | some i =>
      simp [h_firstFail] at h_centreRun
      -- h_centreRun : (if rowR Am i = 0 then none
      --   else centreRun Am bv ρ N (cutUpdate E a (rowR Am i)).1 (cutUpdate E a (rowR Am i)).2) = none
      by_cases h_rowZero : rowR Am i = 0
      · -- rowR Am i = 0 leads to contradiction
        simp [h_rowZero] at h_centreRun
        have h_firstFail_some := firstFail_some h_firstFail
        rcases h_firstFail_some with ⟨h_notRowOK, h_RowOK_lt⟩
        -- h_notRowOK : ¬ RowOK Am bv ρ a i
        -- From rowR Am i = 0, we get (Am i j : ℝ) = 0 for all j
        have h_rowZero' : ∀ j, (Am i j : ℝ) = 0 := by
          intro j
          have := congr_fun h_rowZero j
          simpa [rowR] using this
        have h_rowNorm_zero : rowNorm Am i = 0 := by
          dsimp [rowNorm]
          simp [h_rowZero']
        have h_notRowOK' : (bv i : ℝ) < ∑ j : Fin d, (Am i j : ℝ) * a j + ρ * rowNorm Am i := by
          dsimp [RowOK] at h_notRowOK
          linarith
        -- z ∈ shrunk Am bv ρ
        have hz_shrunk : z ∈ shrunk Am bv ρ := by
          have hz_mem : z ∈ oBall z ρ := by
            dsimp [oBall, oNorm]
            simp [hρ.le]
          exact hz z hz_mem
        have h_RowOK_z : RowOK Am bv ρ z i := hz_shrunk i
        -- h_RowOK_z : ∑ j, (Am i j : ℝ) * z j + ρ * rowNorm Am i ≤ (bv i : ℝ)
        -- With rowR Am i = 0, this gives 0 ≤ (bv i : ℝ)
        have h_RowOK_z' : (0 : ℝ) ≤ (bv i : ℝ) := by
          dsimp [RowOK] at h_RowOK_z
          have h_sum_zero : (∑ j : Fin d, (Am i j : ℝ) * z j) = 0 := by
            simp [h_rowZero']
          rw [h_sum_zero, h_rowNorm_zero] at h_RowOK_z
          simpa using h_RowOK_z
        -- Now h_notRowOK' with h_rowNorm_zero gives (bv i : ℝ) < 0
        have h_neg : (bv i : ℝ) < 0 := by
          have h_sum_zero' : (∑ j : Fin d, (Am i j : ℝ) * a j) = 0 := by
            simp [h_rowZero']
          rw [h_sum_zero', h_rowNorm_zero] at h_notRowOK'
          linarith
        linarith
      · -- rowR Am i ≠ 0
        simp [h_rowZero] at h_centreRun
        -- h_centreRun : centreRun Am bv ρ N (cutUpdate E a (rowR Am i)).1 (cutUpdate E a (rowR Am i)).2 = none
        set g := rowR Am i with hg_def
        have hg_ne_zero : g ≠ 0 := h_rowZero
        have h_firstFail_some := firstFail_some h_firstFail
        rcases h_firstFail_some with ⟨h_notRowOK, h_RowOK_lt⟩
        -- Show g ⬝ᵥ (x - a) ≤ 0 for all x ∈ shrunk
        have h_g_dot_le : ∀ x ∈ shrunk Am bv ρ, g ⬝ᵥ (x - a) ≤ 0 := by
          intro x hx_shrunk
          have hx_RowOK : RowOK Am bv ρ x i := hx_shrunk i
          -- hx_RowOK : ∑ j, (Am i j : ℝ) * x j + ρ * rowNorm Am i ≤ (bv i : ℝ)
          -- h_notRowOK : ¬ RowOK Am bv ρ a i
          -- i.e., ¬ (∑ j, (Am i j : ℝ) * a j + ρ * rowNorm Am i ≤ (bv i : ℝ))
          dsimp [RowOK] at hx_RowOK h_notRowOK
          -- hx_RowOK : ∑ j, (Am i j : ℝ) * x j + ρ * rowNorm Am i ≤ (bv i : ℝ)
          -- h_notRowOK : ¬ (∑ j, (Am i j : ℝ) * a j + ρ * rowNorm Am i ≤ (bv i : ℝ))
          have h_notRowOK' : (bv i : ℝ) < ∑ j : Fin d, (Am i j : ℝ) * a j + ρ * rowNorm Am i := by
            linarith
          -- From hx_RowOK and h_notRowOK':
          -- ∑ j, (Am i j : ℝ) * x j + ρ * rowNorm Am i ≤ (bv i : ℝ) < ∑ j, (Am i j : ℝ) * a j + ρ * rowNorm Am i
          -- So ∑ j, (Am i j : ℝ) * x j < ∑ j, (Am i j : ℝ) * a j
          have h_sum_lt : ∑ j : Fin d, (Am i j : ℝ) * x j < ∑ j : Fin d, (Am i j : ℝ) * a j := by
            linarith
          -- Now g ⬝ᵥ (x - a) = ∑ j, g j * (x j - a j) = (∑ j, (Am i j : ℝ) * x j) - (∑ j, (Am i j : ℝ) * a j) < 0
          have h_g_dot_eq : g ⬝ᵥ (x - a) = (∑ j : Fin d, (Am i j : ℝ) * x j) - (∑ j : Fin d, (Am i j : ℝ) * a j) := by
            simp [g, rowR, dotProduct, Finset.sum_sub_distrib, mul_sub]
          rw [h_g_dot_eq]
          linarith
        -- Use cutUpdate_spec
        have h_cut := cutUpdate_spec hd E a g hE hg_ne_zero
        rcases h_cut with ⟨hE', h_ellIn, h_det_cut⟩
        -- hE' : (cutUpdate E a g).1.PosDef
        -- h_ellIn : ∀ x, ellIn E a x → g ⬝ᵥ (x - a) ≤ 0 → ellIn (cutUpdate E a g).1 (cutUpdate E a g).2 x
        -- h_det_cut : (cutUpdate E a g).1.det ≤ E.det * Real.exp (-1 / ((d : ℝ) + 1))
        -- Show shrunk ⊆ ellIn of cutUpdate
        have h_shrunk_ellIn : ∀ x ∈ shrunk Am bv ρ, ellIn (cutUpdate E a g).1 (cutUpdate E a g).2 x := by
          intro x hx
          apply h_ellIn x (h_shrunk x hx) (h_g_dot_le x hx)
        -- Apply induction hypothesis
        have h_ih := ih (cutUpdate E a g).1 (cutUpdate E a g).2 hE' h_shrunk_ellIn h_centreRun
        -- h_ih : ρ ^ (2 * d) ≤ (cutUpdate E a g).1.det * Real.exp (-(N : ℝ) / ((d : ℝ) + 1))
        -- Combine with h_det_cut
        have h_exp_nonneg : 0 ≤ Real.exp (-(N : ℝ) / ((d : ℝ) + 1)) := by
          positivity
        calc
          ρ ^ (2 * d) ≤ (cutUpdate E a g).1.det * Real.exp (-(N : ℝ) / ((d : ℝ) + 1)) := h_ih
          _ ≤ (E.det * Real.exp (-1 / ((d : ℝ) + 1))) * Real.exp (-(N : ℝ) / ((d : ℝ) + 1)) := by
            nlinarith
          _ = E.det * (Real.exp (-1 / ((d : ℝ) + 1)) * Real.exp (-(N : ℝ) / ((d : ℝ) + 1))) := by ring
          _ = E.det * Real.exp ((-1 / ((d : ℝ) + 1)) + (-(N : ℝ) / ((d : ℝ) + 1))) := by rw [Real.exp_add]
          _ = E.det * Real.exp (-((N : ℝ) + 1) / ((d : ℝ) + 1)) := by ring_nf
          _ = E.det * Real.exp (-(((N + 1 : ℕ) : ℝ)) / ((d : ℝ) + 1)) := by
            push_cast
            simp

/-- Proposition CENTRE-cap (b). -/
theorem centreCap_some (hd : 1 ≤ d) (Am : Matrix (Fin m) (Fin d) ℚ) (bv : Fin m → ℚ) {R ρ : ℝ} (hρ : 0 < ρ)
    (hR : 0 < R) (hK : polytope Am bv ⊆ Metric.closedBall 0 R) (z : E d)
    (hz : Metric.closedBall z (2 * ρ) ⊆ polytope Am bv) {N : ℕ}
    (hN : 2 * (d : ℝ) * ((d : ℝ) + 1) * Real.log (R / ρ) < N) : ∃ a0, centreCap Am bv R ρ N = some a0 := by
  by_contra! h
  -- h: ∀ a0, centreCap Am bv R ρ N ≠ some a0
  have hnone : centreCap Am bv R ρ N = none := by
    refine Option.eq_none_iff_forall_not_mem.mpr ?_
    intro a0 hsome
    apply h a0
    exact hsome
  have hpos : ((R ^ 2) • (1 : Matrix (Fin d) (Fin d) ℝ)).PosDef := by
    have h_one : (1 : Matrix (Fin d) (Fin d) ℝ).PosDef := Matrix.PosDef.one
    exact Matrix.PosDef.smul h_one (by positivity)
  have h_shrunk_sub : ∀ x ∈ shrunk Am bv ρ, ellIn ((R ^ 2) • (1 : Matrix (Fin d) (Fin d) ℝ)) 0 x :=
    shrunk_sub_ell0 Am bv (by linarith) hR hK
  have h_ball_sub : ∀ x ∈ oBall (WithLp.ofLp z) ρ, x ∈ shrunk Am bv ρ :=
    shrunk_ball Am bv (by linarith) z hz
  have h_ineq := centreRun_none hd Am bv hρ (WithLp.ofLp z) h_ball_sub N ((R ^ 2) • (1 : Matrix (Fin d) (Fin d) ℝ)) 0
    hpos h_shrunk_sub hnone
  -- h_ineq : ρ ^ (2 * d) ≤ ((R ^ 2) • 1).det * Real.exp (-(N : ℝ) / ((d : ℝ) + 1))
  have h_det : ((R ^ 2) • (1 : Matrix (Fin d) (Fin d) ℝ)).det = R ^ (2 * d) := by
    calc
      ((R ^ 2) • (1 : Matrix (Fin d) (Fin d) ℝ)).det = (R ^ 2) ^ (Fintype.card (Fin d)) * (1 : Matrix (Fin d) (Fin d) ℝ).det :=
        Matrix.det_smul _ _
      _ = (R ^ 2) ^ (Fintype.card (Fin d)) * 1 := by simp
      _ = (R ^ 2) ^ (Fintype.card (Fin d)) := by simp
      _ = (R ^ 2) ^ d := by simp
      _ = R ^ (2 * d) := by ring
  rw [h_det] at h_ineq
  -- h_ineq : ρ ^ (2 * d) ≤ R ^ (2 * d) * Real.exp (-(N : ℝ) / ((d : ℝ) + 1))
  have h_pos_pow : 0 < ρ ^ (2 * d) := by positivity
  have h_pos_Rpow : 0 < R ^ (2 * d) := by positivity
  have h_pos_exp : 0 < Real.exp (-(N : ℝ) / ((d : ℝ) + 1)) := by positivity
  have h_pos_mul : 0 < R ^ (2 * d) * Real.exp (-(N : ℝ) / ((d : ℝ) + 1)) := by positivity
  have h_log := Real.log_le_log h_pos_pow h_ineq
  -- h_log : Real.log (ρ ^ (2 * d)) ≤ Real.log (R ^ (2 * d) * Real.exp (-(N : ℝ) / ((d : ℝ) + 1)))
  have hR_ne_zero : R ^ (2 * d) ≠ 0 := by positivity
  have h_exp_ne_zero : Real.exp (-(N : ℝ) / ((d : ℝ) + 1)) ≠ 0 := by positivity
  rw [Real.log_pow, Real.log_mul hR_ne_zero h_exp_ne_zero, Real.log_pow, Real.log_exp] at h_log
  -- h_log : ↑(2 * d) * Real.log ρ ≤ ↑(2 * d) * Real.log R + (-(N : ℝ) / ((d : ℝ) + 1))
  have h_log' : (N : ℝ) ≤ 2 * (d : ℝ) * ((d : ℝ) + 1) * Real.log (R / ρ) := by
    have h_div : Real.log R - Real.log ρ = Real.log (R / ρ) := by
      refine (Real.log_div (by linarith) (by linarith)).symm
    -- From h_log: ↑(2*d) * log ρ ≤ ↑(2*d) * log R - N/(d+1)
    -- Multiply by (d+1) and rearrange
    have h_log_rewritten : (2 * (d : ℝ)) * Real.log ρ ≤ (2 * (d : ℝ)) * Real.log R + (-(N : ℝ) / ((d : ℝ) + 1)) := by
      simpa [Nat.cast_mul, Nat.cast_ofNat] using h_log
    have h_mul := mul_le_mul_of_nonneg_right h_log_rewritten (by linarith : 0 ≤ (d : ℝ) + 1)
    field_simp [show (d : ℝ) + 1 ≠ 0 from by linarith] at h_mul
    -- h_mul : 2*d*log ρ*(d+1) ≤ 2*d*(d+1)*log R - N
    -- Goal: N ≤ 2*d*(d+1)*log(R/ρ)
    rw [← h_div]
    -- Goal: N ≤ 2*d*(d+1)*(log R - log ρ)
    nlinarith
  -- h_log' : (N : ℝ) ≤ 2 * (d : ℝ) * ((d : ℝ) + 1) * Real.log (R / ρ)
  -- But hN : 2 * (d : ℝ) * ((d : ℝ) + 1) * Real.log (R / ρ) < N
  -- Note: hN has N on the right, which is ℕ coerced to ℝ
  have hN' : 2 * (d : ℝ) * ((d : ℝ) + 1) * Real.log (R / ρ) < (N : ℝ) := by exact_mod_cast hN
  linarith

/-! ## The doubling radii (form (b)) -/

/-- The radius of the stage `j`, `2^{2^j}`. -/
noncomputable def stageR (j : ℕ) : ℝ := 2 ^ (2 ^ j)

/-- The cap of the stage `j` at the margin `1/2`: `⌈2 d (d + 1) log (2 R_j)⌉ + 1` tests. -/
noncomputable def stageN (d j : ℕ) : ℕ := ⌈2 * (d : ℝ) * ((d : ℝ) + 1) * Real.log (2 * stageR j)⌉₊ + 1

/-- The result of the stage `j`. -/
noncomputable def stageRes (Am : Matrix (Fin m) (Fin d) ℚ) (bv : Fin m → ℚ) (j : ℕ) : Option (Fin d → ℝ) :=
  centreCap Am bv (stageR j) (1 / 2) (stageN d j)

theorem exists_stageR_ge (R : ℝ) : ∃ j, R ≤ stageR j := by
  refine ⟨⌈R⌉₊, (Nat.le_ceil R).trans ?_⟩
  have h1 : ⌈R⌉₊ < 2 ^ ⌈R⌉₊ := Nat.lt_two_pow_self
  have h2 : 2 ^ ⌈R⌉₊ < 2 ^ 2 ^ ⌈R⌉₊ := Nat.pow_lt_pow_right (by norm_num) Nat.lt_two_pow_self
  unfold stageR
  exact_mod_cast (h1.trans h2).le

open Classical in
/-- The first stage whose radius is at least `R`. -/
noncomputable def jStarOf (R : ℝ) : ℕ := Nat.find (exists_stageR_ge R)

/-- Under the hypotheses, a stage whose radius is at least a radius of the polytope returns. -/
theorem stage_some (hd : 1 ≤ d) (Am : Matrix (Fin m) (Fin d) ℚ) (bv : Fin m → ℚ) {R0 : ℝ}
    (hK : polytope Am bv ⊆ Metric.closedBall 0 R0) (z : E d) (hz : Metric.closedBall z 1 ⊆ polytope Am bv)
    {j : ℕ} (hj : R0 ≤ stageR j) : ∃ a0, stageRes Am bv j = some a0 := by
  have hRpos : 0 < stageR j := by
    dsimp [stageR]
    apply pow_pos (by norm_num : 0 < (2 : ℝ)) _
  have hρpos : 0 < (1/2 : ℝ) := by norm_num
  have hK' : polytope Am bv ⊆ Metric.closedBall 0 (stageR j) :=
    hK.trans (Metric.closedBall_subset_closedBall hj)
  have hz' : Metric.closedBall z (2 * (1/2 : ℝ)) ⊆ polytope Am bv := by
    have h_eq : (2 : ℝ) * (1/2 : ℝ) = (1 : ℝ) := by norm_num
    rw [h_eq]
    exact hz
  have hN : 2 * (d : ℝ) * ((d : ℝ) + 1) * Real.log (stageR j / (1/2 : ℝ)) < (stageN d j : ℝ) := by
    have h_div : stageR j / (1/2 : ℝ) = 2 * stageR j := by
      field_simp
    rw [h_div]
    dsimp [stageN]
    have hx_le_ceil : 2 * (d : ℝ) * ((d : ℝ) + 1) * Real.log (2 * stageR j) ≤
        (⌈2 * (d : ℝ) * ((d : ℝ) + 1) * Real.log (2 * stageR j)⌉₊ : ℝ) :=
      Nat.le_ceil _
    have h_lt : (⌈2 * (d : ℝ) * ((d : ℝ) + 1) * Real.log (2 * stageR j)⌉₊ : ℝ) <
        (⌈2 * (d : ℝ) * ((d : ℝ) + 1) * Real.log (2 * stageR j)⌉₊ : ℝ) + 1 := by norm_num
    have hx_lt_succ : 2 * (d : ℝ) * ((d : ℝ) + 1) * Real.log (2 * stageR j) <
        (⌈2 * (d : ℝ) * ((d : ℝ) + 1) * Real.log (2 * stageR j)⌉₊ : ℝ) + 1 :=
      hx_le_ceil.trans_lt h_lt
    simpa [Nat.cast_add, Nat.cast_one] using hx_lt_succ
  have h := centreCap_some hd Am bv hρpos hRpos hK' z hz' (N := stageN d j) hN
  simpa [stageRes] using h

/-- The tests of the stages up to `jStarOf R` number at most `40 d² (log (2 R) + 1)`. -/
theorem stages_count (hd : 1 ≤ d) {R : ℝ} (hR : 1 ≤ R) :
    ∑ j ∈ Finset.range (jStarOf R + 1), (stageN d j : ℝ) ≤ 40 * (d : ℝ) ^ 2 * (Real.log (2 * R) + 1) := by
  classical
  set J := jStarOf R with hJdef
  set L := Real.log 2 with hL
  have hL1 : 0.69 < L := by have := Real.log_two_gt_d9; rw [hL]; linarith
  have hlR : 0 ≤ Real.log R := Real.log_nonneg hR
  have hlog2R : Real.log (2 * R) = L + Real.log R := Real.log_mul (by norm_num) (by linarith)
  have hD : (1 : ℝ) ≤ d := by exact_mod_cast hd
  -- the radius of the stage `j`
  have hlogR : ∀ j : ℕ, Real.log (stageR j) = (2 : ℝ) ^ j * L := by
    intro j
    unfold stageR
    rw [Real.log_pow]
    push_cast
    ring
  -- `2^J log 2 ≤ 2 log R + log 2`: the stage before `J` fails
  have hJ : (2 : ℝ) ^ J * L ≤ 2 * Real.log R + L := by
    rcases Nat.eq_zero_or_eq_succ_pred J with h0 | hs
    · rw [h0, pow_zero, one_mul]; linarith
    · have hlt : J.pred < J := by omega
      have hmin : ¬ R ≤ stageR (J.pred) := Nat.find_min (exists_stageR_ge R) hlt
      push Not at hmin
      have hpos : 0 < stageR J.pred := by unfold stageR; positivity
      have := Real.log_lt_log hpos hmin
      rw [hlogR] at this
      rw [hs, pow_succ]
      nlinarith
  -- each stage
  have hterm : ∀ j : ℕ, (stageN d j : ℝ) ≤ 2 * (d : ℝ) * ((d : ℝ) + 1) * (L + (2 : ℝ) ^ j * L) + 2 := by
    intro j
    have hpos : 0 < stageR j := by unfold stageR; positivity
    have hl : Real.log (2 * stageR j) = L + (2 : ℝ) ^ j * L := by
      rw [Real.log_mul (by norm_num) hpos.ne', hlogR]
    unfold stageN
    rw [hl]
    have hx : 0 ≤ 2 * (d : ℝ) * ((d : ℝ) + 1) * (L + (2 : ℝ) ^ j * L) := by positivity
    have := Nat.ceil_lt_add_one hx
    push_cast
    linarith
  have hgeom : ∀ n : ℕ, ∑ j ∈ Finset.range n, (2 : ℝ) ^ j = 2 ^ n - 1 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ, ih, pow_succ]; ring
  have hsum : ∑ j ∈ Finset.range (J + 1), (stageN d j : ℝ) ≤
      2 * (d : ℝ) * ((d : ℝ) + 1) * L * ((J + 1 : ℝ) + (2 ^ (J + 1) - 1)) + 2 * (J + 1 : ℝ) := by
    calc ∑ j ∈ Finset.range (J + 1), (stageN d j : ℝ)
        ≤ ∑ j ∈ Finset.range (J + 1), (2 * (d : ℝ) * ((d : ℝ) + 1) * (L + (2 : ℝ) ^ j * L) + 2) :=
          Finset.sum_le_sum fun j _ => hterm j
      _ = 2 * (d : ℝ) * ((d : ℝ) + 1) * L * ((J + 1 : ℝ) + (2 ^ (J + 1) - 1)) + 2 * (J + 1 : ℝ) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.sum_mul, hgeom]
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring
  have hJ2 : (J + 1 : ℝ) ≤ 2 ^ J := by exact_mod_cast Nat.lt_two_pow_self (n := J)
  set X : ℝ := 2 ^ J with hX
  have hXpos : 0 < X := by positivity
  have hDD : (d : ℝ) * ((d : ℝ) + 1) ≤ 2 * (d : ℝ) ^ 2 := by nlinarith
  have hA : 0 ≤ 2 * Real.log R + L := by linarith
  have h2 : 2 * (d : ℝ) * ((d : ℝ) + 1) * L * ((J + 1 : ℝ) + (2 ^ (J + 1) - 1)) ≤
      12 * (d : ℝ) ^ 2 * (2 * Real.log R + L) := by
    have e : (2 : ℝ) ^ (J + 1) = 2 * X := by rw [hX, pow_succ]; ring
    rw [e]
    have h3 : (J + 1 : ℝ) + (2 * X - 1) ≤ 3 * X := by linarith
    calc 2 * (d : ℝ) * ((d : ℝ) + 1) * L * ((J + 1 : ℝ) + (2 * X - 1))
        ≤ 2 * (d : ℝ) * ((d : ℝ) + 1) * L * (3 * X) := by gcongr
      _ = 6 * ((d : ℝ) * ((d : ℝ) + 1)) * (X * L) := by ring
      _ ≤ 6 * (2 * (d : ℝ) ^ 2) * (2 * Real.log R + L) := by gcongr
      _ = 12 * (d : ℝ) ^ 2 * (2 * Real.log R + L) := by ring
  have h4 : 2 * (J + 1 : ℝ) ≤ 3 * (d : ℝ) ^ 2 * (2 * Real.log R + L) := by
    have h5 : 0.69 * X ≤ X * L := by nlinarith
    have h6 : 2 * X ≤ 3 * (2 * Real.log R + L) := by nlinarith
    have h7 : (1 : ℝ) ≤ (d : ℝ) ^ 2 := by nlinarith
    nlinarith
  rw [hlog2R]
  nlinarith

end AdversarialBco.Conj1Poly
