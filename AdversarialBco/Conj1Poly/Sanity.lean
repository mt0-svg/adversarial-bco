/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.StatementConj1Poly

@[expose] public section

/-!
# Sanity checks of the polytope definitions (AdversarialBco/StatementConj1Poly.lean)

* The cube `[-1, 1]^d`, given by the `2 d` rows `± e_j` with right-hand sides `1` (`cubeA`, `cubeB`, `mem_cube_iff`),
  has height `1` (`cube_height`), contains the closed unit ball (`cube_ball`) and has diameter at most `2 d`
  (`cube_diam`): the hypotheses on a polytope are satisfiable together, in every dimension.
* The noiseless game satisfies the noise hypothesis (`noiseOK_dirac`).
* A polytope is convex (`convex_polytope`).
-/

open MeasureTheory ProbabilityTheory

namespace AdversarialBco.RealRAM.Conj1PolySanity

variable {d : ℕ}

/-! ## The cube `[-1, 1]^d` -/

/-- The rows `e_j` (`i < d`) and `- e_{i - d}` (`d ≤ i < 2 d`). -/
def cubeA (d : ℕ) : Matrix (Fin (2 * d)) (Fin d) ℚ := fun i j =>
  if i.val < d then (if j.val = i.val then 1 else 0) else (if j.val + d = i.val then -1 else 0)

/-- The right-hand sides `1`. -/
def cubeB (d : ℕ) : Fin (2 * d) → ℚ := fun _ => 1

theorem cube_row_lt (x : E d) (i : Fin (2 * d)) (h : i.val < d) :
    ∑ j, ((cubeA d i j : ℚ) : ℝ) * x j = x ⟨i.val, h⟩ := by
  rw [Finset.sum_eq_single ⟨i.val, h⟩]
  · simp [cubeA, h]
  · intro j _ hj
    have : j.val ≠ i.val := fun e => hj (Fin.ext e)
    simp [cubeA, h, this]
  · simp

theorem cube_row_ge (x : E d) (i : Fin (2 * d)) (h : d ≤ i.val) :
    ∑ j, ((cubeA d i j : ℚ) : ℝ) * x j = - x ⟨i.val - d, by omega⟩ := by
  rw [Finset.sum_eq_single ⟨i.val - d, by omega⟩]
  · have h1 : ¬ i.val < d := by omega
    have h2 : i.val - d + d = i.val := by omega
    simp [cubeA, h1, h2]
  · intro j _ hj
    have h1 : ¬ i.val < d := by omega
    have : j.val + d ≠ i.val := fun e => hj (Fin.ext (by simp; omega))
    simp [cubeA, h1, this]
  · simp

theorem mem_cube_iff (x : E d) : x ∈ polytope (cubeA d) (cubeB d) ↔ ∀ j, |x j| ≤ 1 := by
  constructor
  · intro hx j
    have h1 := hx ⟨j.val, by omega⟩
    have h2 := hx ⟨j.val + d, by omega⟩
    rw [cube_row_lt x _ j.2] at h1
    rw [cube_row_ge x _ (by simp)] at h2
    simp only [cubeB, Rat.cast_one] at h1 h2
    have e : (⟨(⟨j.val + d, by omega⟩ : Fin (2 * d)).val - d, by simp⟩ : Fin d) = j := Fin.ext (by simp)
    rw [e] at h2
    exact abs_le.2 ⟨by linarith, h1⟩
  · intro hx i
    simp only [cubeB, Rat.cast_one]
    rcases lt_or_ge i.val d with h | h
    · rw [cube_row_lt x i h]; exact (abs_le.1 (hx _)).2
    · rw [cube_row_ge x i h]; linarith [(abs_le.1 (hx ⟨i.val - d, by omega⟩)).1]

theorem cube_height (d : ℕ) : HeightLE (cubeA d) (cubeB d) 1 := by
  refine ⟨fun i j => ?_, fun i => by simp [cubeB]⟩
  unfold cubeA
  split_ifs <;> simp

theorem cube_ball (d : ℕ) : Metric.closedBall (0 : E d) 1 ⊆ polytope (cubeA d) (cubeB d) := by
  intro x hx
  rw [mem_cube_iff]
  intro j
  have h := PiLp.norm_apply_le x j
  rw [Metric.mem_closedBall, dist_zero_right] at hx
  rw [Real.norm_eq_abs] at h
  linarith

theorem cube_diam (hd : 1 ≤ d) :
    ∀ x ∈ polytope (cubeA d) (cubeB d), ∀ y ∈ polytope (cubeA d) (cubeB d), dist x y ≤ ((2 * d : ℕ) : ℝ) := by
  intro x hx y hy
  rw [mem_cube_iff] at hx hy
  rw [EuclideanSpace.dist_eq, Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  have hb : ∀ j : Fin d, dist (x j) (y j) ^ 2 ≤ 4 := by
    intro j
    rw [Real.dist_eq]
    have h1 := abs_le.1 (hx j)
    have h2 := abs_le.1 (hy j)
    have : |x j - y j| ≤ 2 := abs_le.2 ⟨by linarith, by linarith⟩
    nlinarith [abs_nonneg (x j - y j)]
  calc ∑ j, dist (x j) (y j) ^ 2 ≤ ∑ _j : Fin d, (4 : ℝ) := Finset.sum_le_sum fun j _ => hb j
    _ = 4 * d := by simp; ring
    _ ≤ ((2 * d : ℕ) : ℝ) ^ 2 := by
      have : (1 : ℝ) ≤ d := by exact_mod_cast hd
      push_cast; nlinarith

/-! ## The noise and the polytope -/

theorem pastNoise_le (t : ℕ) : pastNoise t ≤ (inferInstance : MeasurableSpace (ℕ → ℝ)) :=
  (Measurable.of_eval fun i : Fin t => measurable_pi_apply (i : ℕ)).comap_le

/-- The noiseless game satisfies the noise hypothesis. -/
theorem noiseOK_dirac : NoiseOK (Measure.dirac (0 : ℕ → ℝ)) := by
  refine ⟨inferInstance, fun t => ⟨?_, ?_, ?_⟩⟩
  · have hm : Measurable fun ε : ℕ → ℝ => Real.exp (ε t ^ 2) :=
      Real.measurable_exp.comp ((measurable_pi_apply t).pow_const 2)
    exact integrable_dirac' hm.stronglyMeasurable enorm_lt_top
  · have h : (fun ε : ℕ → ℝ => ε t) =ᵐ[Measure.dirac 0] 0 := by
      filter_upwards [ae_eq_dirac' (a := (0 : ℕ → ℝ)) (measurable_pi_apply t)] with ε hε
      simpa using hε
    exact (condExp_congr_ae h).trans (by rw [condExp_zero])
  · have hm : Measurable fun ε : ℕ → ℝ => Real.exp (ε t ^ 2) :=
      Real.measurable_exp.comp ((measurable_pi_apply t).pow_const 2)
    have h : (fun ε : ℕ → ℝ => Real.exp (ε t ^ 2)) =ᵐ[Measure.dirac 0] fun _ => (1 : ℝ) := by
      filter_upwards [ae_eq_dirac' (a := (0 : ℕ → ℝ)) hm] with ε hε
      simpa using hε
    filter_upwards [condExp_congr_ae (m := pastNoise t) h] with ε hε
    rw [hε, condExp_const (pastNoise_le t)]
    norm_num

/-- A polytope is convex. -/
theorem convex_polytope {m : ℕ} (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) : Convex ℝ (polytope A b) := by
  have : polytope A b = ⋂ i, {x : E d | ∑ j, (A i j : ℝ) * x j ≤ (b i : ℝ)} := by
    ext x; simp [polytope]
  rw [this]
  refine convex_iInter fun i => ?_
  intro x hx y hy a c ha hc hac
  simp only [Set.mem_ofPred_eq, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at hx hy ⊢
  calc ∑ j, (A i j : ℝ) * (a * x j + c * y j) = a * ∑ j, (A i j : ℝ) * x j + c * ∑ j, (A i j : ℝ) * y j := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]; congr 1; ext j; ring
    _ ≤ a * (b i : ℝ) + c * (b i : ℝ) := by gcongr
    _ = (b i : ℝ) := by rw [← add_mul, hac, one_mul]

#print axioms cube_height
#print axioms cube_ball
#print axioms cube_diam
#print axioms mem_cube_iff
#print axioms noiseOK_dirac
#print axioms convex_polytope

end AdversarialBco.RealRAM.Conj1PolySanity
