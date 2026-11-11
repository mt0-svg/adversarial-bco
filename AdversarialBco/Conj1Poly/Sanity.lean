/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.StatementConj1Poly

@[expose] public section

/-!
# Sanity checks of the statement `TheoremConj1UpperPoly` (AdversarialBco/StatementConj1Poly.lean)

* The hypotheses are satisfiable together, in every dimension: the cube `[-1, 1]^d`, given by the `2 d` rows `± e_j`
  with right-hand sides `1` (`cubeA`, `cubeB`, `mem_cube_iff`), has height `1` (`cube_height`), contains the closed
  unit ball (`cube_ball`) and has diameter at most `2 d` (`cube_diam`); with `n = 2 d`, the zero strategy (in the class,
  `zeroStrat_mem`) and the noiseless game (`noiseOK_dirac`), every hypothesis holds (`hyps_satisfiable`).
* Under the hypotheses `m ≥ 1` and `M ≥ 1` (`one_le_m`, `one_le_M`), so `log (2 M) > 0` and `d m L log (2 M) > 0`
  (`bounds_pos`): the cost bounds are not `0` by a junk value.
* The data is read from memory: `initPoly` holds `d`, `n`, `m` in the registers `0`, `1`, `2` and `0` in every other
  register (`initPoly_nreg`), `δ` in the cell `2`, no radius in the cells `0`, `1` (`initPoly_mem_small`), the entry
  `A i j` in the cell `3 + (d + 1) i + j` and `b i` in the cell `3 + (d + 1) i + d` (`initPoly_mem_A`,
  `initPoly_mem_b`), `0` above the rows (`initPoly_mem_high`); two polytopes with the same initial state have the same
  data (`initPoly_injective`). The body of the world is inert for a program with no query: the run, the points played
  and the cost clause are the same for every set in the field `K` of the world (`step_K_irrel`, `runAd_K_irrel`,
  `playedAd_K_irrel`, `costOKAd_K_irrel`). So the polytope reaches the program through `initPoly` alone.
* The existential is not witnessed for free: the empty program has no query (`queryFree_nil`) and fails the cost
  clause on every input (`nil_not_costOKAd`); a program with a query is excluded (`not_queryFree_query`); and for
  every program and every strategy the cost clause forces every round `t < n` to be played from `initPoly`
  (`costOKAd_all_rounds`), so it cannot hold vacuously.
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

/-! ## The strategy and the noise -/

/-- The zero strategy. -/
def zeroStrat (d : ℕ) : Strategy d := fun _ _ _ _ => 0

theorem zeroStrat_mem {K : Set (E d)} (hK : Convex ℝ K) (n : ℕ) : zeroStrat d ∈ Strats K n :=
  fun _ _ => ⟨fun _ _ => ⟨convexOn_const 0 hK, fun _ _ => by simp [zeroStrat]⟩, fun _ _ => measurable_const⟩

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

/-- The hypotheses of `TheoremConj1UpperPoly` hold together in every dimension `d ≥ 1`: the cube `[-1, 1]^d` with
`m = 2 d` rows, `M = 1`, `n = 2 d`, `δ = 1/2`, the zero strategy and the noiseless game. -/
theorem hyps_satisfiable (hd : 1 ≤ d) :
    1 ≤ 2 * d ∧ (0 : ℝ) < 1 / 2 ∧ (1 / 2 : ℝ) < 1 ∧ HeightLE (cubeA d) (cubeB d) 1 ∧
      (∃ c : E d, Metric.closedBall c 1 ⊆ polytope (cubeA d) (cubeB d)) ∧
      (∀ x ∈ polytope (cubeA d) (cubeB d), ∀ y ∈ polytope (cubeA d) (cubeB d), dist x y ≤ ((2 * d : ℕ) : ℝ)) ∧
      zeroStrat d ∈ Strats (polytope (cubeA d) (cubeB d)) (2 * d) ∧ NoiseOK (Measure.dirac (0 : ℕ → ℝ)) :=
  ⟨by omega, by norm_num, by norm_num, cube_height d, ⟨0, cube_ball d⟩, cube_diam hd,
    zeroStrat_mem (convex_polytope _ _) _, noiseOK_dirac⟩

/-! ## No junk value in the bounds -/

/-- With no row the polytope is the whole space, whose diameter is unbounded: under the hypotheses `m ≥ 1`. -/
theorem one_le_m {m n : ℕ} (hd : 1 ≤ d) (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ)
    (hdiam : ∀ x ∈ polytope A b, ∀ y ∈ polytope A b, dist x y ≤ n) : 1 ≤ m := by
  by_contra hm
  have hm0 : m = 0 := by omega
  subst hm0
  have hall : ∀ x : E d, x ∈ polytope A b := fun x i => i.elim0
  have h := hdiam (EuclideanSpace.single ⟨0, hd⟩ ((n : ℝ) + 1)) (hall _) 0 (hall _)
  rw [dist_zero_right, PiLp.norm_single, Real.norm_eq_abs, abs_of_pos (by positivity)] at h
  linarith

/-- A bound on the heights of at least one entry is at least `1`, since a denominator is. -/
theorem one_le_M {m M : ℕ} (hm : 1 ≤ m) (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) (h : HeightLE A b M) :
    1 ≤ M :=
  le_trans (b ⟨0, hm⟩).den_pos (h.2 ⟨0, hm⟩).2

/-- Under the hypotheses the quantities raised to the power `k` in the cost bounds are positive. -/
theorem bounds_pos {m M n : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1)
    (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) (hH : HeightLE A b M)
    (hdiam : ∀ x ∈ polytope A b, ∀ y ∈ polytope A b, dist x y ≤ n) :
    0 < (d : ℝ) * m * Real.log (2 * d * n / δ) * Real.log (2 * M) ∧
      0 < (d : ℝ) * m * Real.log (2 * d * n / δ) := by
  have hm := one_le_m hd A b hdiam
  have hM := one_le_M hm A b hH
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hMR : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hL : 0 < Real.log (2 * d * n / δ) := by
    apply Real.log_pos
    rw [lt_div_iff₀ hδ]
    nlinarith
  have hl : 0 < Real.log (2 * M) := Real.log_pos (by linarith)
  constructor <;> positivity

/-! ## The data is read from memory -/

section Data

variable {n m : ℕ} {δ : ℝ} (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ)

theorem initPoly_nreg :
    (initPoly d n m δ A b).nreg 0 = d ∧ (initPoly d n m δ A b).nreg 1 = n ∧ (initPoly d n m δ A b).nreg 2 = m ∧
      ∀ r, 3 ≤ r → (initPoly d n m δ A b).nreg r = 0 := by
  refine ⟨rfl, rfl, rfl, fun r hr => ?_⟩
  simp only [initPoly]
  split_ifs <;> omega

/-- `δ` in the cell `2`; no radius in the cells `0` and `1`. -/
theorem initPoly_mem_small :
    (initPoly d n m δ A b).mem 0 = 0 ∧ (initPoly d n m δ A b).mem 1 = 0 ∧ (initPoly d n m δ A b).mem 2 = δ := by
  refine ⟨?_, ?_, rfl⟩ <;> simp [initPoly]

theorem initPoly_mem_A (i : Fin m) (j : Fin d) :
    (initPoly d n m δ A b).mem (3 + (d + 1) * i + j) = (A i j : ℝ) := by
  have hq : (3 + (d + 1) * i + j - 3) / (d + 1) = i := by
    rw [show 3 + (d + 1) * i + j - 3 = j + (d + 1) * i by omega, Nat.add_mul_div_left _ _ (by omega),
      Nat.div_eq_of_lt (by omega), zero_add]
  have hr : (3 + (d + 1) * i + j - 3) % (d + 1) = j := by
    rw [show 3 + (d + 1) * i + j - 3 = j + (d + 1) * i by omega, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt (by omega)]
  have hc : 3 + (d + 1) * i + j ≠ 2 := by omega
  have h : 3 ≤ 3 + (d + 1) * i + j ∧ (3 + (d + 1) * i + j - 3) / (d + 1) < m := ⟨by omega, by rw [hq]; exact i.2⟩
  have hj : (3 + (d + 1) * i + j - 3) % (d + 1) < d := by rw [hr]; exact j.2
  have e1 : (⟨(3 + (d + 1) * i + j - 3) / (d + 1), h.2⟩ : Fin m) = i := Fin.ext hq
  have e2 : (⟨(3 + (d + 1) * i + j - 3) % (d + 1), hj⟩ : Fin d) = j := Fin.ext hr
  simp only [initPoly, hc, ↓reduceIte, dite_eq_left_of_eq_true (eq_true h), dite_eq_left_of_eq_true (eq_true hj), e1, e2]

theorem initPoly_mem_b (i : Fin m) : (initPoly d n m δ A b).mem (3 + (d + 1) * i + d) = (b i : ℝ) := by
  have hq : (3 + (d + 1) * i + d - 3) / (d + 1) = i := by
    rw [show 3 + (d + 1) * i + d - 3 = d + (d + 1) * i by omega, Nat.add_mul_div_left _ _ (by omega),
      Nat.div_eq_of_lt (by omega), zero_add]
  have hr : (3 + (d + 1) * i + d - 3) % (d + 1) = d := by
    rw [show 3 + (d + 1) * i + d - 3 = d + (d + 1) * i by omega, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt (by omega)]
  have hc : 3 + (d + 1) * i + d ≠ 2 := by omega
  have h : 3 ≤ 3 + (d + 1) * i + d ∧ (3 + (d + 1) * i + d - 3) / (d + 1) < m := ⟨by omega, by rw [hq]; exact i.2⟩
  have hj : ¬ (3 + (d + 1) * i + d - 3) % (d + 1) < d := by rw [hr]; omega
  have e1 : (⟨(3 + (d + 1) * i + d - 3) / (d + 1), h.2⟩ : Fin m) = i := Fin.ext hq
  simp only [initPoly, hc, ↓reduceIte, dite_eq_left_of_eq_true (eq_true h), dite_eq_right_of_eq_false (eq_false hj), e1]

/-- Every cell above the rows holds `0`. -/
theorem initPoly_mem_high (c : ℕ) (hc : 3 + (d + 1) * m ≤ c) : (initPoly d n m δ A b).mem c = 0 := by
  have h2 : c ≠ 2 := by omega
  have h : ¬ (3 ≤ c ∧ (c - 3) / (d + 1) < m) := by
    rintro ⟨-, h⟩
    have : m ≤ (c - 3) / (d + 1) := (Nat.le_div_iff_mul_le (by omega)).2 (by rw [mul_comm]; omega)
    omega
  simp only [initPoly, h2, h, ↓reduceIte, ↓reduceDIte]

/-- Two polytopes with the same initial state have the same data. -/
theorem initPoly_injective (A' : Matrix (Fin m) (Fin d) ℚ) (b' : Fin m → ℚ)
    (h : initPoly d n m δ A b = initPoly d n m δ A' b') : A = A' ∧ b = b' := by
  refine ⟨funext fun i => funext fun j => ?_, funext fun i => ?_⟩
  · have := congrArg (fun s : State d => s.mem (3 + (d + 1) * i + j)) h
    simp only [initPoly_mem_A] at this
    exact_mod_cast this
  · have := congrArg (fun s : State d => s.mem (3 + (d + 1) * i + d)) h
    simp only [initPoly_mem_b] at this
    exact_mod_cast this

end Data

/-! ## The body of the world is inert for a program with no query -/

section Inert

theorem queryFree_nil : QueryFree [] := fun _ _ h => by simp at h

theorem not_queryFree_query : ¬ QueryFree [.query 0 0] := fun h => h 0 0 (by simp)

/-- A step of a program with no query does not read the body of the world. -/
theorem step_K_irrel {P : List Instr} (hP : QueryFree P) (K K' : Set (E d)) (f : ℕ → E d → ℝ) (ε gs : ℕ → ℝ)
    (s : State d) : step P ⟨K, f, ε, gs⟩ s = step P ⟨K', f, ε, gs⟩ s := by
  unfold step
  rcases hs : P[s.pc]? with _ | ins
  · rfl
  · have hmem : ins ∈ P := List.mem_of_getElem? hs
    cases ins with
    | query dst src => exact absurd hmem (hP dst src)
    | _ => rfl

theorem runAd_K_irrel {P : List Instr} (hP : QueryFree P) (K K' : Set (E d)) (σ : Strategy d) (ε gs : ℕ → ℝ)
    (s0 : State d) (k : ℕ) : runAd P ⟨K, σ, ε, gs⟩ s0 k = runAd P ⟨K', σ, ε, gs⟩ s0 k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [runAd, Function.iterate_succ_apply'] at ih ⊢
    rw [ih]
    exact step_K_irrel hP K K' _ ε gs _

theorem playedAd_K_irrel {P : List Instr} (hP : QueryFree P) (K K' : Set (E d)) (σ : Strategy d) (ε gs : ℕ → ℝ)
    (s0 : State d) : playedAd P ⟨K, σ, ε, gs⟩ s0 = playedAd P ⟨K', σ, ε, gs⟩ s0 := by
  have h : runAd P ⟨K, σ, ε, gs⟩ s0 = runAd P ⟨K', σ, ε, gs⟩ s0 := funext (runAd_K_irrel hP K K' σ ε gs s0)
  funext t
  unfold playedAd
  generalize runAd P ⟨K, σ, ε, gs⟩ s0 = r at h ⊢
  subst h
  rfl

theorem costOKAd_K_irrel {P : List Instr} (hP : QueryFree P) (K K' : Set (E d)) (σ : Strategy d) (ε gs : ℕ → ℝ)
    (s0 : State d) (n : ℕ) (B0 B : ℝ) : CostOKAd P ⟨K, σ, ε, gs⟩ s0 n B0 B ↔ CostOKAd P ⟨K', σ, ε, gs⟩ s0 n B0 B := by
  have h : runAd P ⟨K, σ, ε, gs⟩ s0 = runAd P ⟨K', σ, ε, gs⟩ s0 := funext (runAd_K_irrel hP K K' σ ε gs s0)
  unfold CostOKAd
  rw [h]

end Inert

/-! ## The cost clause is not vacuous -/

section Rounds

variable (P : List Instr) (g : GameAd d)

theorem stepAd_rounds (s : State d) : s.rounds ≤ (stepAd P g s).rounds ∧ (stepAd P g s).rounds ≤ s.rounds + 1 := by
  unfold stepAd step
  rcases P[s.pc]? with _ | ins
  · simp
  · cases ins <;> simp <;> split_ifs <;> simp

theorem runAd_succ (s0 : State d) (k : ℕ) : runAd P g s0 (k + 1) = stepAd P g (runAd P g s0 k) := by
  simp only [runAd, Function.iterate_succ_apply']

/-- Rounds go up one at a time: every value between is reached. -/
theorem reachAd (s0 : State d) (k t : ℕ) (h0 : s0.rounds ≤ t) (ht : t ≤ (runAd P g s0 k).rounds) :
    ∃ k' ≤ k, (runAd P g s0 k').rounds = t := by
  induction k with
  | zero => exact ⟨0, le_rfl, le_antisymm (by simpa [runAd] using ht) (by simpa [runAd] using h0) |>.symm⟩
  | succ k ih =>
    rcases Nat.lt_or_ge (runAd P g s0 k).rounds t with hlt | hge
    · have := (stepAd_rounds P g (runAd P g s0 k)).2
      rw [← runAd_succ] at this
      exact ⟨k + 1, le_rfl, (le_antisymm ht (by omega)).symm⟩
    · obtain ⟨k', hk', h⟩ := ih hge
      exact ⟨k', by omega, h⟩

/-- Under `CostOKAd`, every round `t < n` is played from `initPoly`, for every program and every strategy. -/
theorem costOKAd_all_rounds {n m : ℕ} {δ : ℝ} (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) (B0 B : ℝ)
    (h : CostOKAd P g (initPoly d n m δ A b) n B0 B) :
    ∀ t < n, ∃ k, t < (runAd P g (initPoly d n m δ A b) k).rounds := by
  intro t ht
  induction t with
  | zero => exact ⟨_, h.1⟩
  | succ t ih =>
    obtain ⟨k, hk⟩ := ih (by omega)
    obtain ⟨k', -, hk'⟩ := reachAd P g (initPoly d n m δ A b) k (t + 1) (by simp [initPoly]) hk
    exact ⟨k' + ⌈B⌉₊, h.2 k' (t + 1) (by omega) ht hk'⟩

/-- The empty program never plays: it fails the cost clause on every input. -/
theorem nil_not_costOKAd {n m : ℕ} {δ : ℝ} (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) (B0 B : ℝ) :
    ¬ CostOKAd [] g (initPoly d n m δ A b) n B0 B := by
  intro h
  have hrun : ∀ k, runAd [] g (initPoly d n m δ A b) k = initPoly d n m δ A b := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [runAd_succ, ih]; rfl
  have := h.1
  rw [hrun] at this
  simp [initPoly] at this

end Rounds

#print axioms cube_height
#print axioms cube_ball
#print axioms cube_diam
#print axioms mem_cube_iff
#print axioms zeroStrat_mem
#print axioms noiseOK_dirac
#print axioms convex_polytope
#print axioms hyps_satisfiable
#print axioms one_le_m
#print axioms one_le_M
#print axioms bounds_pos
#print axioms initPoly_nreg
#print axioms initPoly_mem_small
#print axioms initPoly_mem_A
#print axioms initPoly_mem_b
#print axioms initPoly_mem_high
#print axioms initPoly_injective
#print axioms queryFree_nil
#print axioms not_queryFree_query
#print axioms step_K_irrel
#print axioms runAd_K_irrel
#print axioms playedAd_K_irrel
#print axioms costOKAd_K_irrel
#print axioms costOKAd_all_rounds
#print axioms nil_not_costOKAd

end AdversarialBco.RealRAM.Conj1PolySanity
