/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.StatementConj1Bit
public import AdversarialBco.Conj1Poly.Sanity
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.Distributions.Bernoulli

@[expose] public section

/-!
# Sanity checks of the statement `TheoremConj1UpperBit` (StatementConj1Bit.lean, StatementBitRAM.lean)

The theorems stated in the sanity block of the challenge (ChallengeConj1Bit.lean) are proved here under the same
names.

* The coins: `coinLaw` is a probability measure (`isProbabilityMeasure_coinLaw`), and so is the stream
  (`isProbabilityMeasure_coinStream`), so `Measure.infinitePi` is the true product and does not take its junk value
  `0`.
* The input is in the memory as the docstring says: `d`, `n`, `m` in the cells `0`, `1`, `2` (`inputMem_small`), the
  numerator and the denominator in lowest terms of the entry `(i, j)` of the rows `(A i, b i)` in the cells
  `3 + 2 e` and `4 + 2 e`, `e = (d + 1) i + j` (`inputMem_cell`, `inputMem_num`, `inputMem_den`), `0` below `0` and
  above the data (`inputMem_neg`, `inputMem_high`).
* The hypotheses hold together in every dimension `d ≥ 1`: the cube `[-1, 1]^d` of
  AdversarialBco/Conj1Poly/Sanity.lean with `m = 2 d` rows, `M = 1`, `n = 2 d`, the seed space `Bool` with the fair
  coin law, and the adversary that plays the constant loss `1` or `0` according to its seed (`hyps_satisfiable`, and
  `hyps_satisfiable_exists`, in the challenge, with a strategy that depends on the seed).
* The adversary class: a deterministic strategy is a randomised adversary on the seed space `Unit` as soon as its
  losses are admissible, with no measurability asked (`randAdv_unit`, in the challenge).
* The existential is not witnessed for free: the empty program fails the cost clause on every input with `n ≥ 1`
  (`nil_not_costOKBit`, in the challenge).
* The feedback the program reads is the loss of the regret: the run against a strategy is the run of the machine in
  the fixed world of the losses that the strategy chose on that run, `lossAd σ 0 (playedBit ...)`, the losses of
  `regretPts` in the statement (`runBit_eq_run`). The loss of round `t` reads the points before `t` only
  (`lossAd_prefix`), a step reads the world through the last feedback and the coins only (`step_congr`), and the point
  of a round, once played, never changes (`runBit_mono`, `playedBit_eq`).
* The space clause does not clash with the input: the input, which is in the memory and counted, has space at most
  `(3 + 2 (d + 1) m) (len (3 + 2 (d + 1) m) + len d + len n + len m + len M)` (`input_space_nat`).
-/

open MeasureTheory ProbabilityTheory

namespace AdversarialBco.BitRAM.Conj1BitSanity

open RealRAM (Strategy Strats lossAd obsAd polytope HeightLE)

/-! ## The coins -/

instance isProbabilityMeasure_coinLaw : IsProbabilityMeasure coinLaw := by
  constructor
  simp only [coinLaw, Measure.smul_apply, Measure.add_apply, measure_univ, smul_eq_mul]
  rw [one_add_one_eq_two, ENNReal.inv_mul_cancel] <;> norm_num

instance isProbabilityMeasure_coinStream : IsProbabilityMeasure coinStream := by
  unfold coinStream; infer_instance

variable {d : ℕ}

/-! ## The input -/

section Input

variable {n m : ℕ} (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ)

theorem inputMem_small : inputMem d n m A b 0 = d ∧ inputMem d n m A b 1 = n ∧ inputMem d n m A b 2 = m := by
  simp [inputMem]

theorem inputMem_neg (c : ℤ) (hc : c < 0) : inputMem d n m A b c = 0 := by
  unfold inputMem
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), dite_eq_right (by omega)]

theorem entry_decode (i : Fin m) (j : ℕ) (hj : j ≤ d) :
    ((d + 1) * i + j) / (d + 1) = i ∧ ((d + 1) * i + j) % (d + 1) = j := by
  constructor
  · rw [Nat.add_comm, Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt (by omega), zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

/-- The cell `3 + 2 e + r`, `e = (d + 1) i + j`, holds the numerator in lowest terms of the entry `(i, j)` for `r = 0`
and its denominator for `r = 1`. -/
theorem inputMem_cell (i : Fin m) (j : ℕ) (hj : j ≤ d) (r : ℕ) (hr : r < 2) :
    inputMem d n m A b (3 + 2 * ((d + 1) * i + j) + r : ℕ) =
      if r = 0 then (entry A b i j).num else ((entry A b i j).den : ℤ) := by
  obtain ⟨h3, h4⟩ := entry_decode i j hj
  have hc : ((3 + 2 * ((d + 1) * i + j) + r : ℕ) : ℤ) - 3 = ((2 * ((d + 1) * i + j) + r : ℕ) : ℤ) := by
    push_cast; ring
  have hdiv : (2 * ((d + 1) * i + j) + r) / 2 = (d + 1) * i + j := by omega
  have hmod : (2 * ((d + 1) * i + j) + r) % 2 = r := by omega
  unfold inputMem
  simp only [hc, Int.toNat_natCast, hdiv, hmod, h3, h4]
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), dite_eq_left ⟨by omega, i.2⟩]

/-- The numerator, in lowest terms, of the entry `(i, j)` is in the cell `3 + 2 ((d + 1) i + j)`. -/
theorem inputMem_num (i : Fin m) (j : ℕ) (hj : j ≤ d) :
    inputMem d n m A b (3 + 2 * ((d + 1) * i + j) : ℕ) = (entry A b i j).num := by
  simpa using inputMem_cell (n := n) A b i j hj 0 (by norm_num)

/-- The denominator of the entry `(i, j)` is in the cell `4 + 2 ((d + 1) i + j)`. -/
theorem inputMem_den (i : Fin m) (j : ℕ) (hj : j ≤ d) :
    inputMem d n m A b (4 + 2 * ((d + 1) * i + j) : ℕ) = (entry A b i j).den := by
  have h := inputMem_cell (n := n) A b i j hj 1 (by norm_num)
  rw [ite_eq_right one_ne_zero] at h
  rw [← h]
  congr 2
  omega

/-- Above the data every cell is `0`. -/
theorem inputMem_high (c : ℤ) (hc : 3 + 2 * (d + 1) * m ≤ c) : inputMem d n m A b c = 0 := by
  unfold inputMem
  have h3 : 3 ≤ c := by
    have : (0 : ℤ) ≤ 2 * (d + 1) * m := by positivity
    omega
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), dite_eq_right]
  rintro ⟨-, h⟩
  have hc' : 3 + 2 * (((d + 1) * m : ℕ) : ℤ) ≤ c := by push_cast; linarith
  have h2 : (d + 1) * m ≤ (c - 3).toNat / 2 := by
    generalize (d + 1) * m = K at hc' ⊢; omega
  have h4 : m ≤ (c - 3).toNat / 2 / (d + 1) := by
    rw [Nat.le_div_iff_mul_le (by omega), mul_comm]; exact h2
  omega

end Input

/-! ## The hypotheses -/

/-- The adversary that plays, in every round, the constant loss `1` if its seed is `true` and `0` otherwise. -/
def coinFlipStrat (d : ℕ) : Bool → Strategy d := fun θ _ _ _ _ => if θ then 1 else 0

theorem randAdv_coinFlip {K : Set (E d)} (hK : Convex ℝ K) (n : ℕ) : RandAdv K n (coinFlipStrat d) := by
  intro t _ q
  refine ⟨fun θ => ⟨?_, fun y _ => ?_⟩, fun y _ => measurable_of_countable _⟩
  · exact convexOn_const _ hK
  · cases θ <;> simp [lossAd, coinFlipStrat]

/-- The hypotheses of `TheoremConj1UpperBit` hold together in every dimension `d ≥ 1`: the cube `[-1, 1]^d` with
`m = 2 d` rows, `M = 1`, `n = 2 d`, the seed space `Bool` with the fair coin law, and the coin-flip adversary. -/
theorem hyps_satisfiable (hd : 1 ≤ d) :
    1 ≤ 2 * d ∧ HeightLE (RealRAM.Conj1PolySanity.cubeA d) (RealRAM.Conj1PolySanity.cubeB d) 1 ∧
      (∃ c : E d, Metric.closedBall c 1 ⊆
        polytope (RealRAM.Conj1PolySanity.cubeA d) (RealRAM.Conj1PolySanity.cubeB d)) ∧
      (∀ x ∈ polytope (RealRAM.Conj1PolySanity.cubeA d) (RealRAM.Conj1PolySanity.cubeB d),
        ∀ y ∈ polytope (RealRAM.Conj1PolySanity.cubeA d) (RealRAM.Conj1PolySanity.cubeB d),
          dist x y ≤ ((2 * d : ℕ) : ℝ)) ∧
      IsProbabilityMeasure coinLaw ∧
      RandAdv (polytope (RealRAM.Conj1PolySanity.cubeA d) (RealRAM.Conj1PolySanity.cubeB d)) (2 * d)
        (coinFlipStrat d) :=
  ⟨by omega, RealRAM.Conj1PolySanity.cube_height d, ⟨0, RealRAM.Conj1PolySanity.cube_ball d⟩,
    RealRAM.Conj1PolySanity.cube_diam hd, inferInstance,
    randAdv_coinFlip (RealRAM.Conj1PolySanity.convex_polytope _ _) _⟩

/-- The hypotheses of `TheoremConj1UpperBit` are satisfiable in every dimension `d ≥ 1`, by a randomised adversary
whose strategy depends on its seed. -/
theorem hyps_satisfiable_exists (d : ℕ) (hd : 1 ≤ d) :
    ∃ (n m M : ℕ) (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ), 1 ≤ n ∧ HeightLE A b M ∧
      (∃ c : E d, Metric.closedBall c 1 ⊆ polytope A b) ∧
      (∀ x ∈ polytope A b, ∀ y ∈ polytope A b, dist x y ≤ n) ∧
      ∃ (ρ : Measure Bool) (σ : Bool → Strategy d), IsProbabilityMeasure ρ ∧ RandAdv (polytope A b) n σ ∧
        σ true ≠ σ false := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hyps_satisfiable hd
  refine ⟨2 * d, 2 * d, 1, _, _, h1, h2, h3, h4, coinLaw, coinFlipStrat d, h5, h6, fun h => ?_⟩
  have := congrFun (congrFun (congrFun (congrFun h 0) Fin.elim0) Fin.elim0) 0
  simp [coinFlipStrat] at this

/-! ## The adversary class -/

/-- A deterministic strategy whose losses are admissible is a randomised adversary on the seed space `Unit`, with no
measurability asked of it. -/
theorem randAdv_unit {K : Set (E d)} {n : ℕ} (σ : Strategy d)
    (h : ∀ t < n, ∀ x o, AdmLoss K (σ t x o)) : RandAdv K n (fun _ : Unit => σ) :=
  fun t ht _ => ⟨fun _ => h t ht _ _, fun _ _ => measurable_of_countable _⟩

/-! ## The cost clause -/

/-- The empty program never plays, so it fails the cost clause on every input with `n ≥ 1`. -/
theorem nil_not_costOKBit (g : GameBit d) (s0 : State d) (n : ℕ) (B : ℝ) (h0 : s0.rounds < n) :
    ¬ CostOKBit [] g s0 n B := by
  have hrun : ∀ k, runBit [] g s0 k = s0 := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [runBit, Function.iterate_succ_apply', ← runBit, ih]; simp [stepBit, step]
  intro h
  obtain ⟨j, hj, -⟩ := h 0 (by rw [hrun]; exact h0)
  rw [hrun, hrun] at hj
  exact lt_irrefl _ hj

/-! ## The run against a strategy -/

/-- The observations of the rounds before `t` read the points of those rounds only. -/
theorem obsAd_prefix (σ : Strategy d) (ε : ℕ → ℝ) {x y : ℕ → E d} :
    ∀ t, (∀ i < t, x i = y i) → obsAd σ ε x t = obsAd σ ε y t
  | 0, _ => rfl
  | t + 1, h => by
    have ih := obsAd_prefix σ ε t fun i hi => h i (by omega)
    have hx : (fun i : Fin t => x i) = fun i : Fin t => y i := funext fun i => h i (by omega)
    simp only [obsAd, ih, hx, h t (by omega)]

/-- The loss of round `t` reads the points of the rounds before `t` only. -/
theorem lossAd_prefix (σ : Strategy d) (ε : ℕ → ℝ) {x y : ℕ → E d} (t : ℕ) (h : ∀ i < t, x i = y i) :
    lossAd σ ε x t = lossAd σ ε y t := by
  have hx : (fun i : Fin t => x i) = fun i : Fin t => y i := funext fun i => h i i.2
  simp only [lossAd, obsAd_prefix σ ε t h, hx]

/-- A step reads the world through the feedback of the last round played and the coins only. -/
theorem step_congr (P : List Instr) {w w' : World d} (s : State d) (hcs : w.cs = w'.cs)
    (hf : feedback w s = feedback w' s) : step P w s = step P w' s := by
  unfold step reading
  rw [hcs, hf]

/-- A step never decreases the number of rounds and never changes the point of a round already played. -/
theorem step_rounds_pts (P : List Instr) (w : World d) (s : State d) :
    s.rounds ≤ (step P w s).rounds ∧ ∀ i < s.rounds, (step P w s).pts i = s.pts i := by
  unfold step
  split
  · exact ⟨le_rfl, fun _ _ => rfl⟩
  · rename_i ins _
    cases ins <;> simp
    intro i hi
    rw [Function.update_of_ne (by omega)]

theorem runBit_succ (P : List Instr) (g : GameBit d) (s0 : State d) (k : ℕ) :
    runBit P g s0 (k + 1) = stepBit P g (runBit P g s0 k) := by
  rw [runBit, Function.iterate_succ_apply', ← runBit]

theorem runBit_mono (P : List Instr) (g : GameBit d) (s0 : State d) {k k' : ℕ} (hk : k ≤ k') :
    (runBit P g s0 k).rounds ≤ (runBit P g s0 k').rounds ∧
      ∀ i < (runBit P g s0 k).rounds, (runBit P g s0 k').pts i = (runBit P g s0 k).pts i := by
  induction k', hk using Nat.le_induction with
  | base => exact ⟨le_rfl, fun _ _ => rfl⟩
  | succ k' hk ih =>
    obtain ⟨h1, h2⟩ := step_rounds_pts P (g.world (runBit P g s0 k').pts) (runBit P g s0 k')
    rw [runBit_succ]
    refine ⟨ih.1.trans h1, fun i hi => ?_⟩
    rw [stepBit, h2 i (lt_of_lt_of_le hi ih.1), ih.2 i hi]

/-- The point of a round already played at step `k` is the point `playedBit` gives for that round. -/
theorem playedBit_eq (P : List Instr) (g : GameBit d) (s0 : State d) (k i : ℕ)
    (hi : i < (runBit P g s0 k).rounds) : playedBit P g s0 i = toE ((runBit P g s0 k).pts i) := by
  have h : ∃ k, i < (runBit P g s0 k).rounds := ⟨k, hi⟩
  simp only [playedBit, h, ↓reduceDIte]
  rw [(runBit_mono P g s0 (Nat.find_min' h hi)).2 i (Nat.find_spec h)]

/-- The run against a strategy is the run of the machine in the fixed world of the losses that the strategy chose on
that run, those of the regret: the feedback the program reads in round `t` is the loss of the regret at the point of
round `t`. -/
theorem runBit_eq_run (P : List Instr) (σ : Strategy d) (cs : ℕ → Bool) (s0 : State d) (k : ℕ) :
    runBit P ⟨σ, cs⟩ s0 k = run P ⟨lossAd σ 0 (playedBit P ⟨σ, cs⟩ s0), cs⟩ s0 k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [runBit_succ, run, Function.iterate_succ_apply', ← run, ← ih]
    refine step_congr P _ rfl ?_
    unfold feedback
    split
    · rfl
    · rename_i h0
      have := lossAd_prefix σ 0 (x := fun i => toE ((runBit P ⟨σ, cs⟩ s0 k).pts i))
        (y := playedBit P ⟨σ, cs⟩ s0) ((runBit P ⟨σ, cs⟩ s0 k).rounds - 1)
        fun i hi => (playedBit_eq P ⟨σ, cs⟩ s0 k i (by omega)).symm
      simp only [GameBit.world]
      rw [this]

/-! ## The space clause -/

theorem len_mono {a b : ℤ} (h : a.natAbs ≤ b.natAbs) : len a ≤ len b := Nat.size_le_size h

/-- The entries of the input are bounded by the height. -/
theorem entry_height {m M : ℕ} {A : Matrix (Fin m) (Fin d) ℚ} {b : Fin m → ℚ} (hH : HeightLE A b M)
    (i : Fin m) (j : ℕ) : (entry A b i j).num.natAbs ≤ M ∧ (entry A b i j).den ≤ M := by
  unfold entry
  split
  · exact hH.1 i _
  · exact hH.2 i

/-- Every cell of the input has length at most `len d + len n + len m + len M`. -/
theorem len_inputMem_le {n m M : ℕ} {A : Matrix (Fin m) (Fin d) ℚ} {b : Fin m → ℚ} (hH : HeightLE A b M)
    (c : ℤ) : len (inputMem d n m A b c) ≤ len d + len n + len m + len M := by
  unfold inputMem
  split_ifs with h0 h1 h2 h3 h4
  · omega
  · omega
  · omega
  · have := len_mono (a := (entry A b ⟨(c - 3).toNat / 2 / (d + 1), h3.2⟩ ((c - 3).toNat / 2 % (d + 1))).num)
      (b := (M : ℤ)) (by rw [Int.natAbs_natCast]; exact (entry_height hH _ _).1)
    omega
  · have := len_mono (a := ((entry A b ⟨(c - 3).toNat / 2 / (d + 1), h3.2⟩ ((c - 3).toNat / 2 % (d + 1))).den : ℤ))
      (b := (M : ℤ)) (by rw [Int.natAbs_natCast, Int.natAbs_natCast]; exact (entry_height hH _ _).2)
    omega
  · simp [len]

/-- The cells in use of the input are among `0, ..., 2 + 2 (d + 1) m`. -/
theorem inputMem_support {n m : ℕ} (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) (c : ℤ)
    (hc : inputMem d n m A b c ≠ 0) : c ∈ Finset.Ico (0 : ℤ) (3 + 2 * (d + 1) * m) := by
  rw [Finset.mem_Ico]
  constructor
  · by_contra h; exact hc (inputMem_neg A b c (by omega))
  · by_contra h; exact hc (inputMem_high A b c (by omega))

/-- The space of the input: `N (len N + len d + len n + len m + len M)` at most, `N = 3 + 2 (d + 1) m`. -/
theorem input_space_nat {n m M : ℕ} {A : Matrix (Fin m) (Fin d) ℚ} {b : Fin m → ℚ} (hH : HeightLE A b M)
    (F : Finset ℤ) (hF : ∀ c ∈ F, inputMem d n m A b c ≠ 0) :
    ∑ c ∈ F, (len c + len (inputMem d n m A b c)) ≤
      (3 + 2 * (d + 1) * m) * (len ((3 + 2 * (d + 1) * m : ℕ) : ℤ) + (len d + len n + len m + len M)) := by
  have hsub : F ⊆ Finset.Ico (0 : ℤ) (3 + 2 * (d + 1) * m) := fun c hc => inputMem_support A b c (hF c hc)
  calc ∑ c ∈ F, (len c + len (inputMem d n m A b c))
      ≤ ∑ c ∈ Finset.Ico (0 : ℤ) (3 + 2 * (d + 1) * m), (len c + len (inputMem d n m A b c)) :=
        Finset.sum_le_sum_of_subset hsub
    _ ≤ (Finset.Ico (0 : ℤ) (3 + 2 * (d + 1) * m)).card *
          (len ((3 + 2 * (d + 1) * m : ℕ) : ℤ) + (len d + len n + len m + len M)) := by
        refine Finset.sum_le_card_nsmul _ _ _ fun c hc => ?_
        rw [Finset.mem_Ico] at hc
        have h1 : len c ≤ len ((3 + 2 * (d + 1) * m : ℕ) : ℤ) := len_mono (by push_cast; omega)
        have h2 := len_inputMem_le (n := n) hH c
        omega
    _ = (3 + 2 * (d + 1) * m) * (len ((3 + 2 * (d + 1) * m : ℕ) : ℤ) + (len d + len n + len m + len M)) := by
        rw [Int.card_Ico]; congr 1

end AdversarialBco.BitRAM.Conj1BitSanity
