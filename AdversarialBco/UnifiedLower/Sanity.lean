/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.StatementUnifiedLower
public import AdversarialBco.Unified.Sanity

@[expose] public section

/-!
# Sanity checks of the statements `TheoremLowerU` and `TheoremLowerUProg` (StatementUnifiedLower.lean)

The theorems stated in the challenge (ChallengeUnifiedLower.lean) next to `theoremLowerU` and `theoremLowerUProg` are
proved here under the same names, and Comparator checks them against it next to the two theorems
(config-unified-lower.json).

* The hypotheses of `TheoremLowerU` hold for every `d` and `n` at the closed unit ball about `0` with the constant
  learner on `Unit` (`lowerU_hyps_satisfiable`).
* The hypotheses of `TheoremLowerUProg` hold for every `d`, `n` and `δ` at the closed unit ball about the rational
  centre `0`, with its exact membership oracle, and for the program of three instructions `M (-1) := -2`,
  `play (-1)`, `jmp 1`, which plays the point `0` (the centre; the denominator cell `-2` holds `0`) in every round
  and reads no coin, with the windows `D = D' = 0`, on every world and for every oracle (`progU_hyps_satisfiable`).
* `MachineOK` is not met for free: the empty program fails it on every input with `n ≥ 1` (`nil_not_machineOK`).
* The conclusions are consistent, and their content is in the constants: at the threshold `0`, against the constant
  loss `1/2`, they hold for every learner (`lowerU_zero`) and for every program, with a closed-loop environment of
  `TheoremUnified` on the coin space (`progU_zero`).
* Every body of `TheoremUnified` is a body of `BodyU` (`bodyU_of_unified`), and `TheoremLowerU` contains the lower
  statement of v2.1 on the unit ball (`theoremConj1Lower_of_lowerU`).
* Corollary MATCH: `TheoremUnified` and `TheoremLowerUProg` give `CorollaryMatch`
  (`corollaryMatch_of_unified_lower`), whose upper part is `TheoremUnified` word for word
  (`theoremUnified_of_corollaryMatch`).
-/

open MeasureTheory ProbabilityTheory

namespace AdversarialBco.UnifiedLower.LowerSanity

open BitRAM BitRAMO Unified Unified.UnifiedSanity
open RealRAM (Strategy Strats regretPts)
open Lower (Learner IsLearnerAd regretAd)

/-! ## The constant loss -/

/-- The regret against a constant loss is `0` on a nonempty `K`. -/
theorem regretPts_const {d : ℕ} {K : Set (E d)} (hne : K.Nonempty) (c : ℝ) (x : ℕ → E d) (n : ℕ) :
    regretPts K (fun _ _ => c) x n = 0 := by
  unfold regretPts
  rw [show (fun y : E d => ∑ t ∈ Finset.range n, (fun (_ : ℕ) (_ : E d) => c) t y) =
      fun _ => ∑ t ∈ Finset.range n, c from rfl, hne.image_const, csInf_singleton, sub_self]

/-- The constant strategy `1/2`. -/
noncomputable def halfStrat (d : ℕ) : Strategy d := fun _ _ _ _ => 1 / 2

/-- The constant strategy `1/2` is a strategy of the lower bound on every convex `K`, at every inner radius
`r0 > 0`. -/
theorem halfStrat_mem {d : ℕ} {K : Set (E d)} (hK : Convex ℝ K) (n : ℕ) {r0 : ℝ} (hr0 : 0 < r0) :
    halfStrat d ∈ StratsLowU K n r0 := by
  refine ⟨fun t _ => ⟨fun x o => ⟨convexOn_const _ hK, fun y _ => ⟨by norm_num [halfStrat], by norm_num [halfStrat]⟩⟩,
    fun y _ => measurable_const⟩, fun t _ x o o' => ⟨rfl, fun y _ => ⟨by norm_num [halfStrat],
      by norm_num [halfStrat]⟩, fun y z => ?_⟩⟩
  simp only [halfStrat, sub_self, abs_zero]
  positivity

/-- The constant loss `c ∈ [0, 1]` with zero noise on the coin space is a noisy adversary, for every convex `K`, every
`n` and all windows. -/
theorem noisyAdv_const {d : ℕ} {K : Set (E d)} (hK : Convex ℝ K) (n : ℕ) (D D' : ℕ → ℕ) {c : ℝ} (hc0 : 0 ≤ c)
    (hc1 : c ≤ 1) : NoisyAdv K n D D' coinStream id (fun _ _ _ => c) (fun _ _ => 0) := by
  classical
  have hhist : ∀ L M N, histσ K (fun _ _ _ => c) (fun _ _ => 0) (id : (ℕ → Bool) → ℕ → Bool) L M N ≤
      coordσ (Set.Iio N) := by
    intro L M N
    refine sup_le (sup_le ?_ ?_) ?_
    · exact iSup₂_le fun _ _ => iSup₂_le fun _ _ => by simp
    · exact iSup₂_le fun _ _ => by simp
    · exact iSup₂_le fun j hj => le_coordσ hj
  have hfrom : ∀ N, coinsFrom (id : (ℕ → Bool) → ℕ → Bool) N ≤ coordσ (Set.Ici N) :=
    fun N => iSup₂_le fun j hj => le_coordσ hj
  have hind : ∀ L M N, Indep (coinsFrom (id : (ℕ → Bool) → ℕ → Bool) N)
      (histσ K (fun _ _ _ => c) (fun _ _ => 0) id L M N) coinStream := by
    intro L M N
    have h0 := coordσ_indep (ι := ℕ) (S := Set.Ici N) (T := Set.Iio N)
      (Set.disjoint_left.2 fun j h1 h2 => absurd (Set.mem_Iio.1 h2) (not_lt.2 (Set.mem_Ici.1 h1)))
    exact indep_of_indep_of_le_right (indep_of_indep_of_le_left h0 (hfrom N)) (hhist L M N)
  refine
    { prob := inferInstance
      coin_meas := measurable_id
      coin_law := Measure.map_id
      adm := fun _ _ _ => ⟨convexOn_const c hK, fun _ _ => ⟨hc0, hc1⟩⟩
      loss_meas := fun _ _ _ _ => measurable_const
      noise_meas := fun _ _ => measurable_const
      fresh_loss := fun t _ => hind _ _ _
      fresh_noise := fun t _ => hind _ _ _
      noise_int := fun _ _ => integrable_const _
      noise_mean := fun t _ => ?_
      noise_exp := fun t _ => ?_ }
  · have : (fun _ : ℕ → Bool => (0 : ℝ)) = 0 := rfl
    rw [this, condExp_zero]
  · have hle := (hhist (t + 1) t (D' t)).trans (coordσ_le (Set.Iio (D' t)))
    have : (fun ω : ℕ → Bool => Real.exp ((fun _ _ => (0 : ℝ)) t ω ^ 2)) = fun _ => (1 : ℝ) := by
      funext ω; simp
    rw [this, condExp_const hle]
    exact Filter.Eventually.of_forall fun _ => by norm_num

/-! ## `TheoremLowerU` -/

/-- The hypotheses of `TheoremLowerU` hold for every `d` and `n`: the closed unit ball about `0` (`r0 = R0 = 1`) and
the constant learner `0` on `Unit` with the Dirac measure. -/
theorem lowerU_hyps_satisfiable (d n : ℕ) :
    BodyU (Metric.closedBall (0 : E d) 1) 0 1 1 ∧ IsProbabilityMeasure (Measure.dirac ()) ∧
      IsLearnerAd (Metric.closedBall (0 : E d) 1) n (fun _ _ _ _ => 0 : Learner Unit d) :=
  ⟨⟨one_pos, le_rfl, isCompact_closedBall _ _, convex_closedBall _ _, subset_rfl, subset_rfl⟩, inferInstance,
    fun _ _ => ⟨measurable_const, fun _ _ _ => Metric.mem_closedBall_self zero_le_one⟩⟩

/-- The conclusions of `TheoremLowerU` hold at the threshold `0`, with probability `1`, for every learner on a convex
nonempty `K` and every `r0 > 0`: against the constant loss `1/2` the regret is `0`. -/
theorem lowerU_zero {d : ℕ} {K : Set (E d)} (hK : Convex ℝ K) (hne : K.Nonempty) (n : ℕ) {r0 : ℝ} (hr0 : 0 < r0)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (pol : Learner Ω d) :
    LowerMean K n r0 μ pol 0 ∧ LowerProb K n r0 μ pol 0 1 := by
  have h0' : ∀ ω, regretAd K (halfStrat d) (fun t => pol t ω) n = 0 := fun _ => regretPts_const hne _ _ _
  have h0 : (fun ω => regretAd K (halfStrat d) (fun t => pol t ω) n) = fun _ => 0 := funext h0'
  refine ⟨⟨halfStrat d, halfStrat_mem hK n hr0, ?_, ?_⟩, ⟨halfStrat d, halfStrat_mem hK n hr0, ?_, ?_⟩⟩
  · rw [h0]; exact integrable_const _
  · rw [h0]; simp
  · rw [h0]; exact measurable_const
  · simp [h0']

/-! ## `TheoremLowerUProg` -/

section Centre

variable {d : ℕ}

/-- The cost of the first instruction `M (-1) := -2`. -/
def costC : ℕ := 1 + len (-1) + len (-2)

/-- The cost of the instruction `play (-1)` once `M (-1) = -2`, the memory being `m` with `-2` stored in `-1`. -/
def costP (m : ℤ → ℤ) : ℕ := 1 + len (-1) + len (-2) + playCost d (Function.update m (-1) (-2)) (-2)

/-- The run of the program `M (-1) := -2`, `play (-1)`, `jmp 1` from a state at the counter `0` with no round, no coin,
no cost and `0` in the cell `-2`: after `2 j + 1` steps it is at the play with `j` rounds played, after `2 j + 2` steps
it has just played round `j`; the memory, the coins and the points stay fixed. -/
theorem centre_run (w : WorldO d) (s0 : State d) (h0 : s0.pc = 0) (hc : s0.coins = 0) (hr : s0.rounds = 0)
    (hp : s0.pts = fun _ _ => 0) (hcost : s0.cost = 0) (hm : s0.mem (-2) = 0) (j : ℕ) :
    runO [.base (.const (-1) (-2)), .base (.play (-1)), .base (.jmp 1)] w s0 (2 * j + 1) =
        ⟨1, Function.update s0.mem (-1) (-2), 0, j, fun _ _ => 0, costC + j * (costP (d := d) s0.mem + 1)⟩ ∧
      runO [.base (.const (-1) (-2)), .base (.play (-1)), .base (.jmp 1)] w s0 (2 * j + 2) =
        ⟨2, Function.update s0.mem (-1) (-2), 0, j + 1, fun _ _ => 0,
          costC + j * (costP (d := d) s0.mem + 1) + costP (d := d) s0.mem⟩ := by
  obtain ⟨pc, mem, coins, rounds, pts, cost⟩ := s0
  simp only at h0 hc hr hp hcost hm
  subst h0 hc hr hp hcost
  have hsucc : ∀ k, runO [.base (.const (-1) (-2)), .base (.play (-1)), .base (.jmp 1)] w ⟨0, mem, 0, 0,
      fun _ _ => 0, 0⟩ (k + 1) = stepO [.base (.const (-1) (-2)), .base (.play (-1)), .base (.jmp 1)] w
      (runO [.base (.const (-1) (-2)), .base (.play (-1)), .base (.jmp 1)] w ⟨0, mem, 0, 0, fun _ _ => 0, 0⟩ k) :=
    fun k => Function.iterate_succ_apply' _ _ _
  have hpt : ptAt d (Function.update mem (-1) (-2)) (Function.update mem (-1) (-2) (-1)) = fun _ => 0 := by
    funext i
    simp [ptAt, hm]
  have hplay : ∀ (r : ℕ) (c : ℕ), stepO [.base (.const (-1) (-2)), .base (.play (-1)), .base (.jmp 1)] w
      ⟨1, Function.update mem (-1) (-2), 0, r, fun _ _ => 0, c⟩ =
      ⟨2, Function.update mem (-1) (-2), 0, r + 1, fun _ _ => 0, c + costP (d := d) mem⟩ := by
    intro r c
    simp only [stepO, step, lowerP, lowerI, List.map_cons, List.map_nil, List.length_cons, List.length_nil]
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, State.mk.injEq, true_and]
    refine ⟨?_, ?_⟩
    · rw [hpt]; exact Function.update_eq_self_iff.2 rfl
    · simp [costP, Function.update_self]
  have hjmp : ∀ (r : ℕ) (c : ℕ), stepO [.base (.const (-1) (-2)), .base (.play (-1)), .base (.jmp 1)] w
      ⟨2, Function.update mem (-1) (-2), 0, r, fun _ _ => 0, c⟩ =
      ⟨1, Function.update mem (-1) (-2), 0, r, fun _ _ => 0, c + 1⟩ := by
    intro r c
    simp [stepO, step, lowerP, lowerI]
  have hconst : stepO [.base (.const (-1) (-2)), .base (.play (-1)), .base (.jmp 1)] w
      ⟨0, mem, 0, 0, fun _ _ => 0, 0⟩ = ⟨1, Function.update mem (-1) (-2), 0, 0, fun _ _ => 0, costC⟩ := by
    simp [stepO, step, lowerP, lowerI, costC]
  induction j with
  | zero =>
    have h1 : runO [.base (.const (-1) (-2)), .base (.play (-1)), .base (.jmp 1)] w
        ⟨0, mem, 0, 0, fun _ _ => 0, 0⟩ 1 = ⟨1, Function.update mem (-1) (-2), 0, 0, fun _ _ => 0, costC⟩ := by
      rw [hsucc 0]; exact hconst
    refine ⟨by simpa using h1, ?_⟩
    rw [show 2 * 0 + 2 = 1 + 1 from rfl, hsucc 1, h1, hplay]
    simp
  | succ j ih =>
    have h3 : runO [.base (.const (-1) (-2)), .base (.play (-1)), .base (.jmp 1)] w
        ⟨0, mem, 0, 0, fun _ _ => 0, 0⟩ (2 * (j + 1) + 1) =
        ⟨1, Function.update mem (-1) (-2), 0, j + 1, fun _ _ => 0, costC + (j + 1) * (costP (d := d) mem + 1)⟩ := by
      rw [show 2 * (j + 1) + 1 = (2 * j + 2) + 1 by ring, hsucc, ih.2, hjmp]
      congr 1
      ring
    refine ⟨h3, ?_⟩
    rw [show 2 * (j + 1) + 2 = (2 * (j + 1) + 1) + 1 by ring, hsucc, h3, hplay]

/-- The states of the run of the centre program: every state has read no coin and holds the points `0`, and from every
step at which fewer than `n` rounds have been played a later step plays one more round within cost
`costC + costP + 1`. -/
theorem centre_facts (w : WorldO d) (s0 : State d) (h0 : s0.pc = 0) (hc : s0.coins = 0) (hr : s0.rounds = 0)
    (hp : s0.pts = fun _ _ => 0) (hcost : s0.cost = 0) (hm : s0.mem (-2) = 0) (k : ℕ) :
    (runO [.base (.const (-1) (-2)), .base (.play (-1)), .base (.jmp 1)] w s0 k).coins = 0 ∧
      (runO [.base (.const (-1) (-2)), .base (.play (-1)), .base (.jmp 1)] w s0 k).pts = (fun _ _ => 0) ∧
      ∃ j, (runO [.base (.const (-1) (-2)), .base (.play (-1)), .base (.jmp 1)] w s0 k).rounds <
          (runO [.base (.const (-1) (-2)), .base (.play (-1)), .base (.jmp 1)] w s0 (k + j)).rounds ∧
        ((runO [.base (.const (-1) (-2)), .base (.play (-1)), .base (.jmp 1)] w s0 (k + j)).cost : ℝ) ≤
          (runO [.base (.const (-1) (-2)), .base (.play (-1)), .base (.jmp 1)] w s0 k).cost +
            ((costC + costP (d := d) s0.mem + 1 : ℕ) : ℝ) := by
  have hR := centre_run w s0 h0 hc hr hp hcost hm
  rcases Nat.even_or_odd' k with ⟨i, rfl | rfl⟩
  · rcases i with _ | i
    · have h2 := (hR 0).2
      simp only [Nat.mul_zero, Nat.zero_add] at h2 ⊢
      refine ⟨by simp [runO, hc], by simp [runO, hp], 2, ?_, ?_⟩
      · rw [h2]; simp [runO, hr]
      · rw [h2]; simp [runO, hcost]
    · have h2 := (hR i).2
      have h4 := (hR (i + 1)).2
      rw [show 2 * (i + 1) = 2 * i + 2 by ring, h2]
      refine ⟨rfl, rfl, 2, ?_, ?_⟩
      · rw [show 2 * i + 2 + 2 = 2 * (i + 1) + 2 by ring, h4]; simp
      · rw [show 2 * i + 2 + 2 = 2 * (i + 1) + 2 by ring, h4]
        push_cast
        nlinarith
  · have h1 := (hR i).1
    have h2 := (hR i).2
    rw [h1]
    refine ⟨rfl, rfl, 1, ?_, ?_⟩
    · rw [show 2 * i + 1 + 1 = 2 * i + 2 by ring, h2]; simp
    · rw [show 2 * i + 1 + 1 = 2 * i + 2 by ring, h2]
      push_cast
      nlinarith

/-- The rational centre `0` is the point `0` of `E d`. -/
theorem toE_zero : toE (0 : Fin d → ℚ) = 0 := by
  simp [toE]
  rfl

end Centre

/-- The hypotheses of `TheoremLowerUProg` hold for every `d`, `n` and `δ`: the closed unit ball about the rational
centre `0` (`r0 = R0 = 1`) is compact and convex, has an exact membership oracle, which is a weak membership oracle;
and for every oracle the program `M (-1) := -2`, `play (-1)`, `jmp 1`, which plays the point `0` in every round and
reads no coin, meets `MachineOK` on the input with some cost bound `B` and the windows `D = D' = 0`. -/
theorem progU_hyps_satisfiable (d n : ℕ) (δ : ℚ) :
    IsCompact (Metric.closedBall (toE (0 : Fin d → ℚ)) 1) ∧
      Convex ℝ (Metric.closedBall (toE (0 : Fin d → ℚ)) 1) ∧
      Metric.closedBall (toE (0 : Fin d → ℚ)) ((1 : ℚ) : ℝ) ⊆ Metric.closedBall (toE (0 : Fin d → ℚ)) 1 ∧
      Metric.closedBall (toE (0 : Fin d → ℚ)) 1 ⊆ Metric.closedBall (toE (0 : Fin d → ℚ)) ((1 : ℚ) : ℝ) ∧
      (∃ orc : (Fin d → ℚ) → ℕ → Bool, WeakMemOracle (Metric.closedBall (toE (0 : Fin d → ℚ)) 1) orc ∧
        ∀ y k, orc y k = true ↔ toE y ∈ Metric.closedBall (toE (0 : Fin d → ℚ)) 1) ∧
      ∀ orc : (Fin d → ℚ) → ℕ → Bool, ∃ B : ℝ,
        MachineOK [.base (.const (-1) (-2)), .base (.play (-1)), .base (.jmp 1)]
          (Metric.closedBall (toE (0 : Fin d → ℚ)) 1) orc (initU d n δ 1 1 0) n B (fun _ => 0) (fun _ => 0) := by
  classical
  refine ⟨isCompact_closedBall _ _, convex_closedBall _ _, by simp, by simp,
    ⟨fun y _ => decide (toE y ∈ Metric.closedBall (toE (0 : Fin d → ℚ)) 1), weakMemOracle_exact _,
      fun y k => by simp⟩, fun orc => ⟨((costC + costP (d := d) (initU d n δ 1 1 0).mem + 1 : ℕ) : ℝ), ?_⟩⟩
  intro f noise cs _
  have hm : (initU d n δ 1 1 0).mem (-2) = 0 := by simp [initU, inputU]
  have hF := centre_facts ⟨f, noise, cs, orc⟩ (initU d n δ 1 1 0) rfl rfl rfl rfl rfl hm
  refine ⟨fun k _ => (hF k).2.2, fun t _ => ?_, fun t _ k => ?_⟩
  · unfold playedO
    split_ifs with h
    · rw [(hF _).2.1]
      exact Metric.mem_closedBall_self zero_le_one
    · rw [toE_zero]
      exact Metric.mem_closedBall_self zero_le_one
  · rw [(hF k).1]
    exact ⟨fun _ => le_rfl, fun _ => le_rfl, fun _ => le_rfl⟩

/-- The empty program never plays, so it fails `MachineOK` on every input with `n ≥ 1`, for every convex `K`. -/
theorem nil_not_machineOK {d : ℕ} {K : Set (E d)} (hK : Convex ℝ K) (orc : (Fin d → ℚ) → ℕ → Bool) (s0 : State d)
    (n : ℕ) (B : ℝ) (D D' : ℕ → ℕ) (h0 : s0.rounds < n) : ¬ MachineOK [] K orc s0 n B D D' := fun h =>
  nil_not_costOKO _ s0 n B h0 (h (fun _ _ => 0) (fun _ => 0) (fun _ => false) fun _ _ => admLoss_zero hK).1

/-- The conclusions of `TheoremLowerUProg` hold at the threshold `0`, with probability `1`, for every program on a
convex nonempty `K` and every `r0 > 0`: the constant loss `1/2` is a strategy of `StratsLowU` in closed loop with any
program, with zero noise it is a noisy adversary with any windows, and the regret against it is `0`. -/
theorem progU_zero {d : ℕ} (P : List InstrO) {K : Set (E d)} (hK : Convex ℝ K) (hne : K.Nonempty)
    (orc : (Fin d → ℚ) → ℕ → Bool) (s0 : State d) (n : ℕ) {r0 : ℝ} (hr0 : 0 < r0) (D D' : ℕ → ℕ) :
    ProgMean P K orc s0 n r0 D D' 0 ∧ ProgProb P K orc s0 n r0 D D' 0 1 := by
  have hcl : ClosedLoop P s0 orc n (halfStrat d) (fun _ _ _ => 1 / 2) := fun _ _ _ => rfl
  have hN := noisyAdv_const hK n D D' (c := 1 / 2) (by norm_num) (by norm_num)
  have h0 : (fun cs => regretU P K n s0 (envWorld orc id (fun _ _ _ => (1 / 2 : ℝ)) (fun _ _ => 0) cs)) =
      fun _ => 0 := funext fun _ => regretPts_const hne _ _ _
  refine ⟨⟨halfStrat d, fun _ _ _ => 1 / 2, halfStrat_mem hK n hr0, hcl, hN, ?_, ?_⟩,
    ⟨halfStrat d, fun _ _ _ => 1 / 2, halfStrat_mem hK n hr0, hcl, hN, ?_, ?_⟩⟩
  · rw [h0]; exact integrable_const _
  · rw [h0]; simp
  · rw [h0]; exact measurable_const
  · simp [regretU, regretPts_const hne, envWorld]

/-! ## The bodies and Corollary MATCH -/

/-- Every body of `TheoremUnified` (rational centre and radii) is a body of `BodyU`. -/
theorem bodyU_of_unified {d : ℕ} {r0 R0 : ℚ} (h0 : 0 < r0) (h1 : r0 ≤ R0) (a : Fin d → ℚ) {K : Set (E d)}
    (hK : IsCompact K) (hc : Convex ℝ K) (hb1 : Metric.closedBall (toE a) (r0 : ℝ) ⊆ K)
    (hb2 : K ⊆ Metric.closedBall (toE a) (R0 : ℝ)) : BodyU K (toE a) r0 R0 :=
  ⟨by exact_mod_cast h0, by exact_mod_cast h1, hK, hc, hb1, hb2⟩

/-- `TheoremLowerU` contains the lower statement of v2.1 (`TheoremConj1Lower`, StatementConj1Lower.lean): its clause (a)
on the closed unit ball about `0` (`r0 = R0 = 1`), whose strategies are `1/4`-Lipschitz on all of `E d`, hence on the
ball. -/
theorem theoremConj1Lower_of_lowerU : TheoremLowerU → TheoremConj1Lower := by
  intro h d hd n hn Ω _ μ hμ pol hpol
  have hn1 : 1 ≤ n := le_trans (Nat.one_le_pow _ _ (by omega)) hn
  obtain ⟨σ, hσ, hint, hmean⟩ :=
    ((h d (by omega) n hn1 0 1 1 _ (lowerU_hyps_satisfiable d n).1 Ω _ μ hμ pol hpol).1 hd hn).1
  refine ⟨σ, ⟨hσ.1, fun t ht x o o' => ⟨(hσ.2 t ht x o o').1, fun y _ z _ => ?_⟩⟩, hint, hmean⟩
  have := (hσ.2 t ht x o o').2.2 y z
  rwa [mul_one] at this

/-- Corollary MATCH from the two theorems: the program of `TheoremUnified` meets `MachineOK` with its own bound and
windows, so `TheoremLowerUProg` applies to it, in environments of its own class. -/
theorem corollaryMatch_of_unified_lower : TheoremUnified → TheoremLowerUProg → CorollaryMatch := by
  rintro ⟨P, C, C', k, D, D', hU⟩ hL
  refine ⟨P, C, C', k, D, D', fun d hd n hn δ r0 R0 hδ0 hδ1 hr0 hr0R a K hK hc hb1 hb2 orc horc => ?_⟩
  have h := hU d hd n hn δ r0 R0 hδ0 hδ1 hr0 hr0R a K hK hc hb1 hb2 orc horc
  have hM : MachineOK P K orc (initU d n δ r0 R0 a) n
      (C' * ((d : ℝ) * Real.log (2 * d * n / (δ : ℝ)) * sizeU δ r0 R0 a) ^ k) (D d n δ r0 R0 a)
      (D' d n δ r0 R0 a) :=
    fun f noise cs hf => ⟨(h.1 f noise cs hf).1, (h.1 f noise cs hf).2.2.1, (h.1 f noise cs hf).2.2.2⟩
  exact ⟨h.1, h.2, hL P d hd n hn δ r0 R0 hδ0 hδ1 hr0 hr0R a K hK hc hb1 hb2 orc horc _ _ _ hM⟩

/-- The upper part of `CorollaryMatch` is `TheoremUnified` word for word. -/
theorem theoremUnified_of_corollaryMatch : CorollaryMatch → TheoremUnified := by
  rintro ⟨P, C, C', k, D, D', h⟩
  exact ⟨P, C, C', k, D, D', fun d hd n hn δ r0 R0 hδ0 hδ1 hr0 hr0R a K hK hc hb1 hb2 orc horc =>
    ⟨(h d hd n hn δ r0 R0 hδ0 hδ1 hr0 hr0R a K hK hc hb1 hb2 orc horc).1,
      (h d hd n hn δ r0 R0 hδ0 hδ1 hr0 hr0R a K hK hc hb1 hb2 orc horc).2.1⟩⟩

end AdversarialBco.UnifiedLower.LowerSanity
