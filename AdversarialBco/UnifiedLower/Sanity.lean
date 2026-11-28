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

The witnesses `lowerU_hyps_satisfiable` and `progU_hyps_satisfiable` are certified by Comparator in the configurations
config-minimax-q.json and config-matched.json, against the challenges ChallengeMinimaxQ.lean and ChallengeMatched.lean.

* The hypotheses of `TheoremLowerU` hold for every `d` and `n` at the closed unit ball about `0` with the constant
  learner on `Unit` (`lowerU_hyps_satisfiable`).
* The hypotheses of `TheoremLowerUProg` hold for every `d`, `n` and `δ` at the closed unit ball about the rational
  centre `0`, with its exact membership oracle, and for the program of three instructions `M (-1) := -2`,
  `play (-1)`, `jmp 1`, which plays the point `0` (the centre; the denominator cell `-2` holds `0`) in every round
  and reads no coin, with the windows `D = D' = 0`, on every world and for every oracle (`progU_hyps_satisfiable`).
* Every body of `TheoremUnified` is a body of `BodyU` (`bodyU_of_unified`).
-/

open MeasureTheory ProbabilityTheory

namespace AdversarialBco.UnifiedLower.LowerSanity

open BitRAM BitRAMO Unified Unified.UnifiedSanity
open RealRAM (Strategy Strats regretPts)
open Lower (Learner IsLearnerAd regretAd)

/-! ## The constant loss -/

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

/-! ## The bodies and Corollary MATCH -/

/-- Every body of `TheoremUnified` (rational centre and radii) is a body of `BodyU`. -/
theorem bodyU_of_unified {d : ℕ} {r0 R0 : ℚ} (h0 : 0 < r0) (h1 : r0 ≤ R0) (a : Fin d → ℚ) {K : Set (E d)}
    (hK : IsCompact K) (hc : Convex ℝ K) (hb1 : Metric.closedBall (toE a) (r0 : ℝ) ⊆ K)
    (hb2 : K ⊆ Metric.closedBall (toE a) (R0 : ℝ)) : BodyU K (toE a) r0 R0 :=
  ⟨by exact_mod_cast h0, by exact_mod_cast h1, hK, hc, hb1, hb2⟩

end AdversarialBco.UnifiedLower.LowerSanity
