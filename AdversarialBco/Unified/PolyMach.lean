/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.PolySim

@[expose] public section

/-!
# UNI-POLY: the machine clauses of the compiled program (`mach`) and its plays (`plays_eq`)
-/

open MeasureTheory ProbabilityTheory

namespace AdversarialBco.UniPoly

open BitRAM BitRAMO Unified
open RealRAM (Strategy lossAd regretPts polytope HeightLE)
open Bit.Asm (InputOK)
open Bit.Transfer (B.run_add)

variable {d : ℕ}

/-! ## Small facts -/

/-- A step of the oracle machine that plays changes no cell. -/
theorem stepO_mem_of_play (P : List InstrO) (w : WorldO d) (s : State d)
    (h : (stepO P w s).rounds = s.rounds + 1) : (stepO P w s).mem = s.mem := by
  unfold stepO at h ⊢
  rcases hP : P[s.pc]? with _ | ins
  · simp [hP] at h
  · rw [hP] at h
    rcases ins with i | ⟨dst, src, prec⟩ | ⟨dst, prec, rng⟩
    · simp only at h ⊢
      unfold step at h ⊢
      rw [RunFacts.lowerP_get' hP] at h ⊢
      rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | src | _ <;> simp at h ⊢
    · simp at h
    · simp at h

/-- The cost of the oracle machine never decreases. -/
theorem stepO_cost_le (P : List InstrO) (w : WorldO d) (s : State d) : s.cost ≤ (stepO P w s).cost := by
  unfold stepO
  rcases hP : P[s.pc]? with _ | ins
  · exact le_rfl
  · rcases ins with i | ⟨dst, src, prec⟩ | ⟨dst, prec, rng⟩
    · exact Bit.Transfer.step_cost_le _ _ _
    · simp only; omega
    · simp only; omega

theorem runO_cost_mono (P : List InstrO) (w : WorldO d) (s0 : State d) {k k' : ℕ} (hk : k ≤ k') :
    (runO P w s0 k).cost ≤ (runO P w s0 k').cost := by
  induction k', hk using Nat.le_induction with
  | base => exact le_rfl
  | succ k' hk ih => rw [RunFacts.runO_succ]; exact ih.trans (stepO_cost_le _ _ _)

/-- The cubes of the increments of a monotone sequence sum to at most the cube of the total increment. -/
theorem sum_cube_le (a : ℕ → ℕ) (ha : Monotone a) (j : ℕ) :
    ∑ i ∈ Finset.range j, (a (i + 1) - a i) ^ 3 ≤ (a j - a 0) ^ 3 := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Finset.sum_range_succ]
    have h1 : a j ≤ a (j + 1) := ha (Nat.le_add_right j 1)
    have h2 : a 0 ≤ a j := ha (Nat.zero_le j)
    have e : a (j + 1) - a 0 = (a j - a 0) + (a (j + 1) - a j) := by omega
    rw [e]
    have : (a j - a 0) ^ 3 + (a (j + 1) - a j) ^ 3 ≤ ((a j - a 0) + (a (j + 1) - a j)) ^ 3 := by
      nlinarith [Nat.zero_le (a j - a 0), Nat.zero_le (a (j + 1) - a j),
        Nat.zero_le ((a j - a 0) * (a (j + 1) - a j))]
    omega

/-- The space of the compiled program at a state holding `s`. -/
theorem rel_space {F : ℕ → ℕ} {t0 : State d} {s t : State d} {S Sf : ℝ} (h : Rel F t0.mem s t)
    (hs : SpaceLE s S) (hf : SpaceLE t0 Sf) : SpaceLE t (12 * S + Sf) := by
  intro G hG
  set g : ℤ → ℕ := fun c => len c + len (t.mem c) with hg
  rw [← Finset.sum_filter_add_sum_filter_not G (fun c => -N0 < c)]
  have h1 : ((∑ c ∈ G.filter (fun c => -N0 < c), g c : ℕ) : ℝ) ≤ Sf := by
    have e : ∑ c ∈ G.filter (fun c => -N0 < c), g c =
        ∑ c ∈ G.filter (fun c => -N0 < c), (len c + len (t0.mem c)) :=
      Finset.sum_congr rfl fun c hc => by
        rw [Finset.mem_filter] at hc; simp only [hg, h.fix c hc.2]
    rw [e]
    refine hf _ fun c hc => ?_
    rw [Finset.mem_filter] at hc
    rw [← h.fix c hc.2]; exact hG c hc.1
  have hinj : Set.InjOn φ (φ ⁻¹' ↑(G.filter (fun c => ¬ -N0 < c))) := fun x _ y _ e => φ_inj e
  have h2 : ((∑ c ∈ G.filter (fun c => ¬ -N0 < c), g c : ℕ) : ℝ) ≤ 12 * S := by
    rw [← Finset.sum_preimage φ _ hinj g (fun c hc hr => by
      rw [Finset.mem_filter] at hc
      exact absurd (φ_surj (c := c) (by omega)) (by simpa using hr))]
    set H := (G.filter (fun c => ¬ -N0 < c)).preimage φ hinj
    have hH : ∀ x ∈ H, s.mem x ≠ 0 := fun x hx => by
      rw [Finset.mem_preimage, Finset.mem_filter] at hx
      rw [← h.z x]; exact hG _ hx.1
    have hle : ∑ x ∈ H, g (φ x) ≤ 12 * ∑ x ∈ H, (len x + len (s.mem x)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun x hx => ?_
      have l1 := len_φ x
      have l2 : 1 ≤ len (s.mem x) := by
        unfold len; exact Nat.size_pos.2 (Int.natAbs_pos.2 (hH x hx))
      simp only [hg, h.z x]
      omega
    have := hs H hH
    calc ((∑ x ∈ H, g (φ x) : ℕ) : ℝ) ≤ ((12 * ∑ x ∈ H, (len x + len (s.mem x)) : ℕ) : ℝ) := by
          exact_mod_cast hle
      _ ≤ 12 * S := by push_cast; push_cast at this; linarith
  have e : ∀ c, len c + len (t.mem c) = g c := fun c => rfl
  simp only [e]
  push_cast at h1 h2 ⊢
  linarith

/-! ## The machine clauses -/

/-- The bound of the machine clauses of the compiled program, from the bound `BU` of `P`. -/
noncomputable def Bmach (d n m M : ℕ) (BU : ℝ) : ℝ :=
  ((2 * Cpro d n m M + 2 * (Kc d m M * ⌊BU⌋₊ ^ 3) : ℕ) : ℝ) + 2 * (Bit.Transfer.inSpace d n m M : ℝ) + 12 * BU

/-- The cost of the compiled program along a segment of `P` whose readings are in `[0, 1]`. -/
theorem seg_cost (P : List InstrO) {n m M : ℕ} {A : Matrix (Fin m) (Fin d) ℚ} {b : Fin m → ℚ} (w : World d)
    (g : ℕ → ℕ) (hg : ∀ k, FbOK w (run (progP P) w (initBit d n m A b) (g k)) →
        (run (progP P) w (initBit d n m A b) (g (k + 1))).cost ≤
          (run (progP P) w (initBit d n m A b) (g k)).cost +
            Kc d m M * ((runO P (worldO A b w) (s0U d n m A b) (k + 1)).cost -
              (runO P (worldO A b w) (s0U d n m A b) k).cost) ^ 3) (k : ℕ) :
    ∀ j, (∀ i < j, FbOK w (run (progP P) w (initBit d n m A b) (g (k + i)))) →
      (run (progP P) w (initBit d n m A b) (g (k + j))).cost ≤
        (run (progP P) w (initBit d n m A b) (g k)).cost +
          Kc d m M * ((runO P (worldO A b w) (s0U d n m A b) (k + j)).cost -
            (runO P (worldO A b w) (s0U d n m A b) k).cost) ^ 3 := by
  intro j hj
  set c : ℕ → ℕ := fun i => (runO P (worldO A b w) (s0U d n m A b) (k + i)).cost with hc
  have hmono : Monotone c := fun i i' h => runO_cost_mono _ _ _ (by omega)
  have key : (run (progP P) w (initBit d n m A b) (g (k + j))).cost ≤
      (run (progP P) w (initBit d n m A b) (g k)).cost +
        Kc d m M * ∑ i ∈ Finset.range j, (c (i + 1) - c i) ^ 3 := by
    induction j with
    | zero => simp
    | succ j ih =>
      have h1 := ih (fun i hi => hj i (by omega))
      have h2 := hg (k + j) (hj j (by omega))
      rw [Finset.sum_range_succ, Nat.mul_add]
      have e1 : k + (j + 1) = k + j + 1 := by omega
      rw [e1]
      have e2 : c (j + 1) - c j = (runO P (worldO A b w) (s0U d n m A b) (k + j + 1)).cost -
          (runO P (worldO A b w) (s0U d n m A b) (k + j)).cost := by
        simp only [hc, e1]
      rw [e2]
      omega
  have := sum_cube_le c hmono j
  have e0 : c 0 = (runO P (worldO A b w) (s0U d n m A b) k).cost := by simp [hc]
  rw [e0] at this
  calc _ ≤ _ := key
    _ ≤ _ := by gcongr

/-- The world of the compiled program in the game `g0`. -/
noncomputable abbrev gw (P : List InstrO) (g0 : GameBit d) (n m : ℕ) (A : Matrix (Fin m) (Fin d) ℚ)
    (b : Fin m → ℚ) : World d :=
  Bit.Transfer.gameWorld (progP P) g0 (initBit d n m A b)

/-- **The machine clauses** of the compiled program, from those of `P` in the oracle world of the game. -/
theorem mach (P : List InstrO) {n m M : ℕ} {A : Matrix (Fin m) (Fin d) ℚ} {b : Fin m → ℚ}
    (hI : InputOK d n m M A b) (g0 : GameBit d) {BU : ℝ}
    (hc : CostOKO P (worldO A b (gw P g0 n m A b)) (s0U d n m A b) n BU)
    (hs : SpaceOKO P (worldO A b (gw P g0 n m A b)) (s0U d n m A b) n BU)
    (hK : ∀ t < n, playedO P (worldO A b (gw P g0 n m A b)) (s0U d n m A b) t ∈ polytope A b)
    (hadm : ∀ t < n, AdmLoss (polytope A b) ((gw P g0 n m A b).f t)) :
    CostOKBit (progP P) g0 (initBit d n m A b) n (Bmach d n m M BU) ∧
      SpaceOKBit (progP P) g0 (initBit d n m A b) n (Bmach d n m M BU) := by
  set w := gw P g0 n m A b with hw
  obtain ⟨g, hrel, hmono, hc0, hstep⟩ := sim P hI w
  set wO := worldO A b w with hwO
  have hn0 : (runO P wO (s0U d n m A b) 0).rounds < n := by
    show 0 < n; exact hI.hn
  have hBU : 0 ≤ BU := by
    have := hs 0 hn0 ∅ (by simp)
    simpa using this
  have hin := Bit.Transfer.input_spaceLE (n := n) hI.height
  have hT0 : SpaceLE (run (progP P) w (initBit d n m A b) (g 0))
      ((Bit.Transfer.inSpace d n m M : ℝ) + (Cpro d n m M : ℝ)) := by
    refine Bit.Transfer.spaceLE_mono (Bit.Transfer.space_run_le hin (g 0)) ?_
    have : ((run (progP P) w (initBit d n m A b) (g 0)).cost : ℝ) ≤ Cpro d n m M := by exact_mod_cast hc0
    have e : (initBit d n m A b).cost = 0 := rfl
    rw [e]; push_cast; linarith
  set Start : State d → Prop := fun a =>
    ∃ k, a = run (progP P) w (initBit d n m A b) (g k) ∧ SpaceLE (runO P wO (s0U d n m A b) k) BU with hStart
  have hS : ∀ a, Start a → SpaceLE a (12 * BU + ((Bit.Transfer.inSpace d n m M : ℝ) + (Cpro d n m M : ℝ))) := by
    rintro a ⟨k, rfl, hsk⟩
    exact rel_space (hrel k) hsk hT0
  have hseg : ∀ a, Start a → a.rounds < n → ∃ j, Start (run (progP P) w a j) ∧
      a.rounds < (run (progP P) w a j).rounds ∧
      (run (progP P) w a j).cost ≤ a.cost + Kc d m M * ⌊BU⌋₊ ^ 3 := by
    rintro a ⟨k, rfl, -⟩ hlt
    rw [(hrel k).rounds] at hlt
    obtain ⟨j, hj1, hj2⟩ := hc k hlt
    have hex : ∃ j, (runO P wO (s0U d n m A b) k).rounds < (runO P wO (s0U d n m A b) (k + j)).rounds :=
      ⟨j, hj1⟩
    have hj'j : Nat.find hex ≤ j := Nat.find_min' hex hj1
    have hspec := Nat.find_spec hex
    obtain ⟨i, hi⟩ : ∃ i, Nat.find hex = i + 1 := by
      rcases h0 : Nat.find hex with _ | i
      · rw [h0] at hspec; simp at hspec
      · exact ⟨i, rfl⟩
    rw [hi] at hspec hj'j
    have hsame : ∀ i' ≤ i, (runO P wO (s0U d n m A b) (k + i')).rounds = (runO P wO (s0U d n m A b) k).rounds := by
      intro i' hi'
      have h1 := (RunFacts.runO_mono P wO (s0U d n m A b) (Nat.le_add_right k i')).1
      have h2 := Nat.find_min hex (show i' < Nat.find hex by omega)
      omega
    have hplay := RunFacts.stepO_facts P wO (runO P wO (s0U d n m A b) (k + i))
    rw [← RunFacts.runO_succ, show k + i + 1 = k + (i + 1) by omega, hsame i le_rfl] at hplay
    have hr1 : (runO P wO (s0U d n m A b) (k + (i + 1))).rounds = (runO P wO (s0U d n m A b) (k + i)).rounds + 1 := by
      rw [hsame i le_rfl]; omega
    have hmem : (runO P wO (s0U d n m A b) (k + (i + 1))).mem = (runO P wO (s0U d n m A b) (k + i)).mem := by
      rw [show k + (i + 1) = k + i + 1 by omega, RunFacts.runO_succ] at hr1 ⊢
      exact stepO_mem_of_play P wO _ hr1
    have hsp : SpaceLE (runO P wO (s0U d n m A b) (k + (i + 1))) BU := by
      have := hs (k + i) (by rw [hsame i le_rfl]; exact hlt)
      intro F hF
      have hF' : ∀ c ∈ F, (runO P wO (s0U d n m A b) (k + i)).mem c ≠ 0 := by
        intro c hc; rw [← hmem]; exact hF c hc
      have := this F hF'
      rw [hmem]; exact this
    have hgk : g k ≤ g (k + (i + 1)) := hmono (by omega)
    refine ⟨g (k + (i + 1)) - g k, ?_, ?_, ?_⟩
    · refine ⟨k + (i + 1), ?_, hsp⟩
      rw [← B.run_add, Nat.add_sub_cancel' hgk]
    · rw [← B.run_add, Nat.add_sub_cancel' hgk, (hrel _).rounds, (hrel _).rounds]
      exact hspec
    · rw [← B.run_add, Nat.add_sub_cancel' hgk]
      have hfb : ∀ i' < i + 1, FbOK w (run (progP P) w (initBit d n m A b) (g (k + i'))) := by
        intro i' hi'
        have hr := hsame i' (by omega)
        unfold FbOK feedback
        rw [(hrel _).rounds, hr]
        split_ifs with h0
        · exact ⟨le_rfl, zero_le_one⟩
        · rw [(hrel _).pts]
          have hlt' : (runO P wO (s0U d n m A b) k).rounds - 1 < (runO P wO (s0U d n m A b) (k + i')).rounds := by
            rw [hr]; omega
          rw [← RunFacts.playedO_eq_pts P wO (s0U d n m A b) hlt']
          exact (hadm _ (by omega)).2 _ (hK _ (by omega))
      have hcost := seg_cost P w g hstep k (i + 1) hfb
      have hdiff : (runO P wO (s0U d n m A b) (k + (i + 1))).cost - (runO P wO (s0U d n m A b) k).cost ≤ ⌊BU⌋₊ := by
        apply Nat.le_floor
        have h1 := runO_cost_mono P wO (s0U d n m A b) (show k + (i + 1) ≤ k + j by omega)
        have h2 := runO_cost_mono P wO (s0U d n m A b) (show k ≤ k + (i + 1) by omega)
        rw [Nat.cast_sub h2]
        have h1' : ((runO P wO (s0U d n m A b) (k + (i + 1))).cost : ℝ) ≤ (runO P wO (s0U d n m A b) (k + j)).cost := by
          exact_mod_cast h1
        linarith
      calc _ ≤ _ := hcost
        _ ≤ _ := by gcongr
  have hc0' : (run (progP P) w (initBit d n m A b) (g 0)).cost ≤ (initBit d n m A b).cost + Cpro d n m M := by
    have e : (initBit d n m A b).cost = 0 := rfl
    rw [e, Nat.zero_add]; exact hc0
  obtain ⟨hC, hSp⟩ := Bit.Transfer.driver_bit (Bp := Cpro d n m M) (Bc := Kc d m M * ⌊BU⌋₊ ^ 3) g0 rfl Start hin
    (g 0) ⟨0, rfl, hs 0 hn0⟩ hc0' hS hseg
  have hinS : (0 : ℝ) ≤ Bit.Transfer.inSpace d n m M := Nat.cast_nonneg _
  have hCp : (0 : ℝ) ≤ Cpro d n m M := Nat.cast_nonneg _
  refine ⟨fun k hk => ?_, fun k hk => ?_⟩
  · obtain ⟨j, h1, h2⟩ := hC k hk
    refine ⟨j, h1, h2.trans ?_⟩
    unfold Bmach
    push_cast
    linarith
  · refine Bit.Transfer.spaceLE_mono (hSp k hk) ?_
    unfold Bmach
    push_cast
    rw [max_eq_right (by linarith)]
    have : (0 : ℝ) ≤ (Kc d m M : ℝ) * (⌊BU⌋₊ : ℝ) ^ 3 := by positivity
    linarith

/-! ## The plays and the regret -/

/-- Under the cost clause every round `t < n` is played. -/
theorem plays_all {P : List InstrO} {w : WorldO d} {s0 : State d} {n : ℕ} {B : ℝ} (hc : CostOKO P w s0 n B)
    (h0 : s0.rounds = 0) : ∀ t < n, ∃ k, t < (runO P w s0 k).rounds := by
  intro t ht
  induction t with
  | zero =>
    obtain ⟨j, hj, -⟩ := hc 0 (by rw [RunFacts.runO_zero, h0]; omega)
    exact ⟨0 + j, by rw [RunFacts.runO_zero, h0] at hj; omega⟩
  | succ t ih =>
    obtain ⟨k, hk⟩ := ih (by omega)
    by_cases h : t + 1 < (runO P w s0 k).rounds
    · exact ⟨k, h⟩
    · obtain ⟨j, hj, -⟩ := hc k (by omega)
      exact ⟨k + j, by omega⟩

/-- The plays of the compiled program are those of `P` in the oracle world of the game. -/
theorem plays_eq (P : List InstrO) {n m M : ℕ} {A : Matrix (Fin m) (Fin d) ℚ} {b : Fin m → ℚ}
    (hI : InputOK d n m M A b) (g0 : GameBit d) {BU : ℝ}
    (hc : CostOKO P (worldO A b (gw P g0 n m A b)) (s0U d n m A b) n BU) :
    ∀ t < n, playedBit (progP P) g0 (initBit d n m A b) t =
      playedO P (worldO A b (gw P g0 n m A b)) (s0U d n m A b) t := by
  intro t ht
  obtain ⟨g, hrel, -⟩ := sim P hI (gw P g0 n m A b)
  obtain ⟨k, hk⟩ := plays_all hc rfl t ht
  have e : runBit (progP P) g0 (initBit d n m A b) (g k) = run (progP P) (gw P g0 n m A b) (initBit d n m A b) (g k) := by
    cases g0; exact Conj1BitSanity.runBit_eq_run _ _ _ _ _
  have hk' : t < (runBit (progP P) g0 (initBit d n m A b) (g k)).rounds := by
    rw [e, (hrel k).rounds]; exact hk
  rw [Bit.RegMeas.playedBit_eq_pts _ g0 _ hk', e, (hrel k).pts, RunFacts.playedO_eq_pts P _ _ hk]

/-- The regret reads the points of the rounds `t < n` only. -/
theorem regretPts_congr (K : Set (E d)) (f : ℕ → E d → ℝ) {x y : ℕ → E d} (n : ℕ) (h : ∀ t < n, x t = y t) :
    regretPts K f x n = regretPts K f y n := by
  unfold regretPts
  congr 1
  exact Finset.sum_congr rfl fun t ht => by rw [h t (Finset.mem_range.1 ht)]

/-- The loss of round `t` of the environment at the seed and the coins `ω`. -/
noncomputable def lossE (P : List InstrO) {Θ : Type} (σ : Θ → Strategy d) (n m : ℕ) (A : Matrix (Fin m) (Fin d) ℚ)
    (b : Fin m → ℚ) : ℕ → Θ × (ℕ → Bool) → E d → ℝ :=
  fun t ω => lossAd (σ ω.1) 0 (playedBit (progP P) ⟨σ ω.1, ω.2⟩ (initBit d n m A b)) t

/-- The losses of the game are admissible. -/
theorem adm_gw (P : List InstrO) {n m : ℕ} {A : Matrix (Fin m) (Fin d) ℚ} {b : Fin m → ℚ} {Θ : Type}
    [MeasurableSpace Θ] {σ : Θ → Strategy d} (hσ : RandAdv (polytope A b) n σ) (θ : Θ) (cs : ℕ → Bool) :
    ∀ t < n, AdmLoss (polytope A b) ((gw P ⟨σ θ, cs⟩ n m A b).f t) := by
  intro t ht
  show AdmLoss _ (lossAd (σ θ) 0 (playedBit (progP P) ⟨σ θ, cs⟩ (initBit d n m A b)) t)
  rw [Bit.Asm.playedBit_eq]
  exact (hσ t ht _).1 θ

end AdversarialBco.UniPoly
