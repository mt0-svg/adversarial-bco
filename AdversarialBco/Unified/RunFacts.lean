/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.StatementUnified
public import Mathlib.MeasureTheory.Function.Floor

@[expose] public section

/-!
# The run facts of the oracle machine: causality (M1) and measurability (M2)

Two facts on the runs `runO` of the frozen oracle machine (StatementBitRAMO.lean), shared by the lower bound
(Lemmas BRIDGE and REAL, the paper's section on programs) and the measurability of the regret of the upper
theorem (UNI-MEAS).

* **M1, causality.** A step reads the world through one integer pair only (`stepKeyO`): the coins read by `coins`,
  or the reading `⌊2^p o⌋` of the feedback `o` by `obs` and `obsR`; the oracle is read too, at a point and a precision
  of the state. So a step is the same in two worlds with the same oracle, the same feedback at that state (`fbO`) and
  the same coins below the coin count after the step (`stepO_congr`); a run is the same up to step `k` when this
  holds at every earlier state (`runO_congr`); and the point of round `t` is the same when it holds along the states
  with at most `t` rounds played (`playedO_congr_gen`), in particular when the coins agree below a bound `N` of the
  coin count of those states (`playedO_congr`) or the two worlds have one coin stream (`playedO_congr_same`). The feedback at a state with `r` rounds played is the noisy loss of round `r - 1` at the point of
  round `r - 1` (`fbO_eq`).
* **M2, measurability.** For a family of worlds `g ω` with one oracle, coins measurable in `ω` and the feedback at each
  state with at most `n` rounds measurable in `ω` (`FbMeasO`), the state after `k` steps takes countably many values,
  each on a measurable event among the states with at most `n` rounds (`runO_meas`), and the point of each round
  `t < n` is a measurable function of `ω` with countably many values (`playedO_meas`, `measurable_playedO`).

Also: the monotonicity of a run (`stepO_facts`, `runO_mono`) and the point of a round read off any later state
(`playedO_eq_pts`), and the generic countable-fibre lemmas of the port of Bit/RegMeas.lean.
-/

open MeasureTheory

namespace AdversarialBco.Unified.RunFacts

open BitRAM BitRAMO

variable {d : ℕ}

/-! ## Generic countable fibres -/

theorem measurableSet_preimage_of_factor {Ω C Y : Type*} [MeasurableSpace Ω] [MeasurableSpace C] [Countable C]
    [MeasurableSingletonClass C] {k : Ω → C} (hk : Measurable k) {f : Ω → Y}
    (hf : ∀ ω ω', k ω = k ω' → f ω = f ω') (T : Set Y) : MeasurableSet (f ⁻¹' T) := by
  have h_eq : f ⁻¹' T = k ⁻¹' {c | ∃ ω, k ω = c ∧ f ω ∈ T} := by
    ext ω
    constructor
    · intro hω
      exact ⟨ω, rfl, hω⟩
    · rintro ⟨ω', hk', hf'⟩
      show f ω ∈ T
      rwa [hf ω ω' hk'.symm]
  rw [h_eq]
  exact hk (MeasurableSet.of_discrete)

theorem countable_range_of_factor {Ω C Y : Type*} [Countable C] (k : Ω → C) {f : Ω → Y}
    (hf : ∀ ω ω', k ω = k ω' → f ω = f ω') : (Set.range f).Countable := by
  have hsub : Set.range f ⊆ ⋃ c ∈ Set.range k, {y | ∃ ω, k ω = c ∧ f ω = y} := by
    rintro _ ⟨ω, rfl⟩
    exact Set.mem_biUnion ⟨ω, rfl⟩ ⟨ω, rfl, rfl⟩
  refine Set.Countable.mono hsub ((Set.to_countable (Set.range k)).biUnion fun c _ => ?_)
  refine Set.Subsingleton.countable ?_
  rintro _ ⟨ω, hω, rfl⟩ _ ⟨ω', hω', rfl⟩
  exact hf ω ω' (hω.trans hω'.symm)

theorem measurable_of_countable_fibers {Ω Q Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Y] {X : Ω → Q}
    (hX : (Set.range X).Countable) (hfib : ∀ q ∈ Set.range X, MeasurableSet (X ⁻¹' {q})) {G : Q → Ω → Y}
    (hG : ∀ q ∈ Set.range X, Measurable (G q)) : Measurable fun ω => G (X ω) ω := by
  intro U hU
  have h_eq : (fun ω => G (X ω) ω) ⁻¹' U = ⋃ q ∈ Set.range X, (X ⁻¹' {q}) ∩ (G q ⁻¹' U) := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_range,
      exists_prop]
    constructor
    · intro h
      exact ⟨X ω, ⟨ω, rfl⟩, rfl, h⟩
    · rintro ⟨q, -, rfl, h⟩
      exact h
  rw [h_eq]
  exact MeasurableSet.biUnion hX fun q hq => (hfib q hq).inter (hG q hq hU)

/-- A function with countably many values, each on a measurable event, is measurable. -/
theorem measurable_of_fibers {Ω Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Y] {X : Ω → Y}
    (hX : (Set.range X).Countable) (hfib : ∀ q ∈ Set.range X, MeasurableSet (X ⁻¹' {q})) : Measurable X :=
  measurable_of_countable_fibers (G := fun q _ => q) hX hfib fun _ _ => measurable_const

/-! ## One step -/

theorem runO_zero (P : List InstrO) (w : WorldO d) (s0 : State d) : runO P w s0 0 = s0 := rfl

theorem runO_succ (P : List InstrO) (w : WorldO d) (s0 : State d) (k : ℕ) :
    runO P w s0 (k + 1) = stepO P w (runO P w s0 k) :=
  Function.iterate_succ_apply' _ _ _

/-- The lowered program at a base instruction. -/
theorem lowerP_get' {P : List InstrO} {q : ℕ} {i : Instr} (h : P[q]? = some (.base i)) :
    (lowerP P)[q]? = some i := by
  simp [lowerP, List.getElem?_map, h, lowerI]

/-- What a step changes of the rounds, the coins and the points: the rounds grow by at most one, the coins do not
decrease, the points of the rounds already played stay, and a step that plays reads no coin. -/
theorem stepO_facts (P : List InstrO) (w : WorldO d) (s : State d) :
    s.rounds ≤ (stepO P w s).rounds ∧ (stepO P w s).rounds ≤ s.rounds + 1 ∧ s.coins ≤ (stepO P w s).coins ∧
      (∀ t < s.rounds, (stepO P w s).pts t = s.pts t) ∧
      ((stepO P w s).rounds = s.rounds + 1 → (stepO P w s).coins = s.coins) := by
  unfold stepO
  rcases hP : P[s.pc]? with _ | ins
  · simp
  · rcases ins with i | ⟨dst, src, prec⟩ | ⟨dst, prec, rng⟩
    · simp only
      unfold step
      rw [lowerP_get' hP]
      rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | src | _
      all_goals simp
      intro t ht
      rw [Function.update_of_ne (Nat.ne_of_lt ht)]
    · simp
    · simp

theorem runO_mono (P : List InstrO) (w : WorldO d) (s0 : State d) {k k' : ℕ} (hk : k ≤ k') :
    (runO P w s0 k).rounds ≤ (runO P w s0 k').rounds ∧ (runO P w s0 k).coins ≤ (runO P w s0 k').coins ∧
      ∀ i < (runO P w s0 k).rounds, (runO P w s0 k').pts i = (runO P w s0 k).pts i := by
  induction k', hk using Nat.le_induction with
  | base => exact ⟨le_rfl, le_rfl, fun _ _ => rfl⟩
  | succ k' hk ih =>
    obtain ⟨h1, -, h3, h4, -⟩ := stepO_facts P w (runO P w s0 k')
    rw [runO_succ]
    refine ⟨ih.1.trans h1, ih.2.1.trans h3, fun i hi => ?_⟩
    rw [h4 i (lt_of_lt_of_le hi ih.1), ih.2.2 i hi]

/-- The point of a round already played at step `k` is the point that `playedO` gives for that round. -/
theorem playedO_eq_pts (P : List InstrO) (w : WorldO d) (s0 : State d) {t k : ℕ}
    (h : t < (runO P w s0 k).rounds) : playedO P w s0 t = toE ((runO P w s0 k).pts t) := by
  have hex : ∃ k', t < (runO P w s0 k').rounds := ⟨k, h⟩
  unfold playedO
  rw [dite_eq_left hex]
  rw [(runO_mono P w s0 (Nat.find_min' hex h)).2.2 t (Nat.find_spec hex)]

/-- The point of a round is a rational point. -/
theorem playedO_rat (P : List InstrO) (w : WorldO d) (s0 : State d) (t : ℕ) :
    ∃ q : Fin d → ℚ, playedO P w s0 t = toE q := by
  unfold playedO
  split_ifs with h
  · exact ⟨_, rfl⟩
  · refine ⟨0, ?_⟩
    ext i
    simp [toE]

/-! ## M1: causality -/

/-- The feedback a step at `s` can read in the world `w`: the noisy loss of the last round played. -/
noncomputable def fbO (w : WorldO d) (s : State d) : ℝ := feedback w.toW s

theorem fbO_eq (w : WorldO d) (s : State d) :
    fbO w s = if s.rounds = 0 then 0 else w.f (s.rounds - 1) (toE (s.pts (s.rounds - 1))) + w.noise (s.rounds - 1) :=
  rfl

/-- What a step reads off the world besides the oracle: the integer of the coins read, or the reading of the
feedback. -/
noncomputable def stepKeyO (P : List InstrO) (w : WorldO d) (s : State d) : ℤ × ℤ :=
  match P[s.pc]? with
  | some (.base (.coins _ cnt)) => (readCoins w.cs s.coins (s.mem cnt).toNat, 0)
  | some (.base (.obs _ prec)) => (0, reading w.toW s (s.mem prec).toNat)
  | some (.obsR _ prec _) => (0, reading w.toW s (s.mem prec).toNat)
  | _ => (0, 0)

theorem stepO_eq_of_key (P : List InstrO) {w w' : WorldO d} (s : State d) (horc : w.orc = w'.orc)
    (h : stepKeyO P w s = stepKeyO P w' s) : stepO P w s = stepO P w' s := by
  unfold stepKeyO at h
  unfold stepO
  rcases hP : P[s.pc]? with _ | ins
  · rfl
  · rw [hP] at h
    rcases ins with i | ⟨dst, src, prec⟩ | ⟨dst, prec, rng⟩
    · simp only
      unfold step
      rw [lowerP_get' hP]
      rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | ⟨dst, cnt⟩ | src | ⟨dst, prec⟩
      all_goals try rfl
      · have hr : readCoins w.toW.cs s.coins (s.mem cnt).toNat = readCoins w'.toW.cs s.coins (s.mem cnt).toNat :=
          congrArg Prod.fst h
        simp only [hr]
      · have hr : reading w.toW s (s.mem prec).toNat = reading w'.toW s (s.mem prec).toNat :=
          congrArg Prod.snd h
        simp only [hr]
    · simp only [horc]
    · have hr : reading w.toW s (s.mem prec).toNat = reading w'.toW s (s.mem prec).toNat :=
        congrArg Prod.snd h
      simp only [hr]

theorem readCoins_congr {cs cs' : ℕ → Bool} (c : ℕ) :
    ∀ k, (∀ j, c ≤ j → j < c + k → cs j = cs' j) → readCoins cs c k = readCoins cs' c k
  | 0, _ => rfl
  | k + 1, h => by
    simp only [readCoins]
    rw [readCoins_congr c k fun j h1 h2 => h j h1 (by omega), h (c + k) (by omega) (by omega)]

theorem reading_congr {w w' : WorldO d} (s : State d) (h : fbO w s = fbO w' s) (p : ℕ) :
    reading w.toW s p = reading w'.toW s p := by
  unfold reading
  rw [show feedback w.toW s = fbO w s from rfl, h]
  rfl

/-- M1, one step: with the same oracle, the same feedback at `s` and the same coins below the coin count after the
step, the step is the same. -/
theorem stepO_congr (P : List InstrO) {w w' : WorldO d} (s : State d) (horc : w.orc = w'.orc)
    (hfb : fbO w s = fbO w' s) (hcs : ∀ j < (stepO P w s).coins, w.cs j = w'.cs j) :
    stepO P w s = stepO P w' s := by
  refine stepO_eq_of_key P s horc ?_
  unfold stepKeyO
  rcases hP : P[s.pc]? with _ | ins
  · rfl
  · rcases ins with i | ⟨dst, src, prec⟩ | ⟨dst, prec, rng⟩
    · rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | ⟨dst, cnt⟩ | src | ⟨dst, prec⟩
      all_goals try rfl
      · have hc : (stepO P w s).coins = s.coins + (s.mem cnt).toNat := by
          unfold stepO
          rw [hP]
          simp only
          unfold step
          rw [lowerP_get' hP]
        simp only
        rw [readCoins_congr s.coins _ fun j _ hj => hcs j (by rw [hc]; exact hj)]
      · simp only
        rw [reading_congr s hfb]
    · rfl
    · simp only
      rw [reading_congr s hfb]

/-- M1, the run: with the same oracle, the same feedback at every state before step `k` and the same coins below the
coin count at step `k`, the runs agree up to step `k`. -/
theorem runO_congr (P : List InstrO) {w w' : WorldO d} (s0 : State d) (horc : w.orc = w'.orc) :
    ∀ k, (∀ k' < k, fbO w (runO P w s0 k') = fbO w' (runO P w s0 k')) →
      (∀ j < (runO P w s0 k).coins, w.cs j = w'.cs j) → runO P w s0 k = runO P w' s0 k
  | 0, _, _ => rfl
  | k + 1, hfb, hcs => by
    have hmono := (runO_mono P w s0 (Nat.le_add_right k 1)).2.1
    have ih := runO_congr P s0 horc k (fun k' hk' => hfb k' (by omega)) fun j hj => hcs j (by omega)
    rw [runO_succ, runO_succ, ← ih]
    refine stepO_congr P _ horc (hfb k (by omega)) fun j hj => hcs j ?_
    rwa [runO_succ]

/-- M1, the point of a round, general form: if the feedbacks agree at every state of the run in `w` with at most `t`
rounds played, and the coins agree below the coin count of every step reached from such states, the points of round
`t` agree. -/
theorem playedO_congr_gen (P : List InstrO) {w w' : WorldO d} (s0 : State d) (t : ℕ) (horc : w.orc = w'.orc)
    (hfb : ∀ k, (runO P w s0 k).rounds ≤ t → fbO w (runO P w s0 k) = fbO w' (runO P w s0 k))
    (hcs : ∀ k, (∀ k' ≤ k, (runO P w s0 k').rounds ≤ t) → ∀ j < (runO P w s0 (k + 1)).coins, w.cs j = w'.cs j) :
    playedO P w s0 t = playedO P w' s0 t := by
  -- the runs agree at every step before which the run in `w` has at most `t` rounds
  have hagree : ∀ k, (∀ k' < k, (runO P w s0 k').rounds ≤ t) → runO P w s0 k = runO P w' s0 k := by
    intro k hk
    rcases k with _ | k'
    · rfl
    · exact runO_congr P s0 horc (k' + 1) (fun k'' hk'' => hfb k'' (hk k'' hk''))
        (hcs k' fun k'' hk'' => hk k'' (by omega))
  by_cases hex : ∃ k, t < (runO P w s0 k).rounds
  · have hspec := Nat.find_spec hex
    have hmin : ∀ k' < Nat.find hex, (runO P w s0 k').rounds ≤ t := fun k' hk' =>
      not_lt.1 (Nat.find_min hex hk')
    have hK := hagree _ hmin
    rw [playedO_eq_pts P w s0 hspec, playedO_eq_pts P w' s0 (hK ▸ hspec), hK]
  · push Not at hex
    have hall : ∀ k, runO P w s0 k = runO P w' s0 k := fun k => hagree k fun k' _ => hex k'
    have hex' : ¬ ∃ k, t < (runO P w' s0 k).rounds := by
      rintro ⟨k, hk⟩
      rw [← hall k] at hk
      exact absurd (hex k) (not_le.2 hk)
    unfold playedO
    rw [dite_eq_right (by push Not; exact hex), dite_eq_right hex']

/-- M1, the point of a round: if the feedbacks agree at every state of the run in `w` with at most `t` rounds played,
those states read at most `N` coins, and the coins agree below `N`, the points of round `t` agree. -/
theorem playedO_congr (P : List InstrO) {w w' : WorldO d} (s0 : State d) (t N : ℕ) (horc : w.orc = w'.orc)
    (hfb : ∀ k, (runO P w s0 k).rounds ≤ t → fbO w (runO P w s0 k) = fbO w' (runO P w s0 k))
    (hcoin : ∀ k, (runO P w s0 k).rounds ≤ t → (runO P w s0 k).coins ≤ N)
    (hcs : ∀ j < N, w.cs j = w'.cs j) : playedO P w s0 t = playedO P w' s0 t := by
  refine playedO_congr_gen P s0 t horc hfb fun k hk j hj => hcs j (lt_of_lt_of_le hj ?_)
  obtain ⟨-, -, -, -, h5⟩ := stepO_facts P w (runO P w s0 k)
  rw [runO_succ]
  by_cases hr : (stepO P w (runO P w s0 k)).rounds ≤ t
  · have := hcoin (k + 1) (by rwa [runO_succ])
    rwa [runO_succ] at this
  · rw [h5 (by have := hk k le_rfl; have := (stepO_facts P w (runO P w s0 k)).2.1; omega)]
    exact hcoin k (hk k le_rfl)

/-- M1, the point of a round, with one coin stream: if the feedbacks agree at every state of the run in `w` with at most
`t` rounds played, the points of round `t` agree. -/
theorem playedO_congr_same (P : List InstrO) {w w' : WorldO d} (s0 : State d) (t : ℕ) (horc : w.orc = w'.orc)
    (hcs : w.cs = w'.cs)
    (hfb : ∀ k, (runO P w s0 k).rounds ≤ t → fbO w (runO P w s0 k) = fbO w' (runO P w s0 k)) :
    playedO P w s0 t = playedO P w' s0 t :=
  playedO_congr_gen P s0 t horc hfb fun _ _ j _ => congrFun hcs j

/-! ## M2: measurability -/

section Meas

variable (P : List InstrO) {Ω : Type*} [MeasurableSpace Ω] (g : Ω → WorldO d) (s0 : State d) (n : ℕ)

/-- The feedback read at every state reached with at most `n` rounds played is measurable in `ω`. -/
def FbMeasO : Prop :=
  ∀ k ω0, (runO P (g ω0) s0 k).rounds ≤ n → Measurable fun ω => fbO (g ω) (runO P (g ω0) s0 k)

theorem measurable_readCoins (c : ℕ) : ∀ k, Measurable fun cs : ℕ → Bool => readCoins cs c k
  | 0 => measurable_const
  | k + 1 => by
    simp only [readCoins]
    exact (measurable_const.mul (measurable_readCoins c k)).add
      ((Measurable.of_discrete (f := fun b : Bool => if b then (1 : ℤ) else 0)).comp (measurable_pi_apply _))

theorem measurable_stepKeyO (hcs : ∀ j, Measurable fun ω => (g ω).cs j) (s : State d)
    (hfb : Measurable fun ω => fbO (g ω) s) : Measurable fun ω => stepKeyO P (g ω) s := by
  have hcs' : Measurable fun ω => (g ω).cs := measurable_pi_iff.2 hcs
  have hread : ∀ p : ℕ, Measurable fun ω => reading (g ω).toW s p := fun p =>
    Int.measurable_floor.comp (measurable_const.mul hfb)
  unfold stepKeyO
  rcases hP : P[s.pc]? with _ | ins
  · exact measurable_const
  · rcases ins with i | ⟨dst, src, prec⟩ | ⟨dst, prec, rng⟩
    · rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | ⟨dst, cnt⟩ | src | ⟨dst, prec⟩
      all_goals try exact measurable_const
      · exact ((measurable_readCoins s.coins _).comp hcs').prodMk measurable_const
      · exact measurable_const.prodMk (hread _)
    · exact measurable_const
    · exact measurable_const.prodMk (hread _)

variable {P g s0 n}

/-- M2, the run: the state after `k` steps takes countably many values, and among the states with at most `n` rounds
played each is reached on a measurable event. -/
theorem runO_meas (orc : (Fin d → ℚ) → ℕ → Bool) (horc : ∀ ω, (g ω).orc = orc)
    (hcs : ∀ j, Measurable fun ω => (g ω).cs j) (hfb : FbMeasO P g s0 n) (k : ℕ) :
    (Set.range fun ω => runO P (g ω) s0 k).Countable ∧
      ∀ s : State d, s.rounds ≤ n → MeasurableSet {ω | runO P (g ω) s0 k = s} := by
  have hfac : ∀ (s : State d) ω ω', stepKeyO P (g ω) s = stepKeyO P (g ω') s →
      stepO P (g ω) s = stepO P (g ω') s := fun s ω ω' h =>
    stepO_eq_of_key P s ((horc ω).trans (horc ω').symm) h
  induction k with
  | zero =>
    refine ⟨(Set.countable_singleton s0).mono ?_, fun s _ => ?_⟩
    · rintro _ ⟨ω, rfl⟩
      simp [runO_zero]
    · by_cases h : s0 = s
      · convert MeasurableSet.univ
        ext ω
        simp [runO_zero, h]
      · convert MeasurableSet.empty
        ext ω
        simp [runO_zero, h]
  | succ k ih =>
    obtain ⟨hc, hm⟩ := ih
    refine ⟨?_, fun s' hs' => ?_⟩
    · have hsub : (Set.range fun ω => runO P (g ω) s0 (k + 1)) ⊆
          ⋃ s ∈ Set.range (fun ω => runO P (g ω) s0 k), Set.range fun ω => stepO P (g ω) s := by
        rintro _ ⟨ω, rfl⟩
        simp only [Set.mem_iUnion, Set.mem_range, exists_prop, exists_exists_eq_and]
        exact ⟨ω, ω, (runO_succ P (g ω) s0 k).symm⟩
      refine (hc.biUnion fun s _ => ?_).mono hsub
      exact countable_range_of_factor (fun ω => stepKeyO P (g ω) s) (hfac s)
    · have heq : {ω | runO P (g ω) s0 (k + 1) = s'} =
          ⋃ s ∈ Set.range (fun ω => runO P (g ω) s0 k) ∩ {s | s.rounds ≤ n},
            {ω | runO P (g ω) s0 k = s} ∩ ((fun ω => stepO P (g ω) s) ⁻¹' {s'}) := by
        ext ω
        simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_range, Set.mem_preimage,
          Set.mem_singleton_iff, exists_prop]
        constructor
        · intro h
          refine ⟨runO P (g ω) s0 k, ⟨⟨ω, rfl⟩, ?_⟩, rfl, ?_⟩
          · exact (runO_mono P (g ω) s0 (Nat.le_succ k)).1.trans (h ▸ hs')
          · rw [← runO_succ]
            exact h
        · rintro ⟨s, -, hs, hstep⟩
          rw [runO_succ, hs]
          exact hstep
      rw [heq]
      refine MeasurableSet.biUnion (hc.mono Set.inter_subset_left) ?_
      rintro s ⟨⟨ω0, rfl⟩, hsn⟩
      refine (hm _ hsn).inter ?_
      have hkey : Measurable fun ω => stepKeyO P (g ω) (runO P (g ω0) s0 k) :=
        measurable_stepKeyO P g hcs _ (hfb k ω0 hsn)
      exact measurableSet_preimage_of_factor hkey (hfac _) {s'}

/-- M2, the point of a round `t < n`: countably many values, each on a measurable event. -/
theorem playedO_meas (orc : (Fin d → ℚ) → ℕ → Bool) (horc : ∀ ω, (g ω).orc = orc)
    (hcs : ∀ j, Measurable fun ω => (g ω).cs j) (hfb : FbMeasO P g s0 n) (hs0 : s0.rounds = 0) {t : ℕ}
    (ht : t < n) :
    (Set.range fun ω => playedO P (g ω) s0 t).Countable ∧
      ∀ v : E d, MeasurableSet ((fun ω => playedO P (g ω) s0 t) ⁻¹' {v}) := by
  have hrun := runO_meas orc horc hcs hfb
  have hev : ∀ (k : ℕ) (S : Set (State d)), (∀ s ∈ S, s.rounds ≤ n) →
      MeasurableSet {ω | runO P (g ω) s0 k ∈ S} := by
    intro k S hS
    have : {ω | runO P (g ω) s0 k ∈ S} =
        ⋃ s ∈ Set.range (fun ω => runO P (g ω) s0 k) ∩ S, {ω | runO P (g ω) s0 k = s} := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_range, exists_prop]
      exact ⟨fun h => ⟨_, ⟨⟨ω, rfl⟩, h⟩, rfl⟩, fun ⟨s, ⟨_, hs⟩, h⟩ => h ▸ hs⟩
    rw [this]
    exact MeasurableSet.biUnion ((hrun k).1.mono Set.inter_subset_left) fun s hs => (hrun k).2 s (hS s hs.2)
  refine ⟨(Set.countable_range (toE : (Fin d → ℚ) → E d)).mono ?_, fun v => ?_⟩
  · rintro _ ⟨ω, rfl⟩
    obtain ⟨q, hq⟩ := playedO_rat P (g ω) s0 t
    exact ⟨q, hq.symm⟩
  have heq : (fun ω => playedO P (g ω) s0 t) ⁻¹' {v} =
      ({ω | ∀ k, runO P (g ω) s0 k ∈ {s : State d | s.rounds ≤ t}} ∩ {_ω | v = 0}) ∪
        ⋃ k, {ω | runO P (g ω) s0 k ∈ {s : State d | s.rounds ≤ t + 1 ∧ t < s.rounds ∧ toE (s.pts t) = v}} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_union, Set.mem_inter_iff, Set.mem_ofPred_eq,
      Set.mem_iUnion]
    constructor
    · intro hv
      by_cases h : ∃ k, t < (runO P (g ω) s0 k).rounds
      · right
        refine ⟨Nat.find h, ?_, Nat.find_spec h, ?_⟩
        · obtain ⟨j, hj⟩ : ∃ j, Nat.find h = j + 1 := by
            rcases hk : Nat.find h with _ | j
            · have := Nat.find_spec h
              rw [hk] at this
              simp [runO_zero, hs0] at this
            · exact ⟨j, rfl⟩
          have hmin : (runO P (g ω) s0 j).rounds ≤ t :=
            not_lt.mp (Nat.find_min h (by omega : j < Nat.find h))
          rw [hj, runO_succ]
          exact (stepO_facts P _ _).2.1.trans (by omega)
        · rw [← hv, playedO_eq_pts P (g ω) s0 (Nat.find_spec h)]
      · left
        push Not at h
        refine ⟨h, ?_⟩
        rw [← hv]
        unfold playedO
        rw [dite_eq_right (by push Not; exact h)]
    · rintro (⟨h, rfl⟩ | ⟨k, -, hk, hv⟩)
      · unfold playedO
        rw [dite_eq_right (by push Not; exact h)]
      · rw [playedO_eq_pts P (g ω) s0 hk, hv]
  rw [heq]
  have hA : {ω | ∀ k, runO P (g ω) s0 k ∈ {s : State d | s.rounds ≤ t}} =
      ⋂ k, {ω | runO P (g ω) s0 k ∈ {s : State d | s.rounds ≤ t}} := by
    ext ω
    simp
  rw [hA]
  refine ((MeasurableSet.iInter fun k => hev k {s : State d | s.rounds ≤ t} fun s hs => le_trans hs ht.le).inter
    ?_).union (MeasurableSet.iUnion fun k =>
      hev k {s : State d | s.rounds ≤ t + 1 ∧ t < s.rounds ∧ toE (s.pts t) = v} fun s hs => by
        simp only [Set.mem_ofPred_eq] at hs
        exact hs.1.trans (by omega))
  by_cases hv : v = 0
  · simp [hv]
  · simp [hv]

/-- M2: the point of a round `t < n` is a measurable function of `ω`. -/
theorem measurable_playedO (orc : (Fin d → ℚ) → ℕ → Bool) (horc : ∀ ω, (g ω).orc = orc)
    (hcs : ∀ j, Measurable fun ω => (g ω).cs j) (hfb : FbMeasO P g s0 n) (hs0 : s0.rounds = 0) {t : ℕ}
    (ht : t < n) : Measurable fun ω => playedO P (g ω) s0 t := by
  obtain ⟨h1, h2⟩ := playedO_meas orc horc hcs hfb hs0 ht
  exact measurable_of_fibers h1 fun q _ => h2 q

end Meas

end AdversarialBco.Unified.RunFacts
