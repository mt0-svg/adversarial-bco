/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.StatementConj1Bit
public import AdversarialBco.Conj1Bit.Sanity
public import AdversarialBco.Poly.Df2PropGAdTools
public import AdversarialBco.Bit.Transfer.XCoins

@[expose] public section

/-!
# The regret of any bit program is measurable

`measurable_regret`: against a randomised adaptive adversary `σ` (`RandAdv`) on a convex body `K` with nonempty
interior, if a program `P` plays its rounds `t < n` in `K` on every run, its regret over `n` rounds is a measurable
function of the seed and the coins. No other hypothesis on `P`.

The argument of StatementConj1Bit.lean ("The regret and the expectation"), made exact:
* a step reads the world through one integer only, the one read by `coins` or by `obs` (`step_eq_of_stepKey`); so
  the state after `k` steps takes countably many values, and at each state with at most `n` rounds played the event
  of reaching it is measurable (`runBit_meas`), by induction on `k`: the feedback read at a state reached with
  `r ≤ n` rounds is the loss of round `r - 1 < n` at a point of `K` on a rational history, measurable in the seed by
  `RandAdv` (`fbMeas_of_randAdv`);
* hence the point played in round `t < n` takes countably many values, each on a measurable event
  (`playedBit_meas`);
* on each value `Q` of the points of the rounds `t < n` the regret is a measurable function of the seed: the losses at
  the points of `Q` by `RandAdv`, the infimum over `K` as the infimum over the rational points of the interior
  (`sInf_image_eq_iInf_rat`) (`measurable_regQ`); the regret is measurable
  (`measurable_of_countable_fibers`).
-/

open MeasureTheory

namespace AdversarialBco.Bit.RegMeas

open AdversarialBco.BitRAM AdversarialBco.BitRAM.Conj1BitSanity
open AdversarialBco.RealRAM (Strategy lossAd regretPts)

/-! ## Generic measurability -/

theorem measurableSet_preimage_of_factor {Ω C Y : Type*} [MeasurableSpace Ω] [MeasurableSpace C] [Countable C]
    [MeasurableSingletonClass C] {k : Ω → C} (hk : Measurable k) {f : Ω → Y}
    (hf : ∀ ω ω', k ω = k ω' → f ω = f ω') (T : Set Y) : MeasurableSet (f ⁻¹' T) := by
  set S : Set C := {c | ∃ ω, k ω = c ∧ f ω ∈ T} with hS
  have h_eq : f ⁻¹' T = k ⁻¹' S := by
    ext ω
    constructor
    · intro hω
      have hωT : f ω ∈ T := hω
      refine ⟨ω, ?_, hωT⟩
      rfl
    · intro hω
      have hkS : k ω ∈ S := hω
      rcases hkS with ⟨ω', hkω', hfω'⟩
      have h_eq_f : f ω = f ω' := hf ω ω' hkω'.symm
      simpa [h_eq_f] using hfω'
  rw [h_eq]
  have hS_meas : MeasurableSet S := MeasurableSet.of_discrete
  exact hk hS_meas

theorem countable_range_of_factor {Ω C Y : Type*} [Countable C] (k : Ω → C) {f : Ω → Y}
    (hf : ∀ ω ω', k ω = k ω' → f ω = f ω') : (Set.range f).Countable := by
  by_cases h_ne : Nonempty Ω
  · have := h_ne
    let g : C → Y := f ∘ Function.invFun k
    have hfg : ∀ ω, f ω = g (k ω) := by
      intro ω
      dsimp [g]
      have h_eq : k (Function.invFun k (k ω)) = k ω := Function.invFun_eq ⟨ω, rfl⟩
      symm; apply hf; exact h_eq
    have h_range : Set.range f = g '' Set.range k := by
      ext y; constructor
      · rintro ⟨ω, rfl⟩
        refine ⟨k ω, ⟨ω, rfl⟩, ?_⟩
        exact (hfg ω).symm
      · rintro ⟨c, ⟨ω, rfl⟩, rfl⟩
        exact ⟨ω, hfg ω⟩
    rw [h_range]
    have h_countable_range_k : (Set.range k).Countable := by
      have h_univ : (Set.univ : Set C).Countable := Set.countable_univ
      exact Set.Countable.mono (Set.subset_univ _) h_univ
    exact h_countable_range_k.image g
  · have := not_nonempty_iff.mp h_ne
    have h_empty : Set.range f = (∅ : Set Y) := by
      ext y; constructor
      · rintro ⟨ω, rfl⟩; exact isEmptyElim ω
      · rintro ⟨⟩
    rw [h_empty]
    exact Set.countable_empty

theorem measurable_of_countable_fibers {Ω Q Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Y] {X : Ω → Q}
    (hX : (Set.range X).Countable) (hfib : ∀ q ∈ Set.range X, MeasurableSet (X ⁻¹' {q})) {G : Q → Ω → Y}
    (hG : ∀ q ∈ Set.range X, Measurable (G q)) : Measurable fun ω => G (X ω) ω := by
  intro U hU
  have h_eq : (fun ω => G (X ω) ω) ⁻¹' U = ⋃ q ∈ Set.range X, (X ⁻¹' {q}) ∩ (G q ⁻¹' U) := by
    ext ω
    constructor
    · intro hω
      have hq : X ω ∈ Set.range X := ⟨ω, rfl⟩
      refine Set.mem_biUnion hq ?_
      refine ⟨?_, ?_⟩
      · exact Set.mem_preimage.mpr rfl
      · exact hω
    · intro hω
      rcases Set.mem_iUnion₂.1 hω with ⟨q, hq, hω'⟩
      rcases (Set.mem_inter_iff _ _ _).mp hω' with ⟨hXq, hGq⟩
      have hXωq : X ω = q := by
        simpa using hXq
      simpa [hXωq] using hGq
  rw [h_eq]
  refine MeasurableSet.biUnion hX ?_
  intro q hq
  refine MeasurableSet.inter (hfib q hq) ?_
  exact hG q hq hU

theorem tuple_fibers {Ω Y : Type*} [MeasurableSpace Ω] {n : ℕ} {X : Fin n → Ω → Y}
    (hX : ∀ t, (Set.range (X t)).Countable) (hfib : ∀ t v, MeasurableSet (X t ⁻¹' {v})) :
    (Set.range fun ω t => X t ω).Countable ∧ ∀ v : Fin n → Y, MeasurableSet ((fun ω t => X t ω) ⁻¹' {v}) := by
  constructor
  · -- prove countability of the range
    have h_subset : Set.range (fun ω t => X t ω) ⊆ Set.pi Set.univ (fun t => Set.range (X t)) := by
      intro f hf
      rcases hf with ⟨ω, rfl⟩
      intro t ht
      exact ⟨ω, rfl⟩
    have h_countable_pi : (Set.pi Set.univ (fun t => Set.range (X t))).Countable := by
      apply Set.countable_univ_pi
      intro t
      exact hX t
    exact Set.Countable.mono h_subset h_countable_pi
  · -- prove measurability of fibers
    intro v
    have h_eq : (fun ω t => X t ω) ⁻¹' {v} = ⋂ t, X t ⁻¹' {v t} := by
      ext ω
      simp [Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff, funext_iff]
    rw [h_eq]
    apply MeasurableSet.iInter
    intro t
    exact hfib t (v t)

/-! ## What a step reads -/

/-- What a step reads off the world: the integer read by `coins`, or the reading of `obs`; `(0, 0)` otherwise. -/
noncomputable def stepKey (P : List Instr) {d : ℕ} (w : World d) (s : State d) : ℤ × ℤ :=
  match P[s.pc]? with
  | some (.coins _ cnt) => (readCoins w.cs s.coins (s.mem cnt).toNat, 0)
  | some (.obs _ prec) => (0, reading w s (s.mem prec).toNat)
  | _ => (0, 0)

theorem step_eq_of_stepKey (P : List Instr) {d : ℕ} {w w' : World d} (s : State d)
    (h : stepKey P w s = stepKey P w' s) : step P w s = step P w' s := by
  simp only [step, stepKey] at h ⊢
  cases hP : P[s.pc]?
  · rfl
  · case some ins =>
    simp only [hP] at h ⊢
    cases ins with
    | const => rfl
    | add => rfl
    | sub => rfl
    | mul => rfl
    | div => rfl
    | load => rfl
    | store => rfl
    | jlt => rfl
    | jmp => rfl
    | coins dst cnt =>
        have hread : readCoins w.cs s.coins (s.mem cnt).toNat = readCoins w'.cs s.coins (s.mem cnt).toNat := by
          simpa using congrArg Prod.fst h
        simp [hread]
    | play => rfl
    | obs dst prec =>
        have hread : reading w s (s.mem prec).toNat = reading w' s (s.mem prec).toNat := by
          simpa using congrArg Prod.snd h
        simp [hread]

theorem step_rounds_le_succ (P : List Instr) {d : ℕ} (w : World d) (s : State d) :
    (step P w s).rounds ≤ s.rounds + 1 := by
  unfold step
  split
  · omega
  · split <;> simp

theorem playedBit_eq_pts (P : List Instr) {d : ℕ} (g : GameBit d) (s0 : State d) {t k : ℕ}
    (h : t < (runBit P g s0 k).rounds) : playedBit P g s0 t = toE ((runBit P g s0 k).pts t) := by
  have hex : ∃ k', t < (runBit P g s0 k').rounds := ⟨k, h⟩
  unfold playedBit
  rw [dite_eq_left hex]
  set k0 := Nat.find hex with hk0_def
  have hk0_le_k : k0 ≤ k := Nat.find_min' hex h
  have h_rounds_k0 : t < (runBit P g s0 k0).rounds := Nat.find_spec hex
  have h_mono := runBit_mono P g s0 hk0_le_k
  have h_pts_eq := h_mono.2 t h_rounds_k0
  rw [h_pts_eq]

theorem playedBit_rat (P : List Instr) {d : ℕ} (g : GameBit d) (s0 : State d) (t : ℕ) :
    ∃ q : Fin d → ℚ, playedBit P g s0 t = toE q := by
  unfold playedBit
  split_ifs with h
  · refine ⟨(runBit P g s0 (Nat.find h)).pts t, rfl⟩
  · refine ⟨0, ?_⟩
    ext i
    simp [toE]

/-! ## The run -/

section Run

variable {d : ℕ} (P : List Instr) {Ω : Type*} [MeasurableSpace Ω] (g : Ω → GameBit d) (s0 : State d) (n : ℕ)

/-- The feedback read at every state reached with at most `n` rounds played is measurable in `ω`. -/
def FbMeas : Prop :=
  ∀ k ω0, (runBit P (g ω0) s0 k).rounds ≤ n →
    Measurable fun ω => feedback ((g ω).world (runBit P (g ω0) s0 k).pts) (runBit P (g ω0) s0 k)

theorem measurable_stepKey (hcs : ∀ j, Measurable fun ω => (g ω).cs j) (s : State d)
    (hfb : Measurable fun ω => feedback ((g ω).world s.pts) s) :
    Measurable fun ω => stepKey P ((g ω).world s.pts) s := by
  unfold stepKey
  -- Split on whether P[s.pc]? is none or some instruction
  cases hpc : P[s.pc]? with
  | none =>
    -- Goal: Measurable fun ω => (0, 0)
    exact measurable_const
  | some ins =>
    -- Split on the instruction type
    cases ins with
    | const _ _ => exact measurable_const
    | add _ _ => exact measurable_const
    | sub _ _ => exact measurable_const
    | mul _ _ => exact measurable_const
    | div _ _ => exact measurable_const
    | load _ _ => exact measurable_const
    | store _ _ => exact measurable_const
    | jlt _ _ _ => exact measurable_const
    | jmp _ => exact measurable_const
    | coins dst cnt =>
      -- Goal: Measurable fun ω => (readCoins ((g ω).world s.pts).cs s.coins (s.mem cnt).toNat, 0)
      -- Note: ((g ω).world s.pts).cs = (g ω).cs
      have h_world_cs : ∀ ω, ((g ω).world s.pts).cs = (g ω).cs := by
        intro ω; rfl
      simp [h_world_cs]
      -- Now goal: Measurable fun ω => (readCoins (g ω).cs s.coins (s.mem cnt).toNat, 0)
      -- We need to show the first component is measurable
      have h_readCoins : Measurable (fun (cs : ℕ → Bool) => readCoins cs s.coins (s.mem cnt).toNat) := by
        -- Prove by induction on the third argument
        induction' (s.mem cnt).toNat with k ih
        · -- k = 0: readCoins cs s.coins 0 = 0
          simp [readCoins]
        · -- k = k+1
          -- readCoins cs s.coins (k+1) = 2 * readCoins cs s.coins k + (if cs (s.coins + k) then 1 else 0)
          have h_eq : (fun (cs : ℕ → Bool) => readCoins cs s.coins (k + 1)) =
                      (fun cs => 2 * readCoins cs s.coins k + (if cs (s.coins + k) then (1 : ℤ) else 0)) := by
            ext cs; simp [readCoins]
          rw [h_eq]
          refine Measurable.add ?_ ?_
          · -- 2 * readCoins cs s.coins k
            refine Measurable.mul ?_ ih
            exact measurable_const
          · -- if cs (s.coins + k) then 1 else 0
            -- Need to show this is measurable
            set j := s.coins + k with hj
            have h_bool_fn : Measurable (fun (b : Bool) => if b then (1 : ℤ) else 0) := by
              apply Measurable.of_discrete
            have h_proj : Measurable (fun (cs : ℕ → Bool) => cs j) := measurable_pi_apply j
            exact h_bool_fn.comp h_proj
      -- Now compose with g
      have h_cs_meas : Measurable (fun ω => (g ω).cs) := by
        refine (measurable_pi_iff.mpr ?_)
        intro j
        exact hcs j
      exact (h_readCoins.comp h_cs_meas).prodMk measurable_const
    | play _ => exact measurable_const
    | obs dst prec =>
      -- Goal: Measurable fun ω => (0, reading ((g ω).world s.pts) s (s.mem prec).toNat)
      simp [reading]
      -- Goal: Measurable fun ω => (0, ⌊(2 : ℝ) ^ (s.mem prec).toNat * feedback ((g ω).world s.pts) s⌋)
      -- The first component is constant
      -- For the second component: Int.floor of a measurable ℝ-valued function
      have h_floor : Measurable (fun ω => (⌊(2 : ℝ) ^ (s.mem prec).toNat * feedback ((g ω).world s.pts) s⌋ : ℤ)) := by
        apply Int.measurable_floor.comp
        refine Measurable.mul ?_ hfb
        exact measurable_const
      exact measurable_const.prodMk h_floor

theorem runBit_meas (hcs : ∀ j, Measurable fun ω => (g ω).cs j) (hfb : FbMeas P g s0 n) (k : ℕ) :
    (Set.range fun ω => runBit P (g ω) s0 k).Countable ∧
      ∀ s : State d, s.rounds ≤ n → MeasurableSet {ω | runBit P (g ω) s0 k = s} := by
  have hfac : ∀ (s : State d) ω ω', stepKey P ((g ω).world s.pts) s = stepKey P ((g ω').world s.pts) s →
      stepBit P (g ω) s = stepBit P (g ω') s := fun s _ _ h => step_eq_of_stepKey P s h
  induction k with
  | zero =>
    refine ⟨(Set.countable_singleton s0).mono ?_, fun s _ => ?_⟩
    · rintro _ ⟨ω, rfl⟩
      simp [runBit]
    · by_cases h : s0 = s
      · convert MeasurableSet.univ
        ext ω
        simp [runBit, h]
      · convert MeasurableSet.empty
        ext ω
        simp [runBit, h]
  | succ k ih =>
    obtain ⟨hc, hm⟩ := ih
    refine ⟨?_, fun s' hs' => ?_⟩
    · have hsub : (Set.range fun ω => runBit P (g ω) s0 (k + 1)) ⊆
          ⋃ s ∈ Set.range (fun ω => runBit P (g ω) s0 k), Set.range fun ω => stepBit P (g ω) s := by
        rintro _ ⟨ω, rfl⟩
        simp only [Set.mem_iUnion, Set.mem_range, exists_prop, exists_exists_eq_and]
        exact ⟨ω, ω, (runBit_succ P (g ω) s0 k).symm⟩
      refine (hc.biUnion fun s _ => ?_).mono hsub
      exact countable_range_of_factor (fun ω => stepKey P ((g ω).world s.pts) s) (hfac s)
    · have heq : {ω | runBit P (g ω) s0 (k + 1) = s'} =
          ⋃ s ∈ Set.range (fun ω => runBit P (g ω) s0 k) ∩ {s | s.rounds ≤ n},
            {ω | runBit P (g ω) s0 k = s} ∩ ((fun ω => stepBit P (g ω) s) ⁻¹' {s'}) := by
        ext ω
        simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_range, Set.mem_preimage,
          Set.mem_singleton_iff, exists_prop]
        constructor
        · intro h
          refine ⟨runBit P (g ω) s0 k, ⟨⟨ω, rfl⟩, ?_⟩, rfl, ?_⟩
          · exact (runBit_mono P (g ω) s0 (Nat.le_succ k)).1.trans (h ▸ hs')
          · rw [← runBit_succ]
            exact h
        · rintro ⟨s, -, hs, hstep⟩
          rw [runBit_succ, hs]
          exact hstep
      rw [heq]
      refine MeasurableSet.biUnion (hc.mono Set.inter_subset_left) ?_
      rintro s ⟨⟨ω0, rfl⟩, hsn⟩
      refine (hm _ hsn).inter ?_
      have hkey : Measurable fun ω => stepKey P ((g ω).world (runBit P (g ω0) s0 k).pts) (runBit P (g ω0) s0 k) :=
        measurable_stepKey P g hcs _ (hfb k ω0 hsn)
      exact measurableSet_preimage_of_factor hkey (hfac _) {s'}

theorem playedBit_meas (hcs : ∀ j, Measurable fun ω => (g ω).cs j) (hfb : FbMeas P g s0 n)
    (hs0 : s0.rounds = 0) {t : ℕ} (ht : t < n) :
    (Set.range fun ω => playedBit P (g ω) s0 t).Countable ∧
      ∀ v : E d, MeasurableSet ((fun ω => playedBit P (g ω) s0 t) ⁻¹' {v}) := by
  have hrun := runBit_meas P g s0 n hcs hfb
  -- an event on the state after `k` steps, among the states with at most `n` rounds, is measurable
  have hev : ∀ (k : ℕ) (S : Set (State d)), (∀ s ∈ S, s.rounds ≤ n) →
      MeasurableSet {ω | runBit P (g ω) s0 k ∈ S} := by
    intro k S hS
    have : {ω | runBit P (g ω) s0 k ∈ S} =
        ⋃ s ∈ Set.range (fun ω => runBit P (g ω) s0 k) ∩ S, {ω | runBit P (g ω) s0 k = s} := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_range, exists_prop]
      exact ⟨fun h => ⟨_, ⟨⟨ω, rfl⟩, h⟩, rfl⟩, fun ⟨s, ⟨_, hs⟩, h⟩ => h ▸ hs⟩
    rw [this]
    exact MeasurableSet.biUnion ((hrun k).1.mono Set.inter_subset_left) fun s hs => (hrun k).2 s (hS s hs.2)
  refine ⟨(Set.countable_range (toE : (Fin d → ℚ) → E d)).mono ?_, fun v => ?_⟩
  · rintro _ ⟨ω, rfl⟩
    obtain ⟨q, hq⟩ := playedBit_rat P (g ω) s0 t
    exact ⟨q, hq.symm⟩
  have heq : (fun ω => playedBit P (g ω) s0 t) ⁻¹' {v} =
      ({ω | ∀ k, runBit P (g ω) s0 k ∈ {s : State d | s.rounds ≤ t}} ∩ {_ω | v = 0}) ∪
        ⋃ k, {ω | runBit P (g ω) s0 k ∈ {s : State d | s.rounds ≤ t + 1 ∧ t < s.rounds ∧ toE (s.pts t) = v}} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_union, Set.mem_inter_iff, Set.mem_ofPred_eq,
      Set.mem_iUnion]
    constructor
    · intro hv
      by_cases h : ∃ k, t < (runBit P (g ω) s0 k).rounds
      · right
        refine ⟨Nat.find h, ?_, Nat.find_spec h, ?_⟩
        · obtain ⟨j, hj⟩ : ∃ j, Nat.find h = j + 1 := by
            rcases hk : Nat.find h with _ | j
            · have := Nat.find_spec h
              rw [hk] at this
              simp [runBit, hs0] at this
            · exact ⟨j, rfl⟩
          have hmin : (runBit P (g ω) s0 j).rounds ≤ t :=
            not_lt.mp (Nat.find_min h (by omega : j < Nat.find h))
          rw [hj, runBit_succ, stepBit]
          exact (step_rounds_le_succ P _ _).trans (by omega)
        · rw [← hv, playedBit_eq_pts P (g ω) s0 (Nat.find_spec h)]
      · left
        push Not at h
        refine ⟨h, ?_⟩
        rw [← hv, playedBit, dite_eq_right (by push Not; exact h)]
    · rintro (⟨h, rfl⟩ | ⟨k, -, hk, hv⟩)
      · rw [playedBit, dite_eq_right (by push Not; exact h)]
      · rw [playedBit_eq_pts P (g ω) s0 hk, hv]
  rw [heq, Set.ofPred_forall]
  refine ((MeasurableSet.iInter fun k => hev k {s : State d | s.rounds ≤ t} fun s hs => le_trans hs ht.le).inter
    ?_).union (MeasurableSet.iUnion fun k =>
      hev k {s : State d | s.rounds ≤ t + 1 ∧ t < s.rounds ∧ toE (s.pts t) = v} fun s hs => by
        simp only [Set.mem_ofPred_eq] at hs
        exact hs.1.trans (by omega))
  by_cases hv : v = 0
  · simp [hv]
  · simp [hv]
end Run

/-! ## The regret -/

/-- The game of the seed and the coins. -/
def gameOf {d : ℕ} {Θ : Type} (σ : Θ → Strategy d) (ω : Θ × (ℕ → Bool)) : GameBit d := ⟨σ ω.1, ω.2⟩

theorem fbMeas_of_randAdv (P : List Instr) {d n : ℕ} {Θ : Type} [MeasurableSpace Θ] (K : Set (E d))
    (σ : Θ → Strategy d) (hσ : RandAdv K n σ) (s0 : State d)
    (hplay : ∀ θ cs, ∀ t < n, playedBit P ⟨σ θ, cs⟩ s0 t ∈ K) : FbMeas P (gameOf σ) s0 n := by
  unfold FbMeas
  intro k ω0 hk
  set s := runBit P (gameOf σ ω0) s0 k with hs
  unfold feedback
  split
  · exact measurable_const
  · rename_i h
    have hpos : s.rounds ≠ 0 := h
    have hpos' : 1 ≤ s.rounds := Nat.one_le_of_lt (Nat.pos_of_ne_zero hpos)
    set t := s.rounds - 1 with ht
    have ht_lt_rounds : t < s.rounds := Nat.sub_lt hpos' (by omega)
    have ht_lt_n : t < n := Nat.lt_of_lt_of_le ht_lt_rounds hk
    have h_eq_pts := playedBit_eq_pts P (gameOf σ ω0) s0 ht_lt_rounds
    have h_pts_t_in_K : toE (s.pts t) ∈ K := by
      have h_play_in_K := hplay ω0.1 ω0.2 t ht_lt_n
      have h_game_eq : (gameOf σ ω0 : GameBit d) = { σ := σ ω0.1, cs := ω0.2 } := rfl
      have h_play_in_K' : playedBit P (gameOf σ ω0) s0 t ∈ K := by
        simpa [h_game_eq] using h_play_in_K
      rw [← h_eq_pts]
      exact h_play_in_K'
    have h_rand := hσ t ht_lt_n
    have h_meas := (h_rand (s.pts)).2 (toE (s.pts t)) h_pts_t_in_K
    show Measurable fun ω => ((gameOf σ ω).world s.pts).f t (toE (s.pts t))
    have : ((fun ω => ((gameOf σ ω).world s.pts).f t (toE (s.pts t))) : (Θ × (ℕ → Bool)) → ℝ) =
           (fun θ => lossAd (σ θ) 0 (fun i => toE (s.pts i)) t (toE (s.pts t))) ∘ Prod.fst := by
      ext ω
      simp [gameOf, GameBit.world]
    rw [this]
    exact Measurable.comp h_meas measurable_fst

/-- The points of the rounds `t < n`, extended by `0`. -/
def extQ {d n : ℕ} (Q : Fin n → E d) (i : ℕ) : E d := if h : i < n then Q ⟨i, h⟩ else 0

theorem regret_eq_extQ {d n : ℕ} (K : Set (E d)) (σ : Strategy d) (x : ℕ → E d) :
    regretPts K (lossAd σ 0 x) x n =
      regretPts K (lossAd σ 0 (extQ fun t : Fin n => x t)) (extQ fun t : Fin n => x t) n := by
  unfold regretPts
  have h_extQ_val : ∀ i, i < n → (extQ fun t : Fin n => x t) i = x i := by
    intro i hi
    unfold extQ
    simp [hi]
  have h_lossAd_eq : ∀ t, t < n → lossAd σ 0 x t = lossAd σ 0 (extQ fun t : Fin n => x t) t := by
    intro t ht
    apply lossAd_prefix σ 0 t
    intro i hi
    have hi_n : i < n := lt_of_lt_of_le hi (by omega)
    rw [← (h_extQ_val i hi_n)]
  have h_sum_eq : (∑ t ∈ Finset.range n, (lossAd σ 0 x) t (x t)) =
      (∑ t ∈ Finset.range n, (lossAd σ 0 (extQ fun t : Fin n => x t)) t ((extQ fun t : Fin n => x t) t)) := by
    refine Finset.sum_congr rfl fun t ht => ?_
    have ht' : t < n := Finset.mem_range.1 ht
    rw [h_extQ_val t ht', h_lossAd_eq t ht']
  have h_fun_eq : (fun y => ∑ t ∈ Finset.range n, (lossAd σ 0 x) t y) =
      (fun y => ∑ t ∈ Finset.range n, (lossAd σ 0 (extQ fun t : Fin n => x t)) t y) := by
    ext y
    refine Finset.sum_congr rfl fun t ht => ?_
    have ht' : t < n := Finset.mem_range.1 ht
    rw [h_lossAd_eq t ht']
  rw [h_sum_eq, h_fun_eq]

theorem measurable_regQ {d n : ℕ} {Θ : Type} [MeasurableSpace Θ] (K : Set (E d)) (hK : (interior K).Nonempty)
    (σ : Θ → Strategy d) (hσ : RandAdv K n σ) (Q : Fin n → E d) (hQK : ∀ t, Q t ∈ K)
    (hQ : ∀ t, ∃ q : Fin d → ℚ, Q t = toE q) :
    Measurable fun θ => regretPts K (lossAd (σ θ) 0 (extQ Q)) (extQ Q) n := by
  classical
  let qs : ℕ → Fin d → ℚ := fun i => if h : i < n then (hQ ⟨i, h⟩).choose else 0
  have hext : extQ Q = fun i => toE (qs i) := by
    funext i
    by_cases h : i < n
    · simp only [extQ, qs, h, dite_true]
      exact (hQ ⟨i, h⟩).choose_spec
    · simp only [extQ, qs, h, dite_false]
      ext j
      simp [toE]
  simp only [hext]
  unfold regretPts
  refine Measurable.sub ?_ ?_
  · refine Finset.measurable_sum _ fun t ht => ?_
    have ht' := Finset.mem_range.mp ht
    have hmem : toE (qs t) ∈ K := by
      have := congrFun hext t
      simp only [extQ, ht', dite_true] at this
      rw [← this]; exact hQK _
    exact (hσ t ht' qs).2 _ hmem
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [Finset.range_zero, Finset.sum_empty]
      exact measurable_const
    have key : ∀ θ, sInf ((fun y => ∑ t ∈ Finset.range n, lossAd (σ θ) 0 (fun i => toE (qs i)) t y) '' K) =
        ⨅ q : Fin d → ℚ, if (WithLp.toLp 2 (fun i => (q i : ℝ)) : E d) ∈ interior K then
          ∑ t ∈ Finset.range n, lossAd (σ θ) 0 (fun i => toE (qs i)) t (WithLp.toLp 2 (fun i => (q i : ℝ)))
          else (n : ℝ) := by
      intro θ
      have hKc : Convex ℝ K := ((hσ 0 hn qs).1 θ).1.1
      have hcv := Poly.PropGAd.convexOn_sum_range K hKc n (lossAd (σ θ) 0 (fun i => toE (qs i)))
        (fun t ht => ((hσ t ht qs).1 θ).1) (fun t ht => ((hσ t ht qs).1 θ).2)
      exact Poly.PropGAd.sInf_image_eq_iInf_rat K hK _ hcv.1 n hcv.2
    simp only [key]
    refine Measurable.iInf fun q => ?_
    split_ifs with hq
    · exact Finset.measurable_sum _ fun t ht => (hσ t (Finset.mem_range.mp ht) qs).2 _ (interior_subset hq)
    · exact measurable_const

/-- (REG-MEAS): the regret of any program that plays its rounds `t < n` in `K` on every run is measurable in the
seed and the coins. -/
theorem measurable_regret (P : List Instr) {d n : ℕ} {Θ : Type} [MeasurableSpace Θ] (K : Set (E d))
    (hK : (interior K).Nonempty) (σ : Θ → Strategy d) (hσ : RandAdv K n σ) (s0 : State d) (hs0 : s0.rounds = 0)
    (hplay : ∀ θ cs, ∀ t < n, playedBit P ⟨σ θ, cs⟩ s0 t ∈ K) :
    Measurable fun ω : Θ × (ℕ → Bool) =>
      regretPts K (lossAd (σ ω.1) 0 (playedBit P ⟨σ ω.1, ω.2⟩ s0)) (playedBit P ⟨σ ω.1, ω.2⟩ s0) n := by
  have hcs : ∀ j, Measurable fun ω : Θ × (ℕ → Bool) => (gameOf σ ω).cs j := fun j =>
    (measurable_pi_apply j).comp measurable_snd
  have hfb := fbMeas_of_randAdv P K σ hσ s0 hplay
  have hX := tuple_fibers (X := fun (t : Fin n) (ω : Θ × (ℕ → Bool)) => playedBit P (gameOf σ ω) s0 t)
    (fun t => (playedBit_meas P (gameOf σ) s0 n hcs hfb hs0 t.2).1)
    (fun t v => (playedBit_meas P (gameOf σ) s0 n hcs hfb hs0 t.2).2 v)
  have key : (fun ω : Θ × (ℕ → Bool) =>
      regretPts K (lossAd (σ ω.1) 0 (playedBit P ⟨σ ω.1, ω.2⟩ s0)) (playedBit P ⟨σ ω.1, ω.2⟩ s0) n) =
      fun ω => (fun (Q : Fin n → E d) (ω : Θ × (ℕ → Bool)) =>
        regretPts K (lossAd (σ ω.1) 0 (extQ Q)) (extQ Q) n) ((fun ω (t : Fin n) => playedBit P (gameOf σ ω) s0 t) ω) ω := by
    funext ω
    exact regret_eq_extQ K (σ ω.1) _
  rw [key]
  refine measurable_of_countable_fibers (Y := ℝ)
    (G := fun (Q : Fin n → E d) (ω : Θ × (ℕ → Bool)) => regretPts K (lossAd (σ ω.1) 0 (extQ Q)) (extQ Q) n)
    hX.1 (fun q _ => hX.2 q) ?_
  rintro Q ⟨ω0, rfl⟩
  exact (measurable_regQ K hK σ hσ _ (fun t => hplay ω0.1 ω0.2 t t.2)
    (fun t => playedBit_rat P _ s0 t)).comp measurable_fst
end AdversarialBco.Bit.RegMeas
