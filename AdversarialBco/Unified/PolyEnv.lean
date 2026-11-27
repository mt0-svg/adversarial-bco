/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.PolyMach

@[expose] public section

/-!
# UNI-POLY: the environment of a randomised adversary for Theorem U (`env_noisy`)
-/

open MeasureTheory ProbabilityTheory

namespace AdversarialBco.UniPoly

open BitRAM BitRAMO Unified
open RealRAM (Strategy lossAd regretPts polytope HeightLE)
open Bit.Asm (InputOK)
open Bit.Transfer (B.run_add)

variable {d : ℕ}

open UnifiedSanity (coordσ le_coordσ coordσ_le coordσ_indep)

/-! ## Coins cut at an index, and causality -/

/-- The coins below `N`, then tails. -/
def trunc (N : ℕ) (cs : ℕ → Bool) : ℕ → Bool := fun j => if j < N then cs j else false

theorem step_coins_le (P : List Instr) (w : World d) (s : State d) : s.coins ≤ (step P w s).coins := by
  unfold step
  split
  · exact le_rfl
  · split <;> simp only <;> omega

/-- A step reads the coins below the coin count after it only. -/
theorem step_cs_congr (P : List Instr) (f : ℕ → E d → ℝ) {cs cs' : ℕ → Bool} (s : State d)
    (h : ∀ j < (step P ⟨f, cs⟩ s).coins, cs j = cs' j) : step P ⟨f, cs⟩ s = step P ⟨f, cs'⟩ s := by
  unfold step at h ⊢
  rcases hP : P[s.pc]? with _ | ins
  · rfl
  · rw [hP] at h
    cases ins
    case coins dst cnt =>
      simp only at h ⊢
      rw [RunFacts.readCoins_congr s.coins _ (fun j _ h2 => h j h2)]
    all_goals rfl

/-- The run against a strategy reads the coins below its coin count only. -/
theorem runBit_cs_congr (P : List Instr) (σ : Strategy d) {cs cs' : ℕ → Bool} (s0 : State d) :
    ∀ j, (∀ i < (runBit P ⟨σ, cs⟩ s0 j).coins, cs i = cs' i) →
      runBit P ⟨σ, cs⟩ s0 j = runBit P ⟨σ, cs'⟩ s0 j
  | 0, _ => rfl
  | j + 1, h => by
    have hle : (runBit P ⟨σ, cs⟩ s0 j).coins ≤ (runBit P ⟨σ, cs⟩ s0 (j + 1)).coins := by
      rw [Conj1BitSanity.runBit_succ]; exact step_coins_le _ _ _
    have ih := runBit_cs_congr P σ s0 j fun i hi => h i (by omega)
    rw [Conj1BitSanity.runBit_succ] at h ⊢
    rw [Conj1BitSanity.runBit_succ, ← ih]
    exact step_cs_congr P _ _ h

/-- The plays of the rounds `t' < t` read the coins below both windows of round `t` only. -/
theorem plays_trunc (P : List InstrO) {n m M : ℕ} {A : Matrix (Fin m) (Fin d) ℚ} {b : Fin m → ℚ}
    (hI : InputOK d n m M A b) (σ : Strategy d) (cs : ℕ → Bool) {BU : ℝ} {D D' : ℕ → ℕ}
    (hc : CostOKO P (worldO A b (gw P ⟨σ, cs⟩ n m A b)) (s0U d n m A b) n BU)
    (hw : CoinWindowsOK P (worldO A b (gw P ⟨σ, cs⟩ n m A b)) (s0U d n m A b) n D D')
    {t N : ℕ} (ht : t < n) (hN : D t ≤ N ∨ D' t ≤ N) :
    ∀ i < t, playedBit (progP P) ⟨σ, cs⟩ (initBit d n m A b) i =
      playedBit (progP P) ⟨σ, trunc N cs⟩ (initBit d n m A b) i := by
  intro i hi
  set wO := worldO A b (gw P ⟨σ, cs⟩ n m A b) with hwO
  have hex : ∃ k, t ≤ (runO P wO (s0U d n m A b) k).rounds := by
    obtain ⟨k, hk⟩ := plays_all hc rfl (t - 1) (by omega)
    exact ⟨k, by omega⟩
  have hspec := Nat.find_spec hex
  obtain ⟨k, hk⟩ : ∃ k, Nat.find hex = k + 1 := by
    rcases h0 : Nat.find hex with _ | k
    · rw [h0] at hspec; simp [RunFacts.runO_zero, s0U, initU] at hspec; omega
    · exact ⟨k, rfl⟩
  rw [hk] at hspec
  have hlt : (runO P wO (s0U d n m A b) k).rounds < t := by
    have := Nat.find_min hex (show k < Nat.find hex by omega); omega
  obtain ⟨-, h2, -, -, h5⟩ := RunFacts.stepO_facts P wO (runO P wO (s0U d n m A b) k)
  rw [← RunFacts.runO_succ] at h2 h5
  have hr : (runO P wO (s0U d n m A b) (k + 1)).rounds = t := by omega
  have hc1 : (runO P wO (s0U d n m A b) (k + 1)).coins ≤ N := by
    rcases hN with hN | hN
    · rw [h5 (by omega)]; exact ((hw t ht k).2.2 hlt).trans hN
    · exact ((hw t ht (k + 1)).1 (by omega)).trans hN
  obtain ⟨g, hrel, -⟩ := sim P hI (gw P ⟨σ, cs⟩ n m A b)
  have e : runBit (progP P) ⟨σ, cs⟩ (initBit d n m A b) (g (k + 1)) =
      run (progP P) (gw P ⟨σ, cs⟩ n m A b) (initBit d n m A b) (g (k + 1)) :=
    Conj1BitSanity.runBit_eq_run _ _ _ _ _
  have hcoin : (runBit (progP P) ⟨σ, cs⟩ (initBit d n m A b) (g (k + 1))).coins ≤ N := by
    rw [e, (hrel _).coins]; exact hc1
  have e2 := runBit_cs_congr (progP P) σ (cs := cs) (cs' := trunc N cs) (initBit d n m A b) (g (k + 1))
    fun j hj => by simp [trunc, show j < N by omega]
  have hround : i < (runBit (progP P) ⟨σ, cs⟩ (initBit d n m A b) (g (k + 1))).rounds := by
    rw [e, (hrel _).rounds, hr]; exact hi
  rw [Bit.RegMeas.playedBit_eq_pts _ _ _ hround, Bit.RegMeas.playedBit_eq_pts _ _ _ (by rw [← e2]; exact hround), e2]

/-! ## Independence under the product law -/

/-- Under a product law, a σ-algebra of the second factor independent of another one there stays independent of it
joined with the whole first factor. -/
theorem indep_prod_snd {X Y : Type*} [mX : MeasurableSpace X] {m1 m2 : MeasurableSpace Y} [mY : MeasurableSpace Y]
    (ρ : Measure X) (ν : Measure Y) [IsProbabilityMeasure ρ] [IsProbabilityMeasure ν] (h1 : m1 ≤ mY)
    (h2 : m2 ≤ mY) (h : Indep m1 m2 ν) :
    Indep (MeasurableSpace.comap Prod.snd m1) (MeasurableSpace.comap Prod.fst mX ⊔ MeasurableSpace.comap Prod.snd m2)
      (ρ.prod ν) := by
  set p2 : Set (Set (X × Y)) :=
    {S | ∃ A B, MeasurableSet A ∧ MeasurableSet[m2] B ∧ S = Prod.fst ⁻¹' A ∩ Prod.snd ⁻¹' B} with hp2d
  have hp2 : IsPiSystem p2 := by
    rintro _ ⟨A, B, hA, hB, rfl⟩ _ ⟨A', B', hA', hB', rfl⟩ _
    exact ⟨A ∩ A', B ∩ B', hA.inter hA', MeasurableSet.inter (m := m2) hB hB', by ext; simp only [Set.mem_inter_iff, Set.mem_preimage]; tauto⟩
  have hgen : MeasurableSpace.comap Prod.fst mX ⊔ MeasurableSpace.comap Prod.snd m2 =
      MeasurableSpace.generateFrom p2 := by
    apply le_antisymm
    · refine sup_le ?_ ?_
      · rintro _ ⟨A, hA, rfl⟩
        exact MeasurableSpace.measurableSet_generateFrom ⟨A, Set.univ, hA, MeasurableSet.univ (m := m2), by simp⟩
      · rintro _ ⟨B, hB, rfl⟩
        exact MeasurableSpace.measurableSet_generateFrom ⟨Set.univ, B, MeasurableSet.univ, hB, by simp⟩
    · refine MeasurableSpace.generateFrom_le ?_
      rintro _ ⟨A, B, hA, hB, rfl⟩
      exact MeasurableSet.inter (m := MeasurableSpace.comap Prod.fst mX ⊔ MeasurableSpace.comap Prod.snd m2)
        (le_sup_left (a := MeasurableSpace.comap Prod.fst mX) _ ⟨A, hA, rfl⟩)
        (le_sup_right (b := MeasurableSpace.comap Prod.snd m2) _ ⟨B, hB, rfl⟩)
  have hle1 : MeasurableSpace.comap Prod.snd m1 ≤ (inferInstance : MeasurableSpace (X × Y)) :=
    (MeasurableSpace.comap_mono h1).trans (@measurable_snd X Y mX mY).comap_le
  have hle2 : MeasurableSpace.comap Prod.fst mX ⊔ MeasurableSpace.comap Prod.snd m2 ≤
      (inferInstance : MeasurableSpace (X × Y)) :=
    sup_le measurable_fst.comap_le ((MeasurableSpace.comap_mono h2).trans (@measurable_snd X Y mX mY).comap_le)
  refine IndepSets.indep hle1 hle2 (@MeasurableSpace.isPiSystem_measurableSet _ (MeasurableSpace.comap Prod.snd m1))
    hp2 (@MeasurableSpace.generateFrom_measurableSet _ (MeasurableSpace.comap Prod.snd m1)).symm hgen ?_
  rw [IndepSets_iff]
  rintro _ _ ⟨C, hC, rfl⟩ ⟨A, B, hA, hB, rfl⟩
  have hCB := (Indep_iff _ _ _).1 h C B hC hB
  have e1 : Prod.snd ⁻¹' C ∩ (Prod.fst ⁻¹' A ∩ Prod.snd ⁻¹' B) = A ×ˢ (C ∩ B) := by
    ext ⟨x, y⟩; simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_prod]; tauto
  have e2 : Prod.snd ⁻¹' C = (Set.univ : Set X) ×ˢ C := by ext ⟨x, y⟩; simp
  have e3 : Prod.fst ⁻¹' A ∩ Prod.snd ⁻¹' B = A ×ˢ B := by ext ⟨x, y⟩; simp
  rw [e1, e2, e3, Measure.prod_prod, Measure.prod_prod, Measure.prod_prod, measure_univ, hCB]
  ring

/-- A function that factors through `T` generates a σ-algebra inside that of `T`. -/
theorem comap_le_of_factor {Ω β : Type*} [mΩ : MeasurableSpace Ω] [mβ : MeasurableSpace β] {T : Ω → Ω} {f : Ω → β}
    (hf : Measurable f) (hT : ∀ ω, f (T ω) = f ω) : MeasurableSpace.comap f mβ ≤ MeasurableSpace.comap T mΩ := by
  have : f = f ∘ T := funext fun ω => (hT ω).symm
  rw [this, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono hf.comap_le

/-- The seed and the coins below `N`. -/
def cutN {Θ : Type} (N : ℕ) (ω : Θ × (ℕ → Bool)) : Θ × (ℕ → Bool) := (ω.1, trunc N ω.2)

/-- The coins from `N` on are independent of the seed and the coins below `N`. -/
theorem indep_cut {Θ : Type} [MeasurableSpace Θ] (ρ : Measure Θ) [IsProbabilityMeasure ρ] (N : ℕ) :
    Indep (coinsFrom (Prod.snd : Θ × (ℕ → Bool) → ℕ → Bool) N)
      (MeasurableSpace.comap (cutN N) inferInstance) (ρ.prod coinStream) := by
  have h0 := coordσ_indep (ι := ℕ) (S := Set.Ici N) (T := Set.Iio N)
    (Set.disjoint_left.2 fun j h1 h2 => absurd (Set.mem_Iio.1 h2) (not_lt.2 (Set.mem_Ici.1 h1)))
  have hP := indep_prod_snd ρ coinStream (coordσ_le _) (coordσ_le _) h0
  refine indep_of_indep_of_le (hP) ?_ ?_
  · refine iSup₂_le fun j hj => ?_
    have : (fun ω : Θ × (ℕ → Bool) => ω.2 j) = (fun cs : ℕ → Bool => cs j) ∘ Prod.snd := rfl
    rw [this, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono (le_coordσ (Set.mem_Ici.2 hj))
  · have htrunc : MeasurableSpace.comap (trunc N) (inferInstance : MeasurableSpace (ℕ → Bool)) ≤
        coordσ (Set.Iio N) := by
      rw [show (inferInstance : MeasurableSpace (ℕ → Bool)) =
        ⨆ j, MeasurableSpace.comap (fun cs : ℕ → Bool => cs j) inferInstance from rfl]
      rw [MeasurableSpace.comap_iSup]
      refine iSup_le fun j => ?_
      rw [MeasurableSpace.comap_comp]
      by_cases hj : j < N
      · have e : ((fun cs : ℕ → Bool => cs j) ∘ trunc N) = fun cs => cs j :=
          funext fun cs => by simp [trunc, hj]
        rw [e]; exact le_coordσ (Set.mem_Iio.2 hj)
      · have e : ((fun cs : ℕ → Bool => cs j) ∘ trunc N) = fun _ => false :=
          funext fun cs => by simp [trunc, hj]
        rw [e]
        rintro s ⟨t, -, rfl⟩
        by_cases h : false ∈ t
        · have : (fun _ : ℕ → Bool => false) ⁻¹' t = Set.univ := Set.eq_univ_of_forall fun _ => h
          rw [this]; exact MeasurableSet.univ
        · have : (fun _ : ℕ → Bool => false) ⁻¹' t = ∅ := Set.eq_empty_of_forall_notMem fun _ => h
          rw [this]; exact @MeasurableSet.empty _ (coordσ (Set.Iio N))
    rw [show (inferInstance : MeasurableSpace (Θ × (ℕ → Bool))) =
      MeasurableSpace.comap Prod.fst inferInstance ⊔ MeasurableSpace.comap Prod.snd inferInstance from rfl]
    rw [MeasurableSpace.comap_sup, MeasurableSpace.comap_comp, MeasurableSpace.comap_comp]
    refine sup_le_sup le_rfl ?_
    have e : (Prod.snd ∘ cutN (Θ := Θ) N) = trunc N ∘ Prod.snd := rfl
    rw [e, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono htrunc

/-! ## The environment -/

/-- The loss of round `t < n` at a point of `K` is measurable in the seed and the coins. -/
theorem lossE_meas (P : List InstrO) {n m : ℕ} {A : Matrix (Fin m) (Fin d) ℚ} {b : Fin m → ℚ} {Θ : Type}
    [MeasurableSpace Θ] (σ : Θ → Strategy d) (hσ : RandAdv (polytope A b) n σ)
    (hplay : ∀ θ cs, ∀ t < n, playedBit (progP P) ⟨σ θ, cs⟩ (initBit d n m A b) t ∈ polytope A b) :
    ∀ t < n, ∀ y ∈ polytope A b, Measurable fun ω => lossE P σ n m A b t ω y := by
  intro t ht y hy
  have hcs : ∀ j, Measurable fun ω : Θ × (ℕ → Bool) => (Bit.RegMeas.gameOf σ ω).cs j := fun j =>
    (measurable_pi_apply j).comp measurable_snd
  have hfb := Bit.RegMeas.fbMeas_of_randAdv (progP P) (polytope A b) σ hσ (initBit d n m A b) hplay
  have hX := Bit.RegMeas.tuple_fibers
    (X := fun (i : Fin t) (ω : Θ × (ℕ → Bool)) =>
      playedBit (progP P) (Bit.RegMeas.gameOf σ ω) (initBit d n m A b) i)
    (fun i => (Bit.RegMeas.playedBit_meas (progP P) (Bit.RegMeas.gameOf σ) (initBit d n m A b) n hcs hfb rfl
      (show (i : ℕ) < n by omega)).1)
    (fun i v => (Bit.RegMeas.playedBit_meas (progP P) (Bit.RegMeas.gameOf σ) (initBit d n m A b) n hcs hfb rfl
      (show (i : ℕ) < n by omega)).2 v)
  have key : (fun ω => lossE P σ n m A b t ω y) = fun ω =>
      (fun (Q : Fin t → E d) (ω : Θ × (ℕ → Bool)) => lossAd (σ ω.1) 0 (Bit.RegMeas.extQ Q) t y)
        ((fun ω (i : Fin t) => playedBit (progP P) (Bit.RegMeas.gameOf σ ω) (initBit d n m A b) i) ω) ω := by
    funext ω
    unfold lossE
    exact congrFun (Conj1BitSanity.lossAd_prefix (σ ω.1) 0
      (x := playedBit (progP P) ⟨σ ω.1, ω.2⟩ (initBit d n m A b))
      (y := Bit.RegMeas.extQ fun i : Fin t => playedBit (progP P) (Bit.RegMeas.gameOf σ ω) (initBit d n m A b) i) t
      fun i hi => by simp [Bit.RegMeas.extQ, hi, Bit.RegMeas.gameOf]) y
  rw [key]
  refine Bit.RegMeas.measurable_of_countable_fibers (Y := ℝ)
    (G := fun (Q : Fin t → E d) (ω : Θ × (ℕ → Bool)) => lossAd (σ ω.1) 0 (Bit.RegMeas.extQ Q) t y)
    hX.1 (fun q _ => hX.2 q) ?_
  rintro Q ⟨ω0, rfl⟩
  have e : ∀ θ, lossAd (σ θ) 0 (Bit.RegMeas.extQ fun i : Fin t =>
      playedBit (progP P) (Bit.RegMeas.gameOf σ ω0) (initBit d n m A b) i) t y =
      lossAd (σ θ) 0 (fun i => toE (Bit.Asm.ptsBit (progP P) (Bit.RegMeas.gameOf σ ω0) (initBit d n m A b) i)) t y := by
    intro θ
    exact congrFun (Conj1BitSanity.lossAd_prefix (σ θ) 0
      (x := Bit.RegMeas.extQ fun i : Fin t => playedBit (progP P) (Bit.RegMeas.gameOf σ ω0) (initBit d n m A b) i)
      (y := fun i => toE (Bit.Asm.ptsBit (progP P) (Bit.RegMeas.gameOf σ ω0) (initBit d n m A b) i)) t
      fun i hi => by simp [Bit.RegMeas.extQ, hi, Bit.Asm.playedBit_eq]) y
  simp only [e]
  exact ((hσ t ht _).2 y hy).comp measurable_fst

/-- **The environment** of a randomised adversary, for Theorem U: the seed and the coins, no noise. -/
theorem env_noisy (P : List InstrO) {n m M : ℕ} {A : Matrix (Fin m) (Fin d) ℚ} {b : Fin m → ℚ}
    (hI : InputOK d n m M A b) {Θ : Type} [MeasurableSpace Θ] (ρ : Measure Θ) [IsProbabilityMeasure ρ]
    (σ : Θ → Strategy d) (hσ : RandAdv (polytope A b) n σ) (D D' : ℕ → ℕ) {BU : ℝ}
    (hU : ∀ (f : ℕ → E d → ℝ) (cs : ℕ → Bool), (∀ t < n, AdmLoss (polytope A b) (f t)) →
      CostOKO P ⟨f, fun _ => 0, cs, orcK A b⟩ (s0U d n m A b) n BU ∧
        (∀ t < n, playedO P ⟨f, fun _ => 0, cs, orcK A b⟩ (s0U d n m A b) t ∈ polytope A b) ∧
        CoinWindowsOK P ⟨f, fun _ => 0, cs, orcK A b⟩ (s0U d n m A b) n D D') :
    NoisyAdv (polytope A b) n D D' (ρ.prod coinStream) Prod.snd (lossE P σ n m A b) (fun _ _ => 0) := by
  have hplay : ∀ θ cs, ∀ t < n, playedBit (progP P) ⟨σ θ, cs⟩ (initBit d n m A b) t ∈ polytope A b := by
    intro θ cs t ht
    obtain ⟨h1, h2, -⟩ := hU _ cs (adm_gw P hσ θ cs)
    rw [plays_eq P hI ⟨σ θ, cs⟩ h1 t ht]; exact h2 t ht
  have hmeas := lossE_meas P σ hσ hplay
  have hinv : ∀ t < n, ∀ N, (D t ≤ N ∨ D' t ≤ N) → ∀ s ≤ t, ∀ ω,
      lossE P σ n m A b s (cutN N ω) = lossE P σ n m A b s ω := by
    intro t ht N hN s hs ω
    obtain ⟨h1, -, h3⟩ := hU _ ω.2 (adm_gw P hσ ω.1 ω.2)
    unfold lossE cutN
    exact (Conj1BitSanity.lossAd_prefix _ 0 s fun i hi =>
      plays_trunc P hI (σ ω.1) ω.2 h1 h3 ht hN i (by omega)).symm
  have hhist : ∀ t < n, ∀ N, (D t ≤ N ∨ D' t ≤ N) → ∀ M',
      histσ (polytope A b) (lossE P σ n m A b) (fun _ _ => 0) Prod.snd (t + 1) M' N ≤
        MeasurableSpace.comap (cutN N) inferInstance := by
    intro t ht N hN M'
    refine sup_le (sup_le ?_ ?_) ?_
    · refine iSup₂_le fun s hs => iSup₂_le fun y hy => ?_
      exact comap_le_of_factor (hmeas s (by omega) y hy) fun ω => by rw [hinv t ht N hN s (by omega) ω]
    · exact iSup₂_le fun s _ => comap_le_of_factor measurable_const fun ω => rfl
    · refine iSup₂_le fun j hj => ?_
      exact comap_le_of_factor ((measurable_pi_apply j).comp measurable_snd) fun ω => by
        simp [cutN, trunc, hj]
  refine
    { prob := inferInstance
      coin_meas := measurable_snd
      coin_law := by rw [Measure.map_snd_prod, measure_univ, one_smul]
      adm := fun t ht ω => adm_gw P hσ ω.1 ω.2 t ht
      loss_meas := hmeas
      noise_meas := fun _ _ => measurable_const
      fresh_loss := fun t ht =>
        indep_of_indep_of_le_right (indep_cut ρ (D t)) (hhist t ht _ (Or.inl le_rfl) t)
      fresh_noise := fun t ht =>
        indep_of_indep_of_le_right (indep_cut ρ (D' t)) (hhist t ht _ (Or.inr le_rfl) (t + 1))
      noise_int := fun t _ => ?_
      noise_mean := fun t _ => ?_
      noise_exp := fun t _ => ?_ }
  · have e : (fun ω : Θ × (ℕ → Bool) => Real.exp ((fun _ _ => (0 : ℝ)) t ω ^ 2)) = fun _ => (1 : ℝ) := by
      funext ω; simp
    rw [e]; exact integrable_const _
  · have e : (fun _ : Θ × (ℕ → Bool) => (0 : ℝ)) = 0 := rfl
    show (ρ.prod coinStream)[(fun _ : Θ × (ℕ → Bool) => (0 : ℝ)) | _] =ᵐ[_] 0
    rw [e, condExp_zero]
  · have e : (fun ω : Θ × (ℕ → Bool) => Real.exp ((fun _ _ => (0 : ℝ)) t ω ^ 2)) = fun _ => (1 : ℝ) := by
      funext ω; simp
    rw [e]
    by_cases hle : histσ (polytope A b) (lossE P σ n m A b) (fun _ _ => 0) Prod.snd (t + 1) t (D' t) ≤
        (inferInstance : MeasurableSpace (Θ × (ℕ → Bool)))
    · rw [condExp_const hle]; exact Filter.Eventually.of_forall fun _ => by norm_num
    · rw [condExp_of_not_le hle]; exact Filter.Eventually.of_forall fun _ => by simp

end AdversarialBco.UniPoly
