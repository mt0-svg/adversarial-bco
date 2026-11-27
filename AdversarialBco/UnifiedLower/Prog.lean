/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.RunFacts
public import AdversarialBco.Unified.Sanity
public import AdversarialBco.Conj1Lower.Sanity
public import AdversarialBco.UnifiedLower.Sanity

@[expose] public section

/-!
# `TheoremLowerUProg` from `TheoremLowerU`: Lemmas BRIDGE and REAL

Lemma BRIDGE and Lemma REAL (the paper's section on programs), on the run facts M1, M2 of
Unified/RunFacts.lean. Fix a program `P` that meets `MachineOK` on an input of `TheoremUnified`'s class.

* BRIDGE (`progLearner`, `progLearner_isLearner`): on the coin space, the point of round `t` given the observations
  `o` of the earlier rounds is the point that `P` plays in round `t` in the world with the losses `0`, the noise `o`
  padded by `0` (`padWorld`), the coins and the oracle. That world is a world of `MachineOK` (the losses `0` are
  admissible and the noise is any real sequence), so the point is in `K`; it is jointly measurable in the coins and the
  observations by M2. So it is a learner of `TheoremLowerU`'s class.
* REAL (`clLoss`, `closedLoop_cl`, `noisyAdv_cl`, `regretU_cl`): for a strategy `σ` of `StratsLowU`, the losses of the
  noiseless game of `σ` against that learner, on each coin sequence, are in closed loop with `P` (`ClosedLoop`), since
  the run of `P` in the closed-loop world plays the points of that game (`playedO_closed`, by M1: the feedback at a state
  with `r` rounds played is the observation of round `r - 1`); with the noise `0` they form a noisy adversary of
  `TheoremUnified` with the windows `D`, `D'` of the program: the loss of round `s ≤ t` reads the coins below `D t`,
  resp. `D' t` only (M1 with the coin clause of `MachineOK`, `played_coin_dep`), so it is independent of the coins from
  `D t`, resp. `D' t`, on (on the product of fair coins, `coordσ_indep`); and `regretU` of `P` against them is the
  regret of the learner against `σ`, coin sequence by coin sequence.
* `progU_of_lowerU`: `TheoremLowerU → TheoremLowerUProg`.
-/

open MeasureTheory ProbabilityTheory

namespace AdversarialBco.UnifiedLower.Prog

open BitRAM BitRAMO Unified Unified.RunFacts Unified.UnifiedSanity
open RealRAM (Strategy Strats obsAd lossAd regretPts)
open Lower (Learner IsLearnerAd regretAd Policy transcript plays)
open Lower.Sanity (transcript_snd)

variable {d : ℕ}

/-! ## Lemma BRIDGE: the learner of a program -/

/-- The observations `o` of the rounds before `t`, padded by `0`. -/
def padO {t : ℕ} (o : Fin t → ℝ) : ℕ → ℝ := fun u => if h : u < t then o ⟨u, h⟩ else 0

/-- The world of the learner of a program: the losses `0`, the noise `o` padded by `0`, the coins `cs`, the oracle. -/
def padWorld (orc : (Fin d → ℚ) → ℕ → Bool) (cs : ℕ → Bool) {t : ℕ} (o : Fin t → ℝ) : WorldO d :=
  ⟨fun _ _ => 0, padO o, cs, orc⟩

/-- The learner of the program `P` (Lemma BRIDGE): on the coins `cs`, the point of round `t` after the observations `o`
is the point that `P` plays in round `t` in `padWorld orc cs o`. -/
noncomputable def progLearner (P : List InstrO) (s0 : State d) (orc : (Fin d → ℚ) → ℕ → Bool) :
    Learner (ℕ → Bool) d :=
  fun t cs _ o => playedO P (padWorld orc cs o) s0 t

/-- **Lemma BRIDGE.** A program that meets `MachineOK` on a convex `K` is a learner of `IsLearnerAd K n`. -/
theorem progLearner_isLearner {P : List InstrO} {K : Set (E d)} {orc : (Fin d → ℚ) → ℕ → Bool} {s0 : State d}
    {n : ℕ} {B : ℝ} {D D' : ℕ → ℕ} (hK : Convex ℝ K) (hM : MachineOK P K orc s0 n B D D') (hs0 : s0.rounds = 0) :
    IsLearnerAd K n (progLearner P s0 orc) := by
  intro t ht
  refine ⟨?_, fun cs x o => (hM (fun _ _ => 0) (padO o) cs fun _ _ => admLoss_zero hK).2.1 t ht⟩
  refine measurable_playedO (P := P) (s0 := s0) (n := n)
    (g := fun p : (ℕ → Bool) × (Fin t → E d) × (Fin t → ℝ) => padWorld orc p.1 p.2.2) orc (fun _ => rfl)
    (fun j => (measurable_pi_apply j).comp measurable_fst) ?_ hs0 ht
  intro k ω0 _
  simp only [fbO_eq, padWorld]
  split_ifs
  · exact measurable_const
  · refine measurable_const.add ?_
    unfold padO
    split_ifs
    · exact (measurable_pi_apply _).comp (measurable_snd.comp measurable_snd)
    · exact measurable_const

/-! ## Lemma REAL: the closed loop -/

section Real

variable (P : List InstrO) (s0 : State d) (orc : (Fin d → ℚ) → ℕ → Bool) (σ : Strategy d)

/-- The closed-loop losses: on the coins `cs`, the losses that `σ` chooses in the noiseless game against the learner of
`P`. -/
noncomputable def clLoss : ℕ → (ℕ → Bool) → E d → ℝ :=
  fun t cs => lossAd σ (fun _ => 0) (plays σ (fun _ => 0) (fun t => progLearner P s0 orc t cs)) t

/-- The closed-loop world on the coins `cs`. -/
noncomputable abbrev clWorld (cs : ℕ → Bool) : WorldO d := envWorld orc id (clLoss P s0 orc σ) (fun _ _ => 0) cs

/-- The observation of round `u < t` is the loss of round `u` at the point of round `u`, plus the noise. -/
theorem obsAd_apply (ε : ℕ → ℝ) (x : ℕ → E d) : ∀ (t u : ℕ) (hu : u < t),
    obsAd σ ε x t ⟨u, hu⟩ = lossAd σ ε x u (x u) + ε u
  | 0, u, hu => absurd hu (Nat.not_lt_zero u)
  | t + 1, u, hu => by
    rcases Nat.lt_succ_iff_lt_or_eq.1 hu with h | h
    · have := obsAd_apply ε x t u h
      simp only [obsAd]
      rw [show (⟨u, hu⟩ : Fin (t + 1)) = Fin.castSucc ⟨u, h⟩ from rfl, Fin.snoc_castSucc]
      exact this
    · subst h
      simp only [obsAd]
      rw [show (⟨u, hu⟩ : Fin (u + 1)) = Fin.last u from rfl, Fin.snoc_last]
      rfl

/-- **The identity of the runs.** In the closed-loop world, `P` plays the points of the noiseless game of `σ` against
its learner. -/
theorem playedO_closed (cs : ℕ → Bool) (s : ℕ) :
    playedO P (clWorld P s0 orc σ cs) s0 s = plays σ (fun _ => 0) (fun t => progLearner P s0 orc t cs) s := by
  induction s using Nat.strong_induction_on with
  | _ s ih =>
  set x := plays σ (fun _ => 0) (fun t => progLearner P s0 orc t cs) with hx
  have hpl : x s = playedO P (padWorld orc cs
      (transcript σ (fun _ => 0) (fun t => progLearner P s0 orc t cs) s).2) s0 s := rfl
  rw [hpl]
  refine playedO_congr_same P s0 s rfl rfl fun k hk => ?_
  rw [fbO_eq, fbO_eq]
  split_ifs with h0
  · rfl
  · have hr : (runO P (clWorld P s0 orc σ cs) s0 k).rounds - 1 < s := by omega
    have hpt : toE ((runO P (clWorld P s0 orc σ cs) s0 k).pts ((runO P (clWorld P s0 orc σ cs) s0 k).rounds - 1)) =
        x ((runO P (clWorld P s0 orc σ cs) s0 k).rounds - 1) := by
      rw [← playedO_eq_pts P _ s0 (by omega)]
      exact ih _ hr
    simp only [padWorld, padO, dite_eq_left hr, hpt, transcript_snd, obsAd_apply]
    simp [clLoss, envWorld, hx]

/-- The closed-loop losses of a strategy of `StratsLowU` are in closed loop with `P`. -/
theorem closedLoop_cl {K : Set (E d)} {n : ℕ} {r0 : ℝ} (hσ : σ ∈ StratsLowU K n r0) :
    ClosedLoop P s0 orc n σ (clLoss P s0 orc σ) := by
  intro t ht cs
  have hid : (fun s : Fin t => playedO P (envWorld orc id (clLoss P s0 orc σ) (fun _ _ => 0) cs) s0 s) =
      fun s : Fin t => plays σ (fun _ => 0) (fun t => progLearner P s0 orc t cs) s :=
    funext fun s => playedO_closed P s0 orc σ cs s
  rw [hid]
  exact (hσ.2 t ht _ _ (fun _ => 0)).1

theorem clLoss_eq {K : Set (E d)} {n : ℕ} {r0 : ℝ} (hσ : σ ∈ StratsLowU K n r0) {t : ℕ} (ht : t < n)
    (cs : ℕ → Bool) :
    clLoss P s0 orc σ t cs = σ t (fun i : Fin t => playedO P (clWorld P s0 orc σ cs) s0 i) (fun _ => 0) :=
  closedLoop_cl P s0 orc σ hσ t ht cs

/-- The regret of `P` in the closed-loop world is the regret of its learner against `σ`. -/
theorem regretU_cl (K : Set (E d)) (n : ℕ) (cs : ℕ → Bool) :
    regretU P K n s0 (envWorld orc id (clLoss P s0 orc σ) (fun _ _ => 0) cs) =
      regretAd K σ (fun t => progLearner P s0 orc t cs) n := by
  unfold regretU regretAd
  have h : playedO P (envWorld orc id (clLoss P s0 orc σ) (fun _ _ => 0) cs) s0 =
      plays σ (fun _ => 0) (fun t => progLearner P s0 orc t cs) := funext (playedO_closed P s0 orc σ cs)
  rw [h]
  rfl

variable {P s0 orc σ}

variable {K : Set (E d)} {n : ℕ} {r0 B : ℝ} {D D' : ℕ → ℕ}

theorem adm_cl (hσ : σ ∈ StratsLowU K n r0) {t : ℕ} (ht : t < n) (cs : ℕ → Bool) :
    AdmLoss K (clLoss P s0 orc σ t cs) :=
  (hσ.1 t ht).1 _ _

/-- The coin clause of `MachineOK` in the closed-loop world. -/
theorem cl_windows (hσ : σ ∈ StratsLowU K n r0) (hM : MachineOK P K orc s0 n B D D') {t : ℕ} (ht : t < n)
    (cs : ℕ → Bool) (k : ℕ) :
    ((runO P (clWorld P s0 orc σ cs) s0 k).rounds ≤ t → (runO P (clWorld P s0 orc σ cs) s0 k).coins ≤ D' t) ∧
      (t < (runO P (clWorld P s0 orc σ cs) s0 k).rounds → D' t ≤ (runO P (clWorld P s0 orc σ cs) s0 k).coins) ∧
      ((runO P (clWorld P s0 orc σ cs) s0 k).rounds < t → (runO P (clWorld P s0 orc σ cs) s0 k).coins ≤ D t) :=
  (hM (fun t => clLoss P s0 orc σ t cs) (fun _ => 0) cs fun _ hu => adm_cl hσ hu cs).2.2 t ht k

/-- M1 in the closed loop: the point of a round `v ≤ i < n` reads the coins below `N` only, when the states with at
most `i` rounds played read at most `N` coins. -/
theorem played_coin_dep (hσ : σ ∈ StratsLowU K n r0) {i N : ℕ} (hi : i < n)
    (hN : ∀ cs k, (runO P (clWorld P s0 orc σ cs) s0 k).rounds ≤ i → (runO P (clWorld P s0 orc σ cs) s0 k).coins ≤ N) :
    ∀ v ≤ i, ∀ cs cs' : ℕ → Bool, (∀ j < N, cs j = cs' j) →
      playedO P (clWorld P s0 orc σ cs) s0 v = playedO P (clWorld P s0 orc σ cs') s0 v := by
  intro v
  induction v using Nat.strong_induction_on with
  | _ v ih =>
  intro hv cs cs' hcs
  refine playedO_congr P s0 v N rfl (fun k hk => ?_) (fun k hk => hN cs k (hk.trans hv)) hcs
  rw [fbO_eq, fbO_eq]
  split_ifs with h0
  · rfl
  · have hr : (runO P (clWorld P s0 orc σ cs) s0 k).rounds - 1 < n := by omega
    show clLoss P s0 orc σ _ cs _ + 0 = clLoss P s0 orc σ _ cs' _ + 0
    rw [clLoss_eq P s0 orc σ hσ hr, clLoss_eq P s0 orc σ hσ hr]
    congr 3
    funext u
    exact ih u (by have := u.2; omega) (by have := u.2; omega) cs cs' hcs

/-- The closed-loop loss of a round `s ≤ t < n` reads the coins below `D t` only. -/
theorem loss_dep_D (hσ : σ ∈ StratsLowU K n r0) (hM : MachineOK P K orc s0 n B D D') {s t : ℕ} (hst : s ≤ t)
    (ht : t < n) (y : E d) (cs cs' : ℕ → Bool) (hcs : ∀ j < D t, cs j = cs' j) :
    clLoss P s0 orc σ s cs y = clLoss P s0 orc σ s cs' y := by
  rw [clLoss_eq P s0 orc σ hσ (by omega), clLoss_eq P s0 orc σ hσ (by omega)]
  congr 2
  funext u
  have hu : (u : ℕ) < t := by have := u.2; omega
  exact played_coin_dep hσ (i := u) (by omega)
    (fun cs k hk => (cl_windows hσ hM ht cs k).2.2 (by omega)) u le_rfl cs cs' hcs

/-- The closed-loop loss of a round `s ≤ t < n` reads the coins below `D' t` only. -/
theorem loss_dep_D' (hσ : σ ∈ StratsLowU K n r0) (hM : MachineOK P K orc s0 n B D D') {s t : ℕ} (hst : s ≤ t)
    (ht : t < n) (y : E d) (cs cs' : ℕ → Bool) (hcs : ∀ j < D' t, cs j = cs' j) :
    clLoss P s0 orc σ s cs y = clLoss P s0 orc σ s cs' y := by
  rw [clLoss_eq P s0 orc σ hσ (by omega), clLoss_eq P s0 orc σ hσ (by omega)]
  congr 2
  funext u
  have hu : (u : ℕ) < t := by have := u.2; omega
  exact played_coin_dep hσ (i := u) (by omega)
    (fun cs k hk => (cl_windows hσ hM ht cs k).1 (by omega)) u le_rfl cs cs' hcs

/-- A function of the coins below `N` is measurable for the coins below `N`. -/
theorem meas_coordσ_of_dep {β : Type*} [MeasurableSpace β] {N : ℕ} (f : (ℕ → Bool) → β)
    (hf : ∀ cs cs' : ℕ → Bool, (∀ j < N, cs j = cs' j) → f cs = f cs') : Measurable[coordσ (Set.Iio N)] f := by
  set r : (ℕ → Bool) → (Fin N → Bool) := fun cs j => cs j with hr_def
  set ext : (Fin N → Bool) → (ℕ → Bool) := fun v j => if h : j < N then v ⟨j, h⟩ else false with hext
  have hle : MeasurableSpace.comap r MeasurableSpace.pi ≤ coordσ (Set.Iio N) := by
    rw [MeasurableSpace.comap_le_iff_le_map]
    refine iSup_le fun j => ?_
    rw [← MeasurableSpace.comap_le_iff_le_map, MeasurableSpace.comap_comp]
    exact le_coordσ (Set.mem_Iio.2 j.2)
  have hr : Measurable[coordσ (Set.Iio N)] r := Measurable.of_comap_le hle
  have hg : Measurable (f ∘ ext) := measurable_of_countable _
  have hfe : f = (f ∘ ext) ∘ r := funext fun cs => hf _ _ fun j hj => by simp [hext, hr_def, hj]
  rw [hfe]
  exact hg.comp hr

/-- The σ-algebra of the closed-loop history before a window `N` is that of the coins below `N`, when the losses of
the rounds up to `t` read the coins below `N` only. -/
theorem hist_le (L M N t : ℕ) (hL : L ≤ t + 1)
    (hdep : ∀ s ≤ t, ∀ y : E d, ∀ cs cs' : ℕ → Bool, (∀ j < N, cs j = cs' j) →
      clLoss P s0 orc σ s cs y = clLoss P s0 orc σ s cs' y) :
    histσ K (clLoss P s0 orc σ) (fun _ _ => 0) id L M N ≤ coordσ (Set.Iio N) := by
  refine sup_le (sup_le ?_ ?_) ?_
  · refine iSup₂_le fun s hs => iSup₂_le fun y _ => ?_
    exact (meas_coordσ_of_dep (fun cs => clLoss P s0 orc σ s cs y)
      (fun cs cs' h => hdep s (by omega) y cs cs' h)).comap_le
  · exact iSup₂_le fun _ _ => by simp
  · exact iSup₂_le fun j hj => le_coordσ hj

/-- **Lemma REAL.** The closed-loop losses with the noise `0` form a noisy adversary of `TheoremUnified` with the
windows `D`, `D'` of the program, on the program's coin space. -/
theorem noisyAdv_cl (hσ : σ ∈ StratsLowU K n r0) (hM : MachineOK P K orc s0 n B D D') :
    NoisyAdv K n D D' coinStream id (clLoss P s0 orc σ) (fun _ _ => 0) := by
  classical
  have hfrom : ∀ N, coinsFrom (id : (ℕ → Bool) → ℕ → Bool) N ≤ coordσ (Set.Ici N) :=
    fun N => iSup₂_le fun j hj => le_coordσ hj
  have hind : ∀ L M N, histσ K (clLoss P s0 orc σ) (fun _ _ => 0) id L M N ≤ coordσ (Set.Iio N) →
      Indep (coinsFrom (id : (ℕ → Bool) → ℕ → Bool) N) (histσ K (clLoss P s0 orc σ) (fun _ _ => 0) id L M N)
        coinStream := by
    intro L M N hle
    have h0 := coordσ_indep (ι := ℕ) (S := Set.Ici N) (T := Set.Iio N)
      (Set.disjoint_left.2 fun j h1 h2 => absurd (Set.mem_Iio.1 h2) (not_lt.2 (Set.mem_Ici.1 h1)))
    exact indep_of_indep_of_le_right (indep_of_indep_of_le_left h0 (hfrom N)) hle
  have hD : ∀ t < n, ∀ M, histσ K (clLoss P s0 orc σ) (fun _ _ => 0) id (t + 1) M (D t) ≤ coordσ (Set.Iio (D t)) :=
    fun t ht M => hist_le (t + 1) M (D t) t le_rfl fun s hs y cs cs' h => loss_dep_D hσ hM hs ht y cs cs' h
  have hD' : ∀ t < n, ∀ M, histσ K (clLoss P s0 orc σ) (fun _ _ => 0) id (t + 1) M (D' t) ≤
      coordσ (Set.Iio (D' t)) :=
    fun t ht M => hist_le (t + 1) M (D' t) t le_rfl fun s hs y cs cs' h => loss_dep_D' hσ hM hs ht y cs cs' h
  refine
    { prob := inferInstance
      coin_meas := measurable_id
      coin_law := Measure.map_id
      adm := fun t ht cs => adm_cl hσ ht cs
      loss_meas := fun t ht y _ => ?_
      noise_meas := fun _ _ => measurable_const
      fresh_loss := fun t ht => hind _ _ _ (hD t ht t)
      fresh_noise := fun t ht => hind _ _ _ (hD' t ht (t + 1))
      noise_int := fun _ _ => integrable_const _
      noise_mean := fun t _ => ?_
      noise_exp := fun t ht => ?_ }
  · exact (meas_coordσ_of_dep (fun cs => clLoss P s0 orc σ t cs y)
      (fun cs cs' h => loss_dep_D hσ hM le_rfl ht y cs cs' h)).mono (coordσ_le _) le_rfl
  · have : (fun _ : ℕ → Bool => (0 : ℝ)) = 0 := rfl
    rw [this, condExp_zero]
  · have hle := (hD' t ht t).trans (coordσ_le (Set.Iio (D' t)))
    have : (fun ω : ℕ → Bool => Real.exp ((fun _ _ => (0 : ℝ)) t ω ^ 2)) = fun _ => (1 : ℝ) := by
      funext ω; simp
    rw [this, condExp_const hle]
    exact Filter.Eventually.of_forall fun _ => by norm_num

end Real

/-! ## `TheoremLowerUProg` -/

open LowerSanity in
/-- `TheoremLowerUProg` from `TheoremLowerU`: the learner of the program (Lemma BRIDGE) meets, for each clause, a
strategy of `StratsLowU`; its closed loop with the program (Lemma REAL) is the environment, and the regrets agree. -/
theorem progU_of_lowerU (hL : TheoremLowerU) : TheoremLowerUProg := by
  intro P d hd n hn δ r0 R0 hδ0 hδ1 hr0 hr0R a K hKc hKv hK1 hK2 orc _ B D D' hM
  have hs0 : (initU d n δ r0 R0 a).rounds = 0 := rfl
  have hb := bodyU_of_unified hr0 hr0R a hKc hKv hK1 hK2
  have hpol := progLearner_isLearner hKv hM hs0
  obtain ⟨hab, hcm, hcp⟩ := hL d hd n hn (toE a) r0 R0 K hb (ℕ → Bool) _ coinStream inferInstance
    (progLearner P (initU d n δ r0 R0 a) orc) hpol
  have mean : ∀ c, LowerMean K n r0 coinStream (progLearner P (initU d n δ r0 R0 a) orc) c →
      ProgMean P K orc (initU d n δ r0 R0 a) n r0 D D' c := by
    rintro c ⟨σ, hσ, hint, hge⟩
    refine ⟨σ, clLoss P (initU d n δ r0 R0 a) orc σ, hσ, closedLoop_cl _ _ _ _ hσ, noisyAdv_cl hσ hM, ?_, ?_⟩
    · simpa only [regretU_cl] using hint
    · simpa only [regretU_cl] using hge
  have prob : ∀ c p, LowerProb K n r0 coinStream (progLearner P (initU d n δ r0 R0 a) orc) c p →
      ProgProb P K orc (initU d n δ r0 R0 a) n r0 D D' c p := by
    rintro c p ⟨σ, hσ, hm, hge⟩
    refine ⟨σ, clLoss P (initU d n δ r0 R0 a) orc σ, hσ, closedLoop_cl _ _ _ _ hσ, noisyAdv_cl hσ hM, ?_, ?_⟩
    · simpa only [regretU_cl] using hm
    · simpa only [regretU_cl] using hge
  exact ⟨fun h1 h2 => ⟨mean _ (hab h1 h2).1, prob _ _ (hab h1 h2).2⟩, mean _ hcm, prob _ _ hcp⟩

end AdversarialBco.UnifiedLower.Prog
