/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.WorldGMap
public import AdversarialBco.Unified.WorldCore
public import AdversarialBco.StatementUnified

@[expose] public section

/-!
# The extension of an environment of `TheoremUnified`

A noisy adversary `(Ω, μ, coin, loss, noise)` of `TheoremUnified` with the windows `winL`, `winN` of the schedule with
`P0` prologue blocks of `2 B` coins (`SchedOK`) extends to an abstract coupled world on `Ω × (ℕ → ℝ)` under
`μ ⊗ gaussStream`: the stream is `gmap` (WorldGMap.lean) at the coins of `ω` and the fresh terms, the noise is the
environment's below the horizon and `0` past it, and the filtration before round `t` is the environment's history
before round `t` (the losses of the rounds `≤ t`, the noises of the rounds `< t`, the coins before round `t`,
truncated at the horizon) joined with the fresh terms of `idxC d t`.

* `extW`, `extF`: the world and its filtration;
* `worldLawOK_extW`: the clauses `WorldLawOK`; (W1) of the draw from `fresh_loss`, (W1) of the coupling coordinates
  from `fresh_noise`, (W2) from `noise_mean`, `noise_exp`, each through the product with the fresh terms
  (`indep_prod`, `condExp_fst_eq_zero`, `condExp_fst_le` of WorldGen.lean);
* `extOK`, `ExtOK`: what the assembly reads of the extension: the law clauses, the measure, the digits of the stream
  are the coins, the noise, and the adaptedness of the losses and the coins;
* `exists_extOK`: the same from `SchedOK` and a noisy adversary with the windows `D`, `D'`;
* `lossProcE`: the losses of the environment as a loss process of the extension;
* `prob_ext`, `shadow_env`: the transfer of the regret event of the environment to the extension, and the glue that
  moves the bound of `ShadowPropW` back to `μ`.
-/

open MeasureTheory ProbabilityTheory

namespace AdversarialBco.Unified.World

open AdversarialBco.RealRAM AdversarialBco.Poly AdversarialBco.BitRAM AdversarialBco.Bit AdversarialBco.Bit.Cpl
  AdversarialBco.Bit.Sched
open AdversarialBco.Bit.Cpl.MaxCoup (phiI measurable_phiI)

variable {d : ℕ}

/-! ## Measurability on a σ-algebra that is not the instance -/

theorem meas_pi_iff {α ι : Type*} {π : ι → Type*} [∀ i, MeasurableSpace (π i)] (m : MeasurableSpace α)
    {g : α → ∀ i, π i} : Measurable[m] g ↔ ∀ i, Measurable[m] fun x => g x i := by
  let _ := m
  exact measurable_pi_iff

theorem meas_fst_of {X Y Z : Type*} [MeasurableSpace Z] {mA : MeasurableSpace X} {mB : MeasurableSpace (X × Y)}
    (hle : MeasurableSpace.comap Prod.fst mA ≤ mB) {f : X → Z} (hf : Measurable[mA] f) :
    Measurable[mB] fun p : X × Y => f p.1 :=
  hf.comp (Measurable.of_comap_le hle)

/-! ## The roles of the blocks in their round -/

/-- The role in its round of slot `s` of the round block `k` (`pairOf`). -/
def roleOf (d k : ℕ) (s : Fin 2) : ℕ :=
  if k % nBlk d + 1 = nBlk d then d + 1 + s else 2 * (k % nBlk d) + s

theorem nBlk_pos (d : ℕ) : 0 < nBlk d := by unfold nBlk; omega

theorem pairIdx_inl (k : ℕ) (s : Fin 2) : pairIdx d (.inl k, s) = 4 * k + 1 + 2 * (s : ℕ) := by
  fin_cases s <;> simp [pairIdx, pairOf]

theorem pairIdx_inr (k : ℕ) (s : Fin 2) : pairIdx d (.inr k, s) = cIdx d (k / nBlk d) (roleOf d k s) := by
  fin_cases s <;> by_cases hk : k % nBlk d + 1 = nBlk d <;> simp [pairIdx, pairOf, roleOf, hk]

theorem roleOf_le (k : ℕ) (s : Fin 2) : roleOf d k s ≤ d + 2 := by
  have hs := s.2
  have hq := Nat.mod_lt k (nBlk_pos d)
  unfold roleOf
  generalize k % nBlk d = q at *
  unfold nBlk at *
  split_ifs <;> omega

theorem roleOf_le_draw {k : ℕ} (hk : k % nBlk d + 1 ≠ nBlk d) (s : Fin 2) : roleOf d k s ≤ d := by
  have hs := s.2
  have hq := Nat.mod_lt k (nBlk_pos d)
  unfold roleOf
  generalize k % nBlk d = q at *
  unfold nBlk at *
  split_ifs <;> omega

theorem roleOf_dither {k : ℕ} (hk : k % nBlk d + 1 = nBlk d) (s : Fin 2) : roleOf d k s = d + 1 + s := by
  simp [roleOf, hk]

theorem inr_decomp (k : ℕ) : k = k / nBlk d * nBlk d + k % nBlk d := by
  have := Nat.div_add_mod k (nBlk d)
  rw [Nat.mul_comm] at this
  exact this.symm

theorem cIdx_even (t c : ℕ) : cIdx d t c % 2 = 0 := by unfold cIdx; omega

theorem cIdx_inj {t t' c c' : ℕ} (hc : c < d + 5) (hc' : c' < d + 5) (h : cIdx d t c = cIdx d t' c') :
    t = t' ∧ c = c' := by
  unfold cIdx at h
  have h' : c + (d + 5) * t = c' + (d + 5) * t' := by
    rw [Nat.mul_comm (d + 5) t, Nat.mul_comm (d + 5) t']; omega
  have hp : 0 < d + 5 := by omega
  have e1 := congrArg (· / (d + 5)) h'
  have e2 := congrArg (· % (d + 5)) h'
  simp only [Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt hc, Nat.div_eq_of_lt hc', Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt hc, Nat.mod_eq_of_lt hc', zero_add] at e1 e2
  exact ⟨e1, e2⟩

theorem cIdx_mem_idxC {t t' c : ℕ} (hc : c < d + 5) : cIdx d t c ∈ idxC d t' ↔ t < t' := by
  simp only [idxC, Set.mem_union, Set.mem_ofPred_eq]
  have he := cIdx_even (d := d) t c
  unfold cIdx at he ⊢
  constructor
  · rintro (h | h)
    · omega
    · by_contra hn
      have := Nat.mul_le_mul_right (d + 5) (not_lt.mp hn)
      omega
  · intro h
    right
    have := Nat.mul_le_mul_right (d + 5) (Nat.succ_le_of_lt h)
    rw [Nat.succ_mul] at this
    omega

theorem pairIdx_inl_ne_cIdx (k : ℕ) (s : Fin 2) (t c : ℕ) : pairIdx d (.inl k, s) ≠ cIdx d t c := by
  rw [pairIdx_inl]
  have := cIdx_even (d := d) t c
  omega

theorem pairIdx_inl_mem (k : ℕ) (s : Fin 2) (t : ℕ) : pairIdx d (.inl k, s) ∈ idxC d t := by
  rw [pairIdx_inl]
  left
  show (4 * k + 1 + 2 * (s : ℕ)) % 2 = 1
  omega

theorem pairIdx_inr_eq {k : ℕ} {s : Fin 2} {t c : ℕ} (hc : c < d + 5) (h : pairIdx d (.inr k, s) = cIdx d t c) :
    k / nBlk d = t ∧ roleOf d k s = c := by
  rw [pairIdx_inr] at h
  exact cIdx_inj (by have := roleOf_le (d := d) k s; omega) hc h

/-- The terms of the draw group of round `t` (roles `≤ d`). -/
def gSet (d t : ℕ) : Set ℕ := {i | ∃ c ≤ d, i = cIdx d t c}

/-- The terms of the coupling coordinates of round `t` (roles `d + 1`, `d + 3`, `d + 4`). -/
def zSet (d t : ℕ) : Set ℕ := {cIdx d t (d + 1), cIdx d t (d + 3), cIdx d t (d + 4)}

theorem disjoint_zSet (t : ℕ) : Disjoint (zSet d t) (idxC d t ∪ gSet d t) := by
  rw [Set.disjoint_left]
  rintro i hz (hi | ⟨c, hc, rfl⟩)
  · simp only [zSet, Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl <;> exact lt_irrefl t ((cIdx_mem_idxC (by omega)).mp hi)
  · simp only [zSet, Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with h' | h' | h' <;> (have := (cIdx_inj (by omega) (by omega) h').2; omega)

/-! ## The coins of the blocks against the windows -/

section Coins

variable {P0 B : ℕ}

theorem cj_inl_lt {k s' : ℕ} (hk : k < P0) (hs : s' < 2 * B) (t q : ℕ) :
    cj P0 B (.inl k) s' < blkStart d (2 * B * P0) B t q := by
  show 2 * B * k + s' < 2 * B * P0 + 2 * B * (t * nBlk d + q)
  have : 2 * B * (k + 1) ≤ 2 * B * P0 := Nat.mul_le_mul_left _ hk
  rw [mul_add_one] at this
  omega

theorem cj_inr_lt {k s' t q : ℕ} (hk : k < t * nBlk d + q) (hs : s' < 2 * B) :
    cj P0 B (.inr k) s' < blkStart d (2 * B * P0) B t q := by
  show 2 * B * P0 + 2 * B * k + s' < 2 * B * P0 + 2 * B * (t * nBlk d + q)
  have : 2 * B * (k + 1) ≤ 2 * B * (t * nBlk d + q) := Nat.mul_le_mul_left _ hk
  rw [mul_add_one] at this
  omega

theorem cj_inr_ge {k s' t q : ℕ} (hk : t * nBlk d + q ≤ k) : blkStart d (2 * B * P0) B t q ≤ cj P0 B (.inr k) s' := by
  show 2 * B * P0 + 2 * B * (t * nBlk d + q) ≤ 2 * B * P0 + 2 * B * k + s'
  have : 2 * B * (t * nBlk d + q) ≤ 2 * B * k := Nat.mul_le_mul_left _ hk
  omega

theorem coined_inr {n k : ℕ} (h : coined d n P0 (.inr k)) : k / nBlk d < n :=
  (Nat.div_lt_iff_lt_mul (nBlk_pos d)).mpr h

end Coins

theorem winL_mono {K0 B s t : ℕ} (h : s ≤ t) : winL d K0 B s ≤ winL d K0 B t := by
  unfold winL blkStart
  gcongr

theorem winL_le_winN (K0 B t : ℕ) : winL d K0 B t ≤ winN d K0 B t := by
  unfold winL winN blkStart
  gcongr
  omega

/-! ## The history of an environment -/

section Hist

variable {Ω : Type} {K : Set (E d)} {loss : ℕ → Ω → E d → ℝ} {noise : ℕ → Ω → ℝ}
  {coin : Ω → ℕ → Bool}

theorem histσ_mono {L M N L' M' N' : ℕ} (hL : L ≤ L') (hM : M ≤ M') (hN : N ≤ N') :
    histσ K loss noise coin L M N ≤ histσ K loss noise coin L' M' N' := by
  refine sup_le_sup (sup_le_sup ?_ ?_) ?_
  · exact iSup₂_le fun s hs => le_iSup₂_of_le (f := fun s (_ : s < L') => lossσ K loss s) s (by omega) le_rfl
  · exact iSup₂_le fun s hs => le_iSup₂_of_le (f := fun s (_ : s < M') => noiseσ noise s) s (by omega) le_rfl
  · exact iSup₂_le fun j hj => le_iSup₂_of_le
      (f := fun j (_ : j < N') => MeasurableSpace.comap (fun ω => coin ω j) inferInstance) j (by omega) le_rfl

theorem meas_hist_loss {L M N s : ℕ} (hs : s < L) {y : E d} (hy : y ∈ K) :
    Measurable[histσ K loss noise coin L M N] fun ω => loss s ω y :=
  Measurable.of_comap_le (le_sup_of_le_left (le_sup_of_le_left
    (le_iSup₂_of_le (f := fun s (_ : s < L) => lossσ K loss s) s hs
      (le_iSup₂_of_le (f := fun y (_ : y ∈ K) => MeasurableSpace.comap (fun ω => loss s ω y) inferInstance) y hy
        le_rfl))))

theorem meas_hist_noise {L M N s : ℕ} (hs : s < M) : Measurable[histσ K loss noise coin L M N] (noise s) :=
  Measurable.of_comap_le (le_sup_of_le_left (le_sup_of_le_right
    (le_iSup₂_of_le (f := fun s (_ : s < M) => noiseσ noise s) s hs le_rfl)))

theorem meas_hist_coin {L M N j : ℕ} (hj : j < N) : Measurable[histσ K loss noise coin L M N] fun ω => coin ω j :=
  Measurable.of_comap_le (le_sup_of_le_right
    (le_iSup₂_of_le (f := fun j (_ : j < N) => MeasurableSpace.comap (fun ω => coin ω j) inferInstance) j hj le_rfl))

theorem meas_from_coin {N j : ℕ} (hj : N ≤ j) : Measurable[coinsFrom coin N] fun ω => coin ω j :=
  Measurable.of_comap_le
    (le_iSup₂_of_le (f := fun j (_ : N ≤ j) => MeasurableSpace.comap (fun ω => coin ω j) inferInstance) j hj le_rfl)

theorem histσ_le' [mΩ : MeasurableSpace Ω] {n : ℕ} {D D' : ℕ → ℕ} {μ : Measure Ω} (h : Unified.NoisyAdv K n D D' μ coin loss noise)
    {L M : ℕ} (hL : L ≤ n) (hM : M ≤ n) (N : ℕ) : histσ K loss noise coin L M N ≤ mΩ := by
  have hc : ∀ j, Measurable fun ω => coin ω j := fun j => (measurable_pi_apply j).comp h.coin_meas
  refine sup_le (sup_le ?_ ?_) ?_
  · exact iSup₂_le fun s hs => iSup₂_le fun y hy => (h.loss_meas s (by omega) y hy).comap_le
  · exact iSup₂_le fun s hs => (h.noise_meas s (by omega)).comap_le
  · exact iSup₂_le fun j _ => (hc j).comap_le

theorem coinsFrom_le [mΩ : MeasurableSpace Ω] {n : ℕ} {D D' : ℕ → ℕ} {μ : Measure Ω} (h : Unified.NoisyAdv K n D D' μ coin loss noise)
    (N : ℕ) : coinsFrom coin N ≤ mΩ :=
  iSup₂_le fun j _ => ((measurable_pi_apply j).comp h.coin_meas).comap_le

end Hist

/-! ## Generic facts on a coupled world -/

theorem CWorld.xi_le_xg {Ω : Type} [MeasurableSpace Ω] (W : CWorld d Ω) (t : ℕ) :
    MeasurableSpace.comap (W.xi t) inferInstance ≤ MeasurableSpace.comap (W.xg t) inferInstance := by
  have : W.xi t = (fun g : Fin (d + 1) → ℝ => fun c : Fin d => g c.castSucc) ∘ W.xg t := rfl
  rw [this, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono (Measurable.comap_le (by fun_prop))

theorem CWorld.measurable_xi {Ω : Type} [MeasurableSpace Ω] (W : CWorld d Ω) (hw : Measurable W.w) (t : ℕ) :
    Measurable (W.xi t) :=
  measurable_pi_iff.mpr fun c => by
    show Measurable fun x => (W.w x).1 (cIdx d t c)
    exact (measurable_pi_apply _).comp (measurable_fst.comp hw)

/-! ## The extension -/

section Ext

variable {Ω : Type} {mC mB : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} {K : Set (E d)} {n : ℕ}
  {coin : Ω → ℕ → Bool} {loss : ℕ → Ω → E d → ℝ} {noise : ℕ → Ω → ℝ}

/-- The environment's part of the filtration of the extension before round `t`: the losses of the rounds `≤ t`, the
noises of the rounds `< t` and the coins before round `t`, truncated at the horizon. -/
abbrev envH (K : Set (E d)) (n K0 B : ℕ) (coin : Ω → ℕ → Bool) (loss : ℕ → Ω → E d → ℝ) (noise : ℕ → Ω → ℝ)
    (t : ℕ) : MeasurableSpace Ω :=
  histσ K loss noise coin (min (t + 1) n) (min t n) (winL d K0 B (min t n))

omit mΩ in
theorem envH_lt {K0 B t : ℕ} (ht : t < n) :
    envH K n K0 B coin loss noise t = histσ K loss noise coin (t + 1) t (winL d K0 B t) := by
  simp only [envH, min_eq_left (by omega : t + 1 ≤ n), min_eq_left ht.le]

/-- The noise of the extension: the environment's below the horizon, `0` past it. -/
noncomputable def nzE (n : ℕ) (noise : ℕ → Ω → ℝ) (ω : Ω) : ℕ → ℝ := fun t => if t < n then noise t ω else 0

variable (P0 B : ℕ) (h : Unified.NoisyAdv K n (winL d (2 * B * P0) B) (winN d (2 * B * P0) B) μ coin loss noise)

/-- The filtration of the extension: the environment's history before round `t` and the fresh terms of
`idxC d t`. -/
noncomputable def extF : Filtration ℕ (inferInstance : MeasurableSpace (Ω × (ℕ → ℝ))) where
  seq t := MeasurableSpace.comap Prod.fst (envH K n (2 * B * P0) B coin loss noise t) ⊔
    MeasurableSpace.comap Prod.snd (coordσ (Z := ℝ) (idxC d t))
  mono' s t hst := sup_le_sup
    (MeasurableSpace.comap_mono (histσ_mono (min_le_min_right n (by omega)) (min_le_min_right n hst)
      (winL_mono (min_le_min_right n hst))))
    (MeasurableSpace.comap_mono (coordσ_mono (idxC_mono d hst)))
  le' t := sup_le
    ((MeasurableSpace.comap_mono (histσ_le' h (min_le_right _ _) (min_le_right _ _) _)).trans measurable_fst.comap_le)
    ((MeasurableSpace.comap_mono (coordσ_le _)).trans measurable_snd.comap_le)

/-- The coupled world of a noisy adversary with the windows of the schedule with `P0` prologue blocks of `2 B`
coins. -/
noncomputable def extW : CWorld d (Ω × (ℕ → ℝ)) :=
  ⟨μ.prod gaussStream, fun p => (gmap d n P0 B (coin p.1) p.2, nzE n noise p.1), extF P0 B h⟩

theorem extW_nz (t : ℕ) (p : Ω × (ℕ → ℝ)) : (extW P0 B h).nz t p = if t < n then noise t p.1 else 0 := rfl

theorem extW_prob : IsProbabilityMeasure (extW P0 B h).μ := by
  have := h.prob
  show IsProbabilityMeasure (μ.prod gaussStream)
  infer_instance

theorem extF_fst (t : ℕ) :
    MeasurableSpace.comap Prod.fst (envH K n (2 * B * P0) B coin loss noise t) ≤ (extW P0 B h).𝓕 t :=
  le_sup_left

/-! ### The terms of the stream -/

omit mΩ in
/-- A term of the stream is measurable for the coins of `mC` and the fresh terms of `S` when, should it lie under a
coined block, the coins of the block are in `mC` and its seed in `S`. -/
theorem meas_gmap_coord (S : Set ℕ) {i : ℕ} (hiS : i ∈ S)
    (hpair : ∀ (a : ℕ ⊕ ℕ) (s : Fin 2), pairIdx d (a, s) = i → coined d n P0 a →
      pairIdx d (a, 0) ∈ S ∧ ∀ s' < 2 * B, Measurable[mC] fun ω => coin ω (cj P0 B a s')) :
    @Measurable (Ω × (ℕ → ℝ)) ℝ
      (MeasurableSpace.comap Prod.fst mC ⊔ MeasurableSpace.comap Prod.snd (coordσ (Z := ℝ) S)) _
      fun p => gmap d n P0 B (coin p.1) p.2 i := by
  have hfst : @Measurable (Ω × (ℕ → ℝ)) Ω
      (MeasurableSpace.comap Prod.fst mC ⊔ MeasurableSpace.comap Prod.snd (coordσ (Z := ℝ) S)) mC Prod.fst :=
    Measurable.of_comap_le le_sup_left
  have hsnd : @Measurable (Ω × (ℕ → ℝ)) (ℕ → ℝ)
      (MeasurableSpace.comap Prod.fst mC ⊔ MeasurableSpace.comap Prod.snd (coordσ (Z := ℝ) S)) (coordσ S)
      Prod.snd :=
    Measurable.of_comap_le le_sup_right
  by_cases hex : ∃ a s, pairIdx d (a, s) = i ∧ coined d n P0 a
  · obtain ⟨a, s, rfl, hco⟩ := hex
    obtain ⟨hS0, hcm⟩ := hpair a s rfl hco
    have he : (fun p : Ω × (ℕ → ℝ) => gmap d n P0 B (coin p.1) p.2 (pairIdx d (a, s))) =
        fun p => fillB B (cbk P0 B (coin p.1) a) (phiI (p.2 (pairIdx d (a, 0)))) s :=
      funext fun p => gmap_pair hco s _ _
    rw [he]
    have hcb : @Measurable (Ω × (ℕ → ℝ)) (Fin (2 * B) → Bool)
        (MeasurableSpace.comap Prod.fst mC ⊔ MeasurableSpace.comap Prod.snd (coordσ (Z := ℝ) S)) _
        fun p => cbk P0 B (coin p.1) a :=
      (meas_pi_iff _).mpr fun s' => (hcm s' s'.2).comp hfst
    have hv : @Measurable (Ω × (ℕ → ℝ)) ℝ
        (MeasurableSpace.comap Prod.fst mC ⊔ MeasurableSpace.comap Prod.snd (coordσ (Z := ℝ) S)) _
        fun p => p.2 (pairIdx d (a, 0)) :=
      (measurable_coordσ hS0).comp hsnd
    exact (measurable_pi_apply s).comp ((measurable_fillB B).comp (hcb.prodMk (measurable_phiI.comp hv)))
  · push Not at hex
    have he : (fun p : Ω × (ℕ → ℝ) => gmap d n P0 B (coin p.1) p.2 i) = fun p => p.2 i :=
      funext fun p => gmap_v (fun a s h' => hex a s h') _ _
    rw [he]
    exact (measurable_coordσ hiS).comp hsnd

theorem extW_g_adapt (t : ℕ) (i : ℕ) (hi : i ∈ idxC d t) :
    Measurable[(extW P0 B h).𝓕 t] fun p => (extW P0 B h).gs p i := by
  refine meas_gmap_coord P0 B (mC := envH K n (2 * B * P0) B coin loss noise t) (idxC d t) hi ?_
  intro a s hai hco
  subst hai
  cases a with
  | inl k => exact ⟨pairIdx_inl_mem k 0 t, fun s' hs' => meas_hist_coin (cj_inl_lt hco hs' _ _)⟩
  | inr k =>
    rw [pairIdx_inr] at hi
    have hkt : k / nBlk d < t := (cIdx_mem_idxC (by have := roleOf_le (d := d) k s; omega)).mp hi
    refine ⟨?_, fun s' hs' => meas_hist_coin (cj_inr_lt ?_ hs')⟩
    · rw [pairIdx_inr]
      exact (cIdx_mem_idxC (by have := roleOf_le (d := d) k 0; omega)).mpr hkt
    · have h1 : k < t * nBlk d := (Nat.div_lt_iff_lt_mul (nBlk_pos d)).mp hkt
      have h2 : k < n * nBlk d := hco
      rcases le_total t n with h' | h'
      · rw [min_eq_left h']; omega
      · rw [min_eq_right h']; omega

theorem extW_e_adapt (t s : ℕ) (hst : s < t) : Measurable[(extW P0 B h).𝓕 t] ((extW P0 B h).nz s) := by
  by_cases hs : s < n
  · have hnz : (extW P0 B h).nz s = fun p => noise s p.1 := funext fun p => by simp [extW_nz, hs]
    rw [hnz]
    exact meas_fst_of (extF_fst P0 B h t) (meas_hist_noise (by omega))
  · have hnz : (extW P0 B h).nz s = fun _ => 0 := funext fun p => by simp [extW_nz, hs]
    rw [hnz]
    exact measurable_const

theorem extW_w_meas : Measurable (extW P0 B h).w := by
  show Measurable fun p : Ω × (ℕ → ℝ) => (gmap d n P0 B (coin p.1) p.2, nzE n noise p.1)
  refine Measurable.prodMk ?_ ?_
  · exact (measurable_gmap (d := d) (n := n) (P0 := P0) (B := B)).comp (h.coin_meas.prodMap measurable_id)
  · refine measurable_pi_iff.mpr fun t => ?_
    by_cases ht : t < n
    · simp only [nzE, ht, ↓reduceIte]
      exact (h.noise_meas t ht).comp measurable_fst
    · simp only [nzE, ht, ↓reduceIte]
      exact measurable_const

theorem extW_g_law : (extW P0 B h).μ.map (extW P0 B h).gs = gaussStream := by
  have := h.prob
  have hf : (extW P0 B h).gs = (fun q : (ℕ → Bool) × (ℕ → ℝ) => gmap d n P0 B q.1 q.2) ∘ Prod.map coin id := rfl
  rw [hf, ← Measure.map_map measurable_gmap (h.coin_meas.prodMap measurable_id)]
  show ((μ.prod gaussStream).map (Prod.map coin id)).map _ = _
  rw [← Measure.map_prod_map _ _ h.coin_meas measurable_id, h.coin_law, Measure.map_id, gmap_law]

/-! ### (W1) of the draw -/

theorem extW_xi_le (t : ℕ)
    (hC : t < n → ∀ j, winL d (2 * B * P0) B t ≤ j → Measurable[mC] fun ω => coin ω j) :
    MeasurableSpace.comap ((extW P0 B h).xi t) inferInstance ≤
      MeasurableSpace.comap Prod.fst mC ⊔ MeasurableSpace.comap Prod.snd (coordσ (Z := ℝ) (idxC d t)ᶜ) := by
  refine Measurable.comap_le ((meas_pi_iff _).mpr fun c => ?_)
  have hc : (c : ℕ) < d + 5 := by omega
  show @Measurable (Ω × (ℕ → ℝ)) ℝ
    (MeasurableSpace.comap Prod.fst mC ⊔ MeasurableSpace.comap Prod.snd (coordσ (Z := ℝ) (idxC d t)ᶜ)) _
    fun p => gmap d n P0 B (coin p.1) p.2 (cIdx d t c)
  refine meas_gmap_coord P0 B (mC := mC) _ (fun hm => lt_irrefl t ((cIdx_mem_idxC hc).mp hm)) ?_
  intro a s hai hco
  cases a with
  | inl k => exact absurd hai (pairIdx_inl_ne_cIdx k s t c)
  | inr k =>
    obtain ⟨hkt, -⟩ := pairIdx_inr_eq hc hai
    have htn : t < n := by rw [← hkt]; exact coined_inr hco
    refine ⟨?_, fun s' _ => hC htn _ (cj_inr_ge ?_)⟩
    · rw [pairIdx_inr, hkt]
      exact fun hm => lt_irrefl t ((cIdx_mem_idxC (by have := roleOf_le (d := d) k 0; omega)).mp hm)
    · have := Nat.div_mul_le_self k (nBlk d)
      rw [hkt] at this
      omega

theorem extW_xi_indep (t : ℕ) :
    Indep (MeasurableSpace.comap ((extW P0 B h).xi t) inferInstance) ((extW P0 B h).𝓕 t) (extW P0 B h).μ := by
  have := h.prob
  have hD : coordσ (Z := ℝ) (idxC d t) ≤ (inferInstance : MeasurableSpace (ℕ → ℝ)) := coordσ_le _
  have hC : coordσ (Z := ℝ) (idxC d t)ᶜ ≤ (inferInstance : MeasurableSpace (ℕ → ℝ)) := coordσ_le _
  have h2 : Indep (coordσ (Z := ℝ) (idxC d t)ᶜ) (coordσ (Z := ℝ) (idxC d t)) gaussStream :=
    coordσ_indep (gaussianReal 0 1) disjoint_compl_left
  have hB : envH K n (2 * B * P0) B coin loss noise t ≤ mΩ :=
    histσ_le' h (min_le_right _ _) (min_le_right _ _) _
  by_cases ht : t < n
  · have h1 : Indep (coinsFrom coin (winL d (2 * B * P0) B t)) (envH K n (2 * B * P0) B coin loss noise t) μ := by
      rw [envH_lt ht]
      exact h.fresh_loss t ht
    exact indep_of_indep_of_le_left (indep_prod μ gaussStream (coinsFrom_le h _) hB hC hD h1 h2)
      (extW_xi_le P0 B h t fun _ j hj => meas_from_coin hj)
  · exact indep_of_indep_of_le_left (indep_prod μ gaussStream bot_le hB hC hD (indep_bot_left _) h2)
      (extW_xi_le P0 B h t (mC := ⊥) fun h' => absurd h' ht)

/-! ### (W1) of the coupling coordinates -/

theorem extW_zz_le (t : ℕ)
    (hC : t < n → ∀ j, winN d (2 * B * P0) B t ≤ j → Measurable[mC] fun ω => coin ω j) :
    MeasurableSpace.comap ((extW P0 B h).zz t) inferInstance ≤
      MeasurableSpace.comap Prod.fst mC ⊔ MeasurableSpace.comap Prod.snd (coordσ (Z := ℝ) (zSet d t)) := by
  have key : ∀ c, (c = d + 1 ∨ c = d + 3 ∨ c = d + 4) →
      @Measurable (Ω × (ℕ → ℝ)) ℝ
        (MeasurableSpace.comap Prod.fst mC ⊔ MeasurableSpace.comap Prod.snd (coordσ (Z := ℝ) (zSet d t))) _
        fun p => gmap d n P0 B (coin p.1) p.2 (cIdx d t c) := by
    intro c hc
    have hc5 : c < d + 5 := by omega
    refine meas_gmap_coord P0 B (mC := mC) _ (by rcases hc with rfl | rfl | rfl <;> simp [zSet]) ?_
    intro a s hai hco
    cases a with
    | inl k => exact absurd hai (pairIdx_inl_ne_cIdx k s t c)
    | inr k =>
      obtain ⟨hkt, hr⟩ := pairIdx_inr_eq hc5 hai
      have htn : t < n := by rw [← hkt]; exact coined_inr hco
      have hdk : k % nBlk d + 1 = nBlk d := by
        by_contra hdk
        have := roleOf_le_draw hdk s
        omega
      refine ⟨?_, fun s' _ => hC htn _ (cj_inr_ge ?_)⟩
      · rw [pairIdx_inr, hkt, roleOf_dither hdk]
        simp [zSet]
      · have := inr_decomp (d := d) k
        rw [hkt] at this
        show t * nBlk d + (nBlk d - 1) ≤ k
        omega
  refine Measurable.comap_le ((meas_pi_iff _).mpr fun k => ?_)
  fin_cases k
  · exact key (d + 1) (Or.inl rfl)
  · exact key (d + 3) (Or.inr (Or.inl rfl))
  · exact key (d + 4) (Or.inr (Or.inr rfl))

theorem extW_xg_le (t : ℕ)
    (hC : t < n → ∀ j < winN d (2 * B * P0) B t, Measurable[mC] fun ω => coin ω j) :
    MeasurableSpace.comap ((extW P0 B h).xg t) inferInstance ≤
      MeasurableSpace.comap Prod.fst mC ⊔ MeasurableSpace.comap Prod.snd (coordσ (Z := ℝ) (gSet d t)) := by
  refine Measurable.comap_le ((meas_pi_iff _).mpr fun c => ?_)
  have hc : (c : ℕ) < d + 5 := by omega
  have hcd : (c : ℕ) ≤ d := by omega
  show @Measurable (Ω × (ℕ → ℝ)) ℝ
    (MeasurableSpace.comap Prod.fst mC ⊔ MeasurableSpace.comap Prod.snd (coordσ (Z := ℝ) (gSet d t))) _
    fun p => gmap d n P0 B (coin p.1) p.2 (cIdx d t c)
  refine meas_gmap_coord P0 B (mC := mC) _ ⟨c, hcd, rfl⟩ ?_
  intro a s hai hco
  cases a with
  | inl k => exact absurd hai (pairIdx_inl_ne_cIdx k s t c)
  | inr k =>
    obtain ⟨hkt, hr⟩ := pairIdx_inr_eq hc hai
    have htn : t < n := by rw [← hkt]; exact coined_inr hco
    have hdk : k % nBlk d + 1 ≠ nBlk d := fun hdk => by rw [roleOf_dither hdk] at hr; omega
    refine ⟨⟨roleOf d k 0, roleOf_le_draw hdk 0, by rw [pairIdx_inr, hkt]⟩,
      fun s' hs' => hC htn _ (cj_inr_lt ?_ hs')⟩
    have := inr_decomp (d := d) k
    have hq := Nat.mod_lt k (nBlk_pos d)
    rw [hkt] at this
    omega

theorem extW_Fσ_le (t : ℕ) (h𝓕 : envH K n (2 * B * P0) B coin loss noise t ≤ mB)
    (hC : t < n → ∀ j < winN d (2 * B * P0) B t, Measurable[mB] fun ω => coin ω j)
    (hN : t < n → Measurable[mB] (noise t)) :
    (extW P0 B h).Fσ t ≤
      MeasurableSpace.comap Prod.fst mB ⊔ MeasurableSpace.comap Prod.snd (coordσ (Z := ℝ) (idxC d t ∪ gSet d t)) := by
  refine sup_le (sup_le ?_ ?_) ?_
  · exact sup_le_sup (MeasurableSpace.comap_mono h𝓕) (MeasurableSpace.comap_mono (coordσ_mono Set.subset_union_left))
  · exact (extW_xg_le P0 B h t hC).trans
      (sup_le_sup le_rfl (MeasurableSpace.comap_mono (coordσ_mono Set.subset_union_right)))
  · refine Measurable.comap_le ?_
    show @Measurable (Ω × (ℕ → ℝ)) ℝ
      (MeasurableSpace.comap Prod.fst mB ⊔ MeasurableSpace.comap Prod.snd (coordσ (Z := ℝ) (idxC d t ∪ gSet d t))) _
      fun p => if t < n then noise t p.1 else 0
    by_cases htn : t < n
    · simp only [htn, ↓reduceIte]
      exact meas_fst_of le_sup_left (hN htn)
    · simp only [htn, ↓reduceIte]
      exact measurable_const

theorem extW_z_indep (t : ℕ) :
    Indep (MeasurableSpace.comap ((extW P0 B h).zz t) inferInstance) ((extW P0 B h).Fσ t) (extW P0 B h).μ := by
  have := h.prob
  have hC : coordσ (Z := ℝ) (zSet d t) ≤ (inferInstance : MeasurableSpace (ℕ → ℝ)) := coordσ_le _
  have hD : coordσ (Z := ℝ) (idxC d t ∪ gSet d t) ≤ (inferInstance : MeasurableSpace (ℕ → ℝ)) := coordσ_le _
  have h2 : Indep (coordσ (Z := ℝ) (zSet d t)) (coordσ (Z := ℝ) (idxC d t ∪ gSet d t)) gaussStream :=
    coordσ_indep (gaussianReal 0 1) (disjoint_zSet t)
  by_cases ht : t < n
  · have hB := histσ_le' h (L := t + 1) (M := t + 1) (by omega) (by omega) (winN d (2 * B * P0) B t)
    have hI := indep_prod μ gaussStream (coinsFrom_le h _) hB hC hD (h.fresh_noise t ht) h2
    refine indep_of_indep_of_le_right
      (indep_of_indep_of_le_left hI (extW_zz_le P0 B h t fun _ j hj => meas_from_coin hj)) ?_
    refine extW_Fσ_le P0 B h t ?_ (fun _ j hj => meas_hist_coin hj) (fun _ => meas_hist_noise (by omega))
    rw [envH_lt ht]
    exact histσ_mono le_rfl (by omega) (winL_le_winN _ _ _)
  · have hI := indep_prod μ gaussStream bot_le le_rfl hC hD (indep_bot_left mΩ) h2
    refine indep_of_indep_of_le_right
      (indep_of_indep_of_le_left hI (extW_zz_le P0 B h t (mC := ⊥) fun h' => absurd h' ht)) ?_
    exact extW_Fσ_le P0 B h t (mB := mΩ) (histσ_le' h (min_le_right _ _) (min_le_right _ _) _) (fun h' => absurd h' ht)
      (fun h' => absurd h' ht)

/-! ### (W2) -/

theorem integrable_of_exp_sq {X : Type} [MeasurableSpace X] {ν : Measure X} {f : X → ℝ} (hf : Measurable f)
    (hi : Integrable (fun x => Real.exp (f x ^ 2)) ν) : Integrable f ν := by
  refine hi.mono' hf.aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs]
  have h1 : |f x| ≤ f x ^ 2 + 1 := by nlinarith [abs_nonneg (f x), sq_abs (f x), sq_nonneg (|f x| - 1)]
  have h2 := Real.add_one_le_exp (f x ^ 2)
  linarith

theorem extW_HC_le (t : ℕ) (ht : t < n) :
    (extW P0 B h).HC t ≤ MeasurableSpace.comap Prod.fst (histσ K loss noise coin (t + 1) t (winN d (2 * B * P0) B t)) ⊔
      MeasurableSpace.comap Prod.snd (inferInstance : MeasurableSpace (ℕ → ℝ)) := by
  refine sup_le ?_ ?_
  · refine sup_le_sup (MeasurableSpace.comap_mono ?_) (MeasurableSpace.comap_mono (coordσ_le _))
    rw [envH_lt ht]
    exact histσ_mono le_rfl le_rfl (winL_le_winN _ _ _)
  · refine (CWorld.xi_le_xg _ t).trans ((extW_xg_le P0 B h t
    (mC := histσ K loss noise coin (t + 1) t (winN d (2 * B * P0) B t)) fun _ j hj => meas_hist_coin hj).trans ?_)
    exact sup_le_sup le_rfl (MeasurableSpace.comap_mono (coordσ_le _))

theorem extW_HC_le_top (t : ℕ) : (extW P0 B h).HC t ≤ (inferInstance : MeasurableSpace (Ω × (ℕ → ℝ))) :=
  sup_le ((extW P0 B h).𝓕.le t) ((CWorld.measurable_xi _ (extW_w_meas P0 B h) t).comap_le)

theorem extW_e_int (t : ℕ) : Integrable (fun p => Real.exp ((extW P0 B h).nz t p ^ 2)) (extW P0 B h).μ := by
  have := h.prob
  have := extW_prob P0 B h
  by_cases ht : t < n
  · have hnz : (fun p => Real.exp ((extW P0 B h).nz t p ^ 2)) = fun p => Real.exp (noise t p.1 ^ 2) :=
      funext fun p => by simp [extW_nz, ht]
    rw [hnz]
    exact (h.noise_int t ht).comp_fst gaussStream
  · have hnz : (fun p => Real.exp ((extW P0 B h).nz t p ^ 2)) = fun _ => (1 : ℝ) :=
      funext fun p => by simp [extW_nz, ht]
    rw [hnz]
    exact integrable_const _

theorem extW_e_mean (t : ℕ) :
    (extW P0 B h).μ[(extW P0 B h).nz t | (extW P0 B h).HC t] =ᵐ[(extW P0 B h).μ] 0 := by
  have := h.prob
  by_cases ht : t < n
  · have hnz : (extW P0 B h).nz t = fun p => noise t p.1 := funext fun p => by simp [extW_nz, ht]
    rw [hnz]
    exact condExp_fst_eq_zero _ μ gaussStream (histσ_le' h (by omega) (by omega) _) _ (extW_HC_le P0 B h t ht)
      (noise t) (integrable_of_exp_sq (h.noise_meas t ht) (h.noise_int t ht)) (h.noise_mean t ht)
  · have hnz : (extW P0 B h).nz t = 0 := funext fun p => by simp [extW_nz, ht]
    rw [hnz, condExp_zero]

theorem extW_e_exp (t : ℕ) :
    (extW P0 B h).μ[fun p => Real.exp ((extW P0 B h).nz t p ^ 2) | (extW P0 B h).HC t] ≤ᵐ[(extW P0 B h).μ]
      fun _ => 2 := by
  have := h.prob
  by_cases ht : t < n
  · have hnz : (fun p => Real.exp ((extW P0 B h).nz t p ^ 2)) = fun p => Real.exp (noise t p.1 ^ 2) :=
      funext fun p => by simp [extW_nz, ht]
    rw [hnz]
    exact condExp_fst_le _ μ gaussStream (histσ_le' h (by omega) (by omega) _) _ (extW_HC_le P0 B h t ht)
      (fun ω => Real.exp (noise t ω ^ 2)) (h.noise_int t ht) 2 (h.noise_exp t ht)
  · have hnz : (fun p => Real.exp ((extW P0 B h).nz t p ^ 2)) = fun _ => (1 : ℝ) :=
      funext fun p => by simp [extW_nz, ht]
    have := extW_prob P0 B h
    rw [hnz, condExp_const (extW_HC_le_top P0 B h t)]
    exact Filter.Eventually.of_forall fun _ => by norm_num

/-- The extension of a noisy adversary with the windows of the route is a coupled world. -/
theorem worldLawOK_extW : WorldLawOK (extW P0 B h) where
  prob := extW_prob P0 B h
  w_meas := extW_w_meas P0 B h
  g_adapt := extW_g_adapt P0 B h
  e_adapt := extW_e_adapt P0 B h
  g_law := extW_g_law P0 B h
  xi_indep := extW_xi_indep P0 B h
  z_indep := extW_z_indep P0 B h
  e_int := extW_e_int P0 B h
  e_mean := extW_e_mean P0 B h
  e_exp := extW_e_exp P0 B h

/-! ### The losses and the coins on the extension -/

theorem extW_loss_adapt (t : ℕ) (ht : t < n) (s : ℕ) (hs : s ≤ t) (y : E d) (hy : y ∈ K) :
    Measurable[(extW P0 B h).𝓕 t] fun p => loss s p.1 y :=
  meas_fst_of (f := fun ω => loss s ω y) (extF_fst P0 B h t) (meas_hist_loss (by omega) hy)

theorem extW_coin_adapt (t : ℕ) (ht : t ≤ n) (j : ℕ) (hj : j < blkStart d (2 * B * P0) B t 0) :
    Measurable[(extW P0 B h).𝓕 t] fun p => coin p.1 j := by
  refine meas_fst_of (f := fun ω => coin ω j) (extF_fst P0 B h t) (meas_hist_coin ?_)
  show j < winL d (2 * B * P0) B (min t n)
  rw [min_eq_left ht]
  exact hj

theorem extW_coin_play (hB : 0 < B) (t : ℕ) (ht : t < n) (j : ℕ)
    (hj : j < blkStart d (2 * B * P0) B t (nBlk d - 1)) :
    Measurable[(extW P0 B h).Fσ t] fun p => coin p.1 j := by
  by_cases hjL : j < blkStart d (2 * B * P0) B t 0
  · exact (extW_coin_adapt P0 B h t ht.le j hjL).mono (le_sup_left.trans le_sup_left) le_rfl
  push Not at hjL
  have hB2 : 0 < 2 * B := by omega
  have hinner : t * nBlk d + (nBlk d - 1) ≤ n * nBlk d + 0 := by
    have := Nat.mul_le_mul_right (nBlk d) (show t + 1 ≤ n by omega)
    rw [add_mul, one_mul] at this
    omega
  have hjn : j < blkStart d (2 * B * P0) B n 0 := by
    unfold blkStart at hj ⊢
    have := Nat.mul_le_mul_left (2 * B) hinner
    omega
  have he : (fun p : Ω × (ℕ → ℝ) => coin p.1 j) =
      fun p => Sched.beta d (2 * B * P0) B ((extW P0 B h).gs p) j :=
    funext fun p => (beta_gmap hB (coin p.1) p.2 hjn).symm
  rw [he]
  unfold blkStart at hj hjL
  rw [add_zero] at hjL
  have hK : ¬ j < 2 * B * P0 := by omega
  have hk1 : t * nBlk d ≤ (j - 2 * B * P0) / (2 * B) := by
    rw [Nat.le_div_iff_mul_le hB2]
    have := Nat.mul_comm (t * nBlk d) (2 * B)
    omega
  have hk2 : (j - 2 * B * P0) / (2 * B) < t * nBlk d + (nBlk d - 1) := by
    rw [Nat.div_lt_iff_lt_mul hB2]
    have := Nat.mul_comm (t * nBlk d + (nBlk d - 1)) (2 * B)
    omega
  generalize hk : (j - 2 * B * P0) / (2 * B) = k at hk1 hk2
  have hblk : blkOf (2 * B * P0) B j = .inr k := by simp only [blkOf, hK, ↓reduceIte, hk]
  have hkt : k / nBlk d = t := by
    refine Nat.div_eq_of_lt_le hk1 ?_
    rw [add_mul, one_mul]
    omega
  have hdk : k % nBlk d + 1 ≠ nBlk d := by
    have := inr_decomp (d := d) k
    rw [hkt] at this
    omega
  have hxg : Measurable[(extW P0 B h).Fσ t] ((extW P0 B h).xg t) :=
    Measurable.of_comap_le (le_sup_of_le_left le_sup_right)
  have hm : ∀ r, r ≤ d → Measurable[(extW P0 B h).Fσ t] fun p => (extW P0 B h).gs p (cIdx d t r) := by
    intro r hr
    have := (measurable_pi_apply (⟨r, by omega⟩ : Fin (d + 1))).comp hxg
    exact this
  unfold Sched.beta
  rw [hblk, ← pairIdx_zero, ← pairIdx_one, pairIdx_inr, pairIdx_inr, hkt]
  exact (measurable_blkCoin B _).comp ((hm _ (roleOf_le_draw hdk 0)).prodMk (hm _ (roleOf_le_draw hdk 1)))

end Ext

/-! ## What the assembly reads of the extension -/

/-- What the assembly reads of the extension of an environment: the law clauses, the measure, the digits of the
stream are the coins, the noise, and the adaptedness of the losses and of the coins. -/
structure ExtOK {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (K : Set (E d)) (n P0 B : ℕ) (coin : Ω → ℕ → Bool)
    (loss : ℕ → Ω → E d → ℝ) (noise : ℕ → Ω → ℝ) (W : CWorld d (Ω × (ℕ → ℝ))) : Prop where
  /-- (W1), (W2) and the law of the stream. -/
  law : WorldLawOK W
  /-- The measure is `μ ⊗ gaussStream`: an event of the environment keeps its probability. -/
  meas_eq : W.μ = μ.prod gaussStream
  /-- The digits of the stream are the environment's coins, for every coin read before round `n`, everywhere. -/
  beta : ∀ p, ∀ j < blkStart d (2 * B * P0) B n 0, Sched.beta d (2 * B * P0) B (W.gs p) j = coin p.1 j
  /-- The noise of the world is the environment's below the horizon. -/
  noise : ∀ t < n, ∀ p, W.nz t p = noise t p.1
  /-- The losses of the rounds `≤ t` are known before round `t`. -/
  loss_adapt : ∀ t < n, ∀ s ≤ t, ∀ y ∈ K, Measurable[W.𝓕 t] fun p => loss s p.1 y
  /-- The coins before round `t` are known before round `t`. -/
  coin_adapt : ∀ t ≤ n, ∀ j < blkStart d (2 * B * P0) B t 0, Measurable[W.𝓕 t] fun p => coin p.1 j
  /-- The coins read at the play of round `t` are known at `F*_t`. -/
  coin_play : ∀ t < n, ∀ j < blkStart d (2 * B * P0) B t (nBlk d - 1), Measurable[W.Fσ t] fun p => coin p.1 j

section Assembly

variable {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} {K : Set (E d)} {n : ℕ} {coin : Ω → ℕ → Bool}
  {loss : ℕ → Ω → E d → ℝ} {noise : ℕ → Ω → ℝ}

/-- The extension of every noisy adversary with the windows of the route meets `ExtOK`. -/
theorem extOK (P0 B : ℕ) (hB : 0 < B)
    (h : Unified.NoisyAdv K n (winL d (2 * B * P0) B) (winN d (2 * B * P0) B) μ coin loss noise) :
    ExtOK μ K n P0 B coin loss noise (extW P0 B h) where
  law := worldLawOK_extW P0 B h
  meas_eq := rfl
  beta := fun p _ hj => beta_gmap hB (coin p.1) p.2 hj
  noise := fun t ht p => by simp [extW_nz, ht]
  loss_adapt := extW_loss_adapt P0 B h
  coin_adapt := extW_coin_adapt P0 B h
  coin_play := extW_coin_play P0 B h hB

/-- The same from the schedule of the route (`SchedOK`): every noisy adversary with its windows has an extension. -/
theorem exists_extOK {K0 B : ℕ} {D D' : ℕ → ℕ} (hS : SchedOK d K0 B D D')
    (h : Unified.NoisyAdv K n D D' μ coin loss noise) :
    ∃ P0, K0 = 2 * B * P0 ∧ ∃ W : CWorld d (Ω × (ℕ → ℝ)), ExtOK μ K n P0 B coin loss noise W := by
  obtain ⟨hB, ⟨P0, rfl⟩, rfl, rfl⟩ := hS
  exact ⟨P0, rfl, extW P0 B h, extOK P0 B hB h⟩

/-- The admissible losses on `K`, with the σ-algebra of their values at the points of `K`. -/
def AdmL (K : Set (E d)) : Type := {f : E d → ℝ // AdmLoss K f}

instance instMeasAdmL (K : Set (E d)) : MeasurableSpace (AdmL K) :=
  MeasurableSpace.comap (fun f : AdmL K => fun y : K => f.1 y) inferInstance

theorem admLoss_zero {K : Set (E d)} (hK : Convex ℝ K) : AdmLoss K (0 : E d → ℝ) :=
  ⟨convexOn_const 0 hK, fun _ _ => ⟨le_rfl, zero_le_one⟩⟩

/-- The losses of a noisy adversary as a loss process of a world that meets `ExtOK`. -/
noncomputable def lossProcE {P0 B : ℕ} {W : CWorld d (Ω × (ℕ → ℝ))}
    (hA : Unified.NoisyAdv K n (winL d (2 * B * P0) B) (winN d (2 * B * P0) B) μ coin loss noise)
    (hE : ExtOK μ K n P0 B coin loss noise W) (hK : Convex ℝ K) : LossProcW d n K W.𝓕 where
  Λ := AdmL K
  L := fun _ l => l.1
  lam := fun t p => if ht : t < n then ⟨loss t p.1, hA.adm t ht p.1⟩ else ⟨0, admLoss_zero hK⟩
  adm := fun _ _ l => l.2
  meas := fun _ _ y hy => by
    have : Measurable fun f : AdmL K => fun y : K => f.1 y := Measurable.of_comap_le le_rfl
    exact (measurable_pi_apply (⟨y, interior_subset hy⟩ : K)).comp this
  lam_meas := fun t ht => by
    rw [measurable_iff_comap_le]
    show MeasurableSpace.comap _ (MeasurableSpace.comap (fun f : AdmL K => fun y : K => f.1 y) inferInstance) ≤ _
    rw [MeasurableSpace.comap_comp]
    refine Measurable.comap_le ((meas_pi_iff _).mpr fun y => ?_)
    simp only [Function.comp, ht, ↓reduceDIte]
    exact hE.loss_adapt t ht t le_rfl y.1 y.2

/-- The transfer of an event of the environment to the extension (the product with the fresh terms). -/
theorem prob_ext (μ : Measure Ω) (A : Set Ω) : (μ.prod gaussStream) {p : Ω × (ℕ → ℝ) | p.1 ∈ A} = μ A := by
  have : {p : Ω × (ℕ → ℝ) | p.1 ∈ A} = A ×ˢ Set.univ := by ext p; simp
  rw [this, Measure.prod_prod, measure_univ, mul_one]

/-- The regret of the environment, as `TheoremUnified` reads it. -/
noncomputable def regEnv (P : List BitRAMO.InstrO) (K : Set (E d)) (n : ℕ) (s0 : BitRAM.State d)
    (orc : (Fin d → ℚ) → ℕ → Bool) (coin : Ω → ℕ → Bool) (loss : ℕ → Ω → E d → ℝ) (noise : ℕ → Ω → ℝ)
    (ω : Ω) : ℝ :=
  Unified.regretU P K n s0 (Unified.envWorld orc coin loss noise ω)

/-- The glue of the assembly: a run record on a world that meets `ExtOK`, whose losses are the environment's and whose
plays are those of the program on the environment, moves SHADOW's bound to the environment's probability space. -/
theorem shadow_env (hS : ShadowPropW) {δ : ℝ} {P0 B : ℕ} {W : CWorld d (Ω × (ℕ → ℝ))}
    (hE : ExtOK μ K n P0 B coin loss noise W) (R : RunW d n K W) (P : List BitRAMO.InstrO) (s0 : BitRAM.State d)
    (orc : (Fin d → ℚ) → ℕ → Bool) (hloss : ∀ p, ∀ t < n, R.loss p t = loss t p.1)
    (hplay : ∀ p, ∀ t < n, R.play t p = BitRAMO.playedO P (Unified.envWorld orc coin loss noise p.1) s0 t)
    (δpos δbits κ0 κ1 : ℝ) (hreg : Regime d n δ) (hKc : IsClosed K) (hKv : Convex ℝ K) (hpos : PosHypW R δ δpos)
    (hC : CoupLaw R.Coup) (hTV : CoupTV R.Coup) (hM : BLMeasW R) (hb : BitsHypW R δbits)
    (hEng : EngineHypW R δ κ0 κ1) (h0 : 0 ≤ δpos) (h1 : 0 ≤ δbits) (h2 : 0 ≤ κ0) (h3 : 0 ≤ κ1) :
    μ {ω | bReg d n δ + 1 < regEnv P K n s0 orc coin loss noise ω} ≤
      ENNReal.ofReal (δpos + deltaRef d n δ + δbits + n * (κ0 + κ1)) := by
  have hS' := hS d n δ K (Ω × (ℕ → ℝ)) W R δpos δbits κ0 κ1 hreg hKc hKv hE.law hpos hC hTV hM hb hEng h0 h1 h2 h3
  rw [hE.meas_eq] at hS'
  rw [← prob_ext μ {ω | bReg d n δ + 1 < regEnv P K n s0 orc coin loss noise ω}]
  refine le_trans (le_of_eq ?_) hS'
  congr 1
  ext p
  simp only [Set.mem_ofPred_eq, regEnv, Unified.regretU, regretPts]
  have hsum : ∑ t ∈ Finset.range n, (Unified.envWorld orc coin loss noise p.1).f t
      (BitRAMO.playedO P (Unified.envWorld orc coin loss noise p.1) s0 t) =
      ∑ t ∈ Finset.range n, R.loss p t (R.play t p) :=
    Finset.sum_congr rfl fun t ht => by
      rw [hloss p t (Finset.mem_range.mp ht), hplay p t (Finset.mem_range.mp ht)]; rfl
  have hinf : (fun y => ∑ t ∈ Finset.range n, (Unified.envWorld orc coin loss noise p.1).f t y) =
      fun y => ∑ t ∈ Finset.range n, R.loss p t y :=
    funext fun y => Finset.sum_congr rfl fun t ht => by rw [hloss p t (Finset.mem_range.mp ht)]; rfl
  rw [hsum, hinf]

end Assembly

end AdversarialBco.Unified.World
