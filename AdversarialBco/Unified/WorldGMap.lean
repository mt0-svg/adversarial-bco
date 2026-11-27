/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.WorldGen
public import AdversarialBco.Bit.CoinSchedLaw
public import AdversarialBco.Bit.ShadowCoup

@[expose] public section

/-!
# The Gaussian stream of the extension

The schedule of Bit/CoinSched.lean with a prologue of `P0` whole blocks (`K0 = 2 B P0` coins) and rounds of `nBlk d`
blocks of `2 B` coins. The coined blocks are the prologue blocks and the blocks of the rounds `< n`; their coins are
`cj P0 B a s`. From coins `c` and fresh terms `v`, `gmap d n P0 B c v` is the stream whose pair under a coined block
`a` is the FILL section `fillB B` (WorldGen.lean, `exists_fill`, for the block map `blkMap B` of the Gaussian pair) at
the block's coins and the uniform `phiI (v i_a)`, `i_a` the first index of the pair; every other term is `v i`.

* `beta_gmap`: the digits of the stream are the coins, for every coin read before round `n`, everywhere;
* `measurable_gmap`, `gmap_law`: under `coinStream ⊗ gaussStream` the stream is a Gaussian stream;
* `gmap_pair`, `gmap_v`: the terms of the stream as functions of the coins and the fresh terms;
* `winL`, `winN`, `SchedOK`: the windows of the program of the route and the schedule the extension covers.
-/

open MeasureTheory ProbabilityTheory
open scoped unitInterval

namespace AdversarialBco.Unified.World

open AdversarialBco.RealRAM AdversarialBco.BitRAM AdversarialBco.Bit AdversarialBco.Bit.Cpl AdversarialBco.Bit.Sched
open AdversarialBco.Bit.Cpl.MaxCoup (phiI measurable_phiI map_phiI)

/-! ## The schedule -/

/-- The loss window of round `t`: the coins read before the blocks of round `t` (the route's `D(t)`, 0-indexed). -/
def winL (d K0 B t : ℕ) : ℕ := blkStart d K0 B t 0

/-- The noise window of round `t`: the coins read before the dither block of round `t` (the route's `κ_t`). -/
def winN (d K0 B t : ℕ) : ℕ := blkStart d K0 B t (nBlk d - 1)

/-- The schedule that the extension covers, for the program lane: blocks of `2 B > 0` coins, a prologue of whole
blocks, the loss window `winL` and the noise window `winN`. -/
def SchedOK (d K0 B : ℕ) (D D' : ℕ → ℕ) : Prop :=
  0 < B ∧ 2 * B ∣ K0 ∧ D = winL d K0 B ∧ D' = winN d K0 B

/-! ## Coined blocks and their coins -/

/-- The blocks that carry coins in the extension: the prologue blocks `k < P0` and the blocks of the rounds `< n`. -/
def coined (d n P0 : ℕ) : ℕ ⊕ ℕ → Prop
  | .inl k => k < P0
  | .inr k => k < n * nBlk d

instance (d n P0 : ℕ) : DecidablePred (coined d n P0) := fun a => by
  cases a <;> unfold coined <;> infer_instance

/-- The coin of slot `s` of block `a`. -/
def cj (P0 B : ℕ) : ℕ ⊕ ℕ → ℕ → ℕ
  | .inl k, s => 2 * B * k + s
  | .inr k, s => 2 * B * P0 + 2 * B * k + s

/-- The coins of block `a`. -/
def cbk (P0 B : ℕ) (c : ℕ → Bool) (a : ℕ ⊕ ℕ) : Fin (2 * B) → Bool := fun s => c (cj P0 B a s)

theorem div_mod_block {B k s : ℕ} (hs : s < 2 * B) : (2 * B * k + s) / (2 * B) = k ∧ (2 * B * k + s) % (2 * B) = s := by
  have hB : 0 < 2 * B := by omega
  constructor
  · rw [Nat.add_comm, Nat.add_mul_div_left _ _ hB, Nat.div_eq_of_lt hs, zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hs]

theorem blkOf_cj {d n P0 B : ℕ} {a : ℕ ⊕ ℕ} (ha : coined d n P0 a) {s : ℕ} (hs : s < 2 * B) :
    blkOf (2 * B * P0) B (cj P0 B a s) = a ∧ posOf (2 * B * P0) B (cj P0 B a s) = s := by
  obtain ⟨h1, h2⟩ := div_mod_block (k := match a with | .inl k => k | .inr k => k) hs
  cases a with
  | inl k =>
    simp only [coined] at ha
    have hlt : 2 * B * k + s < 2 * B * P0 := by
      have : 2 * B * (k + 1) ≤ 2 * B * P0 := Nat.mul_le_mul_left _ ha
      nlinarith
    simp only [cj, blkOf, posOf, hlt, ↓reduceIte]
    exact ⟨by rw [h1], h2⟩
  | inr k =>
    have hge : ¬ 2 * B * P0 + 2 * B * k + s < 2 * B * P0 := by omega
    have he : 2 * B * P0 + 2 * B * k + s - 2 * B * P0 = 2 * B * k + s := by omega
    simp only [cj, blkOf, posOf, hge, ↓reduceIte, he]
    exact ⟨by rw [h1], h2⟩

theorem cj_blkOf {d n P0 B j : ℕ} (hB : 0 < B) (hj : j < blkStart d (2 * B * P0) B n 0) :
    coined d n P0 (blkOf (2 * B * P0) B j) ∧ cj P0 B (blkOf (2 * B * P0) B j) (posOf (2 * B * P0) B j) = j := by
  have hB2 : 0 < 2 * B := by omega
  unfold blkStart at hj
  rw [add_zero] at hj
  by_cases hK : j < 2 * B * P0
  · simp only [blkOf, posOf, hK, ↓reduceIte, coined, cj]
    refine ⟨(Nat.div_lt_iff_lt_mul hB2).mpr (by rw [Nat.mul_comm]; exact hK), Nat.div_add_mod j (2 * B)⟩
  · simp only [blkOf, posOf, hK, ↓reduceIte, coined, cj]
    refine ⟨(Nat.div_lt_iff_lt_mul hB2).mpr ?_, ?_⟩
    · have : j - 2 * B * P0 < 2 * B * (n * nBlk d) := by omega
      rw [Nat.mul_comm (n * nBlk d) (2 * B)]; exact this
    · have := Nat.div_add_mod (j - 2 * B * P0) (2 * B)
      omega

theorem cj_injOn {d n P0 B : ℕ} {a a' : ℕ ⊕ ℕ} (ha : coined d n P0 a) (ha' : coined d n P0 a') {s s' : ℕ}
    (hs : s < 2 * B) (hs' : s' < 2 * B) (h : cj P0 B a s = cj P0 B a' s') : a = a' ∧ s = s' := by
  obtain ⟨h1, h2⟩ := blkOf_cj (d := d) (n := n) ha hs
  obtain ⟨h1', h2'⟩ := blkOf_cj (d := d) (n := n) ha' hs'
  rw [h] at h1 h2
  exact ⟨h1.symm.trans h1', h2.symm.trans h2'⟩

/-! ## The FILL section of the block map -/

theorem blkMap_fiber_pos (B : ℕ) (c : Fin (2 * B) → Bool) : (gaussK 2) (blkMap B ⁻¹' {c}) ≠ 0 := by
  rw [← Measure.map_apply (measurable_blkMap B) (measurableSet_singleton c)]
  have hl : (gaussK 2).map (blkMap B) = Measure.pi fun _ : Fin (2 * B) => coinLaw := blk_law B
  rw [hl, ← Set.univ_pi_singleton c, Measure.pi_pi]
  exact Finset.prod_ne_zero_iff.mpr fun s _ => by cases c s <;> simp [coinLaw]

theorem exists_fillB (B : ℕ) :
    ∃ f : (Fin (2 * B) → Bool) → I → (Fin 2 → ℝ), Measurable (Function.uncurry f) ∧
      (∀ c u, blkMap B (f c u) = c) ∧
      (((gaussK 2).map (blkMap B)).prod (volume : Measure I)).map (Function.uncurry f) = gaussK 2 :=
  exists_fill (gaussK 2) (blkMap B) (measurable_blkMap B) (blkMap_fiber_pos B)

/-- The FILL section of the block map: a Gaussian pair with the given `2 B` digits, from a uniform seed. -/
noncomputable def fillB (B : ℕ) : (Fin (2 * B) → Bool) → I → (Fin 2 → ℝ) := Classical.choose (exists_fillB B)

theorem measurable_fillB (B : ℕ) : Measurable (Function.uncurry (fillB B)) := (Classical.choose_spec (exists_fillB B)).1

theorem blkMap_fillB (B : ℕ) (c : Fin (2 * B) → Bool) (u : I) : blkMap B (fillB B c u) = c :=
  (Classical.choose_spec (exists_fillB B)).2.1 c u

theorem fillB_law (B : ℕ) :
    ((Measure.pi fun _ : Fin (2 * B) => coinLaw).prod (volume : Measure I)).map (Function.uncurry (fillB B)) =
      gaussK 2 := by
  rw [← blk_law B]
  exact (Classical.choose_spec (exists_fillB B)).2.2

/-! ## The stream -/

/-- The stream of the extension. -/
noncomputable def gmap (d n P0 B : ℕ) (c : ℕ → Bool) (v : ℕ → ℝ) (i : ℕ) : ℝ :=
  match Function.partialInv (pairIdx d) i with
  | some p => if coined d n P0 p.1 then fillB B (cbk P0 B c p.1) (phiI (v (pairIdx d (p.1, 0)))) p.2 else v i
  | none => v i

variable {d n P0 B : ℕ}

theorem gmap_pair {a : ℕ ⊕ ℕ} (ha : coined d n P0 a) (s : Fin 2) (c : ℕ → Bool) (v : ℕ → ℝ) :
    gmap d n P0 B c v (pairIdx d (a, s)) = fillB B (cbk P0 B c a) (phiI (v (pairIdx d (a, 0)))) s := by
  unfold gmap
  rw [Function.partialInv_left (pairIdx_injective d)]
  simp only [ha, ↓reduceIte]

theorem gmap_v {i : ℕ} (hi : ∀ a s, pairIdx d (a, s) = i → ¬ coined d n P0 a) (c : ℕ → Bool) (v : ℕ → ℝ) :
    gmap d n P0 B c v i = v i := by
  unfold gmap
  rcases h : Function.partialInv (pairIdx d) i with _ | p
  · rfl
  · have hp : pairIdx d p = i := ((pairIdx_injective d).isPartialInv p i).mp h
    simp only [hi p.1 p.2 hp, ↓reduceIte]

theorem pairIdx_zero (a : ℕ ⊕ ℕ) : pairIdx d (a, 0) = (pairOf d a).1 := rfl

theorem pairIdx_one (a : ℕ ⊕ ℕ) : pairIdx d (a, 1) = (pairOf d a).2 := rfl

/-- The digits of the stream are the coins, for every coin read before round `n`, on every point. -/
theorem beta_gmap (hB : 0 < B) (c : ℕ → Bool) (v : ℕ → ℝ) {j : ℕ} (hj : j < blkStart d (2 * B * P0) B n 0) :
    Sched.beta d (2 * B * P0) B (gmap d n P0 B c v) j = c j := by
  obtain ⟨hco, hcj⟩ := cj_blkOf (d := d) (n := n) (P0 := P0) hB hj
  set a := blkOf (2 * B * P0) B j
  unfold Sched.beta
  rw [← pairIdx_zero, ← pairIdx_one, gmap_pair hco, gmap_pair hco]
  have hpos := posOf_lt (K0 := 2 * B * P0) hB j
  have h := congrFun (blkMap_fillB B (cbk P0 B c a) (phiI (v (pairIdx d (a, 0))))) ⟨posOf (2 * B * P0) B j, hpos⟩
  simp only [blkMap, cbk] at h
  rw [h, hcj]

theorem measurable_cbk (a : ℕ ⊕ ℕ) : Measurable fun c : ℕ → Bool => cbk P0 B c a :=
  measurable_pi_iff.mpr fun _ => measurable_pi_apply _

theorem measurable_gmap : Measurable fun q : (ℕ → Bool) × (ℕ → ℝ) => gmap d n P0 B q.1 q.2 := by
  refine measurable_pi_iff.mpr fun i => ?_
  unfold gmap
  rcases h : Function.partialInv (pairIdx d) i with _ | p
  · exact (measurable_pi_apply i).comp measurable_snd
  · simp only
    split_ifs
    · have hm : Measurable fun q : (ℕ → Bool) × (ℕ → ℝ) =>
          fillB B (cbk P0 B q.1 p.1) (phiI (q.2 (pairIdx d (p.1, 0)))) :=
        (measurable_fillB B).comp (((measurable_cbk p.1).comp measurable_fst).prodMk
          (measurable_phiI.comp ((measurable_pi_apply _).comp measurable_snd)))
      exact (measurable_pi_apply p.2).comp hm
    · exact (measurable_pi_apply i).comp measurable_snd

/-! ## The law of the stream -/

section Law

variable (d n P0 B)

/-- The coined blocks. -/
abbrev Rb : Type := {a : ℕ ⊕ ℕ // coined d n P0 a}

/-- The terms of the stream under the coined blocks. -/
def fP (q : Rb d n P0 × Fin 2) : ℕ := pairIdx d (q.1.1, q.2)

theorem fP_inj : Function.Injective (fP d n P0) := by
  intro q q' h
  have h' := pairIdx_injective d h
  simp only [Prod.mk.injEq] at h'
  exact Prod.ext (Subtype.ext h'.1) h'.2

/-- The free terms of the stream. -/
abbrev Fr : Type := ↥(Set.range (fP d n P0))ᶜ

/-- The terms of the stream: the pairs of the coined blocks and the free terms. -/
noncomputable def eqv : (Rb d n P0 × Fin 2) ⊕ Fr d n P0 ≃ ℕ := by
  classical
  exact (Equiv.sumCongr (Equiv.ofInjective _ (fP_inj d n P0)) (Equiv.refl _)).trans
    (Equiv.Set.sumCompl (Set.range (fP d n P0)))

theorem eqv_inl (q : Rb d n P0 × Fin 2) : eqv d n P0 (.inl q) = fP d n P0 q := by
  classical
  simp [eqv, Equiv.Set.sumCompl_apply_inl]

theorem eqv_inr (z : Fr d n P0) : eqv d n P0 (.inr z) = z.1 := by
  classical
  simp [eqv, Equiv.Set.sumCompl_apply_inr]

/-- The coins of the coined blocks. -/
def cIn (c : ℕ → Bool) : Rb d n P0 → Fin (2 * B) → Bool := fun a => cbk P0 B c a.1

/-- The fresh terms: the seeds of the coined blocks and the free terms. -/
def vIn (v : ℕ → ℝ) : (Rb d n P0 → ℝ) × (Fr d n P0 → ℝ) :=
  (fun a => v (pairIdx d (a.1, 0)), fun z => v z.1)

/-- The block maps. -/
noncomputable def blockOut (x : Rb d n P0 → (Fin (2 * B) → Bool) × ℝ) : Rb d n P0 → Fin 2 → ℝ :=
  fun a => fillB B (x a).1 (phiI (x a).2)

/-- The stream from the pairs of the coined blocks and the free terms. -/
noncomputable def assemble (y : (Rb d n P0 → Fin 2 → ℝ) × (Fr d n P0 → ℝ)) : ℕ → ℝ :=
  fun i => Sum.elim (fun q : Rb d n P0 × Fin 2 => y.1 q.1 q.2) y.2 ((eqv d n P0).symm i)

theorem gmap_eq_assemble (c : ℕ → Bool) (v : ℕ → ℝ) :
    gmap d n P0 B c v = assemble d n P0
      (blockOut d n P0 B (fun a => (cIn d n P0 B c a, (vIn d n P0 v).1 a)), (vIn d n P0 v).2) := by
  funext i
  obtain ⟨k, rfl⟩ := (eqv d n P0).surjective i
  unfold assemble
  rw [Equiv.symm_apply_apply]
  cases k with
  | inl q =>
    rw [eqv_inl]
    simp only [fP, Sum.elim_inl, blockOut, cIn, vIn]
    exact gmap_pair q.1.2 q.2 c v
  | inr z =>
    rw [eqv_inr]
    simp only [Sum.elim_inr, vIn]
    refine gmap_v (fun a s h ha => z.2 ⟨(⟨a, ha⟩, s), h⟩) c v

theorem measurable_cIn : Measurable (cIn d n P0 B) :=
  measurable_pi_iff.mpr fun a => measurable_cbk a.1

theorem measurable_vIn : Measurable (vIn d n P0) :=
  (measurable_pi_iff.mpr fun _ => measurable_pi_apply _).prodMk (measurable_pi_iff.mpr fun _ => measurable_pi_apply _)

theorem measurable_blockOut : Measurable (blockOut d n P0 B) := by
  refine measurable_pi_iff.mpr fun a => ?_
  exact (measurable_fillB B).comp ((measurable_pi_apply a).fst.prodMk (measurable_phiI.comp (measurable_pi_apply a).snd))

theorem measurable_assemble : Measurable (assemble d n P0) := by
  refine measurable_pi_iff.mpr fun i => ?_
  unfold assemble
  cases (eqv d n P0).symm i with
  | inl q => exact (measurable_pi_apply q.2).comp ((measurable_pi_apply q.1).comp measurable_fst)
  | inr z => exact (measurable_pi_apply z).comp measurable_snd

/-- The coins of the coined blocks are fair and independent. -/
theorem cIn_law :
    coinStream.map (cIn d n P0 B) = Measure.infinitePi fun _ : Rb d n P0 => Measure.pi fun _ : Fin (2 * B) => coinLaw := by
  let e1 : Rb d n P0 × Fin (2 * B) → ℕ := fun q => cj P0 B q.1.1 q.2
  have he1 : Function.Injective e1 := by
    intro q q' h
    obtain ⟨h1, h2⟩ := cj_injOn (d := d) (n := n) q.1.2 q'.1.2 q.2.2 q'.2.2 h
    exact Prod.ext (Subtype.ext h1) (Fin.ext h2)
  have hfac : cIn d n P0 B = (MeasurableEquiv.curry (Rb d n P0) (Fin (2 * B)) Bool) ∘
      fun c : ℕ → Bool => fun q => c (e1 q) := by
    funext c a s; rfl
  have hm1 : Measurable fun c : ℕ → Bool => fun q : Rb d n P0 × Fin (2 * B) => c (e1 q) :=
    measurable_pi_iff.mpr fun _ => measurable_pi_apply _
  rw [hfac, ← Measure.map_map (MeasurableEquiv.curry _ _ _).measurable hm1, coinStream,
    infinitePi_map_comp_injective coinLaw he1, Measure.infinitePi_map_curry (fun _ _ => coinLaw)]
  congr 1
  funext a
  exact Measure.infinitePi_eq_pi _

/-- The fresh terms: seeds and free terms are independent standard Gaussians. -/
theorem vIn_law :
    gaussStream.map (vIn d n P0) =
      (Measure.infinitePi fun _ : Rb d n P0 => gaussianReal 0 1).prod
        (Measure.infinitePi fun _ : Fr d n P0 => gaussianReal 0 1) := by
  let e2 : Rb d n P0 ⊕ Fr d n P0 → ℕ := Sum.elim (fun a => pairIdx d (a.1, 0)) (fun z => z.1)
  have he2 : Function.Injective e2 := by
    intro x y h
    cases x with
    | inl a =>
      cases y with
      | inl a' =>
        have := fP_inj d n P0 (show fP d n P0 (a, 0) = fP d n P0 (a', 0) from h)
        rw [(Prod.mk.injEq _ _ _ _).mp this |>.1]
      | inr z' => exact absurd ⟨(a, 0), h⟩ z'.2
    | inr z =>
      cases y with
      | inl a' => exact absurd ⟨(a', 0), h.symm⟩ z.2
      | inr z' => rw [Subtype.ext h]
  have hfac : vIn d n P0 = (fun x : Rb d n P0 ⊕ Fr d n P0 → ℝ => (fun a => x (.inl a), fun z => x (.inr z))) ∘
      fun v : ℕ → ℝ => fun k => v (e2 k) := by
    funext v; rfl
  have hm2 : Measurable fun v : ℕ → ℝ => fun k : Rb d n P0 ⊕ Fr d n P0 => v (e2 k) :=
    measurable_pi_iff.mpr fun _ => measurable_pi_apply _
  have hs : Measurable fun x : Rb d n P0 ⊕ Fr d n P0 → ℝ => (fun a => x (.inl a), fun z => x (.inr z)) :=
    (measurable_pi_iff.mpr fun _ => measurable_pi_apply _).prodMk (measurable_pi_iff.mpr fun _ => measurable_pi_apply _)
  rw [hfac, ← Measure.map_map hs hm2, gaussStream, infinitePi_map_comp_injective _ he2]
  exact infinitePi_split (gaussianReal 0 1)

/-- A block map carries fair coins and a Gaussian seed to a Gaussian pair. -/
theorem block_law :
    ((Measure.pi fun _ : Fin (2 * B) => coinLaw).prod (gaussianReal 0 1)).map
      (fun x : (Fin (2 * B) → Bool) × ℝ => fillB B x.1 (phiI x.2)) = gaussK 2 := by
  have h1 : ((Measure.pi fun _ : Fin (2 * B) => coinLaw).prod (gaussianReal 0 1)).map (Prod.map id phiI) =
      (Measure.pi fun _ : Fin (2 * B) => coinLaw).prod (volume : Measure I) := by
    rw [← Measure.map_prod_map _ _ measurable_id measurable_phiI, Measure.map_id, map_phiI]
  have hfac : (fun x : (Fin (2 * B) → Bool) × ℝ => fillB B x.1 (phiI x.2)) =
      Function.uncurry (fillB B) ∘ Prod.map id phiI := by
    funext x; rfl
  rw [hfac, ← Measure.map_map (measurable_fillB B) (measurable_id.prodMap measurable_phiI), h1, fillB_law]

/-- Under `coinStream ⊗ gaussStream`, the stream of the extension is a Gaussian stream. -/
theorem gmap_law :
    (coinStream.prod gaussStream).map (fun q : (ℕ → Bool) × (ℕ → ℝ) => gmap d n P0 B q.1 q.2) = gaussStream := by
  set U := Measure.pi fun _ : Fin (2 * B) => coinLaw
  set γ := gaussianReal 0 1
  let zipR : (Rb d n P0 → Fin (2 * B) → Bool) × (Rb d n P0 → ℝ) → Rb d n P0 → (Fin (2 * B) → Bool) × ℝ :=
    fun p a => (p.1 a, p.2 a)
  have hzip : Measurable zipR := by
    refine measurable_pi_iff.mpr fun a => ?_
    exact ((measurable_pi_apply a).comp measurable_fst).prodMk ((measurable_pi_apply a).comp measurable_snd)
  let M1 := Prod.map (cIn d n P0 B) (vIn d n P0)
  let M2 := (MeasurableEquiv.prodAssoc :
    ((Rb d n P0 → Fin (2 * B) → Bool) × (Rb d n P0 → ℝ)) × (Fr d n P0 → ℝ) ≃ᵐ _).symm
  let M3 := Prod.map zipR (id : (Fr d n P0 → ℝ) → (Fr d n P0 → ℝ))
  let M4 := Prod.map (blockOut d n P0 B) (id : (Fr d n P0 → ℝ) → (Fr d n P0 → ℝ))
  have hM1 : Measurable M1 := (measurable_cIn d n P0 B).prodMap (measurable_vIn d n P0)
  have hM3 : Measurable M3 := hzip.prodMap measurable_id
  have hM4 : Measurable M4 := (measurable_blockOut d n P0 B).prodMap measurable_id
  have hG : (fun q : (ℕ → Bool) × (ℕ → ℝ) => gmap d n P0 B q.1 q.2) = assemble d n P0 ∘ M4 ∘ M3 ∘ M2 ∘ M1 := by
    funext q
    rw [gmap_eq_assemble]
    rfl
  rw [hG, ← Measure.map_map (measurable_assemble d n P0) (hM4.comp (hM3.comp (M2.measurable.comp hM1))),
    ← Measure.map_map hM4 (hM3.comp (M2.measurable.comp hM1)), ← Measure.map_map hM3 (M2.measurable.comp hM1),
    ← Measure.map_map M2.measurable hM1]
  have h1 : (coinStream.prod gaussStream).map M1 =
      (Measure.infinitePi fun _ : Rb d n P0 => U).prod
        ((Measure.infinitePi fun _ : Rb d n P0 => γ).prod (Measure.infinitePi fun _ : Fr d n P0 => γ)) := by
    rw [← Measure.map_prod_map _ _ (measurable_cIn d n P0 B) (measurable_vIn d n P0), cIn_law d n P0 B,
      vIn_law d n P0]
  have h2 := (measurePreserving_prodAssoc (Measure.infinitePi fun _ : Rb d n P0 => U)
    (Measure.infinitePi fun _ : Rb d n P0 => γ) (Measure.infinitePi fun _ : Fr d n P0 => γ)).symm.map_eq
  have h3 : (((Measure.infinitePi fun _ : Rb d n P0 => U).prod (Measure.infinitePi fun _ : Rb d n P0 => γ)).prod
      (Measure.infinitePi fun _ : Fr d n P0 => γ)).map M3 =
      (Measure.infinitePi fun _ : Rb d n P0 => U.prod γ).prod (Measure.infinitePi fun _ : Fr d n P0 => γ) := by
    rw [← Measure.map_prod_map _ _ hzip measurable_id, Measure.map_id, infinitePi_zip U γ]
  have h4 : ((Measure.infinitePi fun _ : Rb d n P0 => U.prod γ).prod
      (Measure.infinitePi fun _ : Fr d n P0 => γ)).map M4 =
      (Measure.infinitePi fun _ : Rb d n P0 => gaussK 2).prod (Measure.infinitePi fun _ : Fr d n P0 => γ) := by
    rw [← Measure.map_prod_map _ _ (measurable_blockOut d n P0 B) measurable_id, Measure.map_id]
    congr 1
    have hb : Measurable fun x : (Fin (2 * B) → Bool) × ℝ => fillB B x.1 (phiI x.2) :=
      (measurable_fillB B).comp (measurable_fst.prodMk (measurable_phiI.comp measurable_snd))
    rw [show blockOut d n P0 B = fun x a => (fun _ : Rb d n P0 => fun x : (Fin (2 * B) → Bool) × ℝ =>
        fillB B x.1 (phiI x.2)) a (x a) from rfl, Measure.infinitePi_map_pi _ (fun _ => hb)]
    congr 1
    funext a
    exact block_law (B := B)
  have h5 : ((Measure.infinitePi fun _ : Rb d n P0 => gaussK 2).prod
      (Measure.infinitePi fun _ : Fr d n P0 => γ)).map (assemble d n P0) = gaussStream := by
    have hK : (Measure.infinitePi fun _ : Rb d n P0 => gaussK 2) =
        Measure.infinitePi fun _ : Rb d n P0 => Measure.infinitePi fun _ : Fin 2 => γ := by
      congr 1; funext a; exact (Measure.infinitePi_eq_pi _).symm
    let A1 := Prod.map (MeasurableEquiv.curry (Rb d n P0) (Fin 2) ℝ).symm (id : (Fr d n P0 → ℝ) → (Fr d n P0 → ℝ))
    let A2 := fun p : (Rb d n P0 × Fin 2 → ℝ) × (Fr d n P0 → ℝ) => Sum.elim p.1 p.2
    let A3 := fun x : (Rb d n P0 × Fin 2) ⊕ Fr d n P0 → ℝ => fun i => x ((eqv d n P0).symm i)
    have hA1 : Measurable A1 := (MeasurableEquiv.curry _ _ _).symm.measurable.prodMap measurable_id
    have hA2 : Measurable A2 := by
      refine measurable_pi_iff.mpr fun k => ?_
      cases k with
      | inl a => exact (measurable_pi_apply a).comp measurable_fst
      | inr b => exact (measurable_pi_apply b).comp measurable_snd
    have hA3 : Measurable A3 := measurable_pi_iff.mpr fun _ => measurable_pi_apply _
    have hfac : assemble d n P0 = A3 ∘ A2 ∘ A1 := by
      funext y i
      simp only [assemble, Function.comp, A1, A2, A3, Prod.map]
      cases (eqv d n P0).symm i <;> rfl
    rw [hfac, ← Measure.map_map hA3 (hA2.comp hA1), ← Measure.map_map hA2 hA1, hK,
      ← Measure.map_prod_map _ _ (MeasurableEquiv.curry _ _ _).symm.measurable measurable_id, Measure.map_id,
      Measure.infinitePi_map_curry_symm (fun _ _ => γ), infinitePi_sumElim γ, gaussStream]
    exact infinitePi_map_comp_injective γ (eqv d n P0).symm.injective
  rw [h1, h2, h3, h4, h5]

end Law

end AdversarialBco.Unified.World
