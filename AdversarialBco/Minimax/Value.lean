/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Minimax.Tail
public import AdversarialBco.UnifiedLower.Sanity
public import Mathlib.MeasureTheory.Integral.Layercake

@[expose] public section

/-!
# The values of the game: ranges, nonemptiness, and the sandwich lemmas

For a learner of `Learners` (the programs with windows that meet `MachineOK`) and every environment with its windows,
the regret lies in `[-n, n]` on every `ω` (`regretPts_mem`: the losses are in `[0, 1]` on `K`, the plays of the rounds
`t < n` in `K`), so its tail is a `TailOK n` (`tailOK`). Every learner has environments with its windows (the constant
loss with zero noise on the coin space, `noisyAdv_const` of UnifiedLower/Sanity.lean), so its payoffs form a nonempty
set (`payoffs_nonempty`) inside the range of the payoff (`payoffs_subset`): `[0, n]` for the mean, `[-n, n]` for the
`(1 - δ')`-quantile with `δ' < 1` (`meanPosOf_range`, `quantileOf_range`). Hence:

* `value_le`: a learner of the class whose payoffs are all at most `X` puts the value at most `X`;
* `le_value`: if the class is nonempty and every learner has a payoff at least `Y`, the value is at least `Y`;
* `value_anti`: a nonempty subclass has a larger value (`LearnersB B ⊆ Learners`, `learnersB_subset`).

The probability forms, with nothing else, then give the four bounds of the theorem:

* from above (`payoff_le_of_prob`): an environment in which `μ {Reg_n > U} ≤ δ` (`0 ≤ U`, `0 ≤ δ < 1`) has quantile
  payoff at most `U` and mean payoff at most `U + n δ`;
* from below (`le_valQuant_of`, `le_valMean_of`): if every learner has an environment with `μ {Reg_n ≥ L} > δ'`, the
  quantile value is at least `L`; with `μ {Reg_n ≥ L} ≥ p` and `L ≥ 0`, the mean value is at least `p L`.

`meanPosOf_tail_eq_ae`: for an almost everywhere strongly measurable regret the mean payoff is `∫ max(Reg_n, 0) dμ`
(the layer cake formula).
-/

open MeasureTheory Set

namespace AdversarialBco.Minimax

open BitRAM BitRAMO Unified UnifiedLower UnifiedLower.LowerSanity
open RealRAM (regretPts)

variable {d : ℕ}

/-! ## The regret of a learner lies in `[-n, n]` -/

/-- The regret against losses in `[0, 1]` on a nonempty `K`, at points of `K`, lies in `[-n, n]`. -/
theorem regretPts_mem {K : Set (E d)} (hne : K.Nonempty) {n : ℕ} {f : ℕ → E d → ℝ} {x : ℕ → E d}
    (hf : ∀ t < n, ∀ y ∈ K, f t y ∈ Icc (0 : ℝ) 1) (hx : ∀ t < n, x t ∈ K) :
    regretPts K f x n ∈ Icc (-(n : ℝ)) n := by
  have hsum : ∀ z : ℕ → E d, (∀ t < n, z t ∈ K) →
      ∑ t ∈ Finset.range n, f t (z t) ∈ Icc (0 : ℝ) n := by
    intro z hz
    refine ⟨Finset.sum_nonneg fun t ht => (hf t (Finset.mem_range.1 ht) _ (hz t (Finset.mem_range.1 ht))).1, ?_⟩
    calc ∑ t ∈ Finset.range n, f t (z t) ≤ ∑ _t ∈ Finset.range n, (1 : ℝ) :=
          Finset.sum_le_sum fun t ht => (hf t (Finset.mem_range.1 ht) _ (hz t (Finset.mem_range.1 ht))).2
      _ = n := by simp
  obtain ⟨y0, hy0⟩ := hne
  have hS := hsum x hx
  have hY := hsum (fun _ => y0) fun _ _ => hy0
  have himne : ((fun y => ∑ t ∈ Finset.range n, f t y) '' K).Nonempty := ⟨_, y0, hy0, rfl⟩
  have hlow : ∀ v ∈ (fun y => ∑ t ∈ Finset.range n, f t y) '' K, (0 : ℝ) ≤ v := by
    rintro v ⟨y, hy, rfl⟩
    exact (hsum (fun _ => y) fun _ _ => hy).1
  have hI0 : 0 ≤ sInf ((fun y => ∑ t ∈ Finset.range n, f t y) '' K) := le_csInf himne hlow
  have hIn : sInf ((fun y => ∑ t ∈ Finset.range n, f t y) '' K) ≤ n :=
    (csInf_le ⟨0, hlow⟩ ⟨y0, hy0, rfl⟩).trans hY.2
  unfold regretPts
  constructor <;> linarith [hS.1, hS.2]

variable {K : Set (E d)} {orc : (Fin d → ℚ) → ℕ → Bool} {s0 : State d} {n : ℕ}

/-- The learners within cost and space `B` are learners. -/
theorem learnersB_subset (B : ℝ) : LearnersB K orc s0 n B ⊆ Learners K orc s0 n :=
  fun _ h => ⟨B, fun f noise cs hf => ⟨(h f noise cs hf).1, (h f noise cs hf).2.2.1, (h f noise cs hf).2.2.2⟩⟩

/-- The regret of a learner in an environment with its windows lies in `[-n, n]` at every `ω`. -/
theorem regret_mem {ℓ : ProgWin} (hℓ : ℓ ∈ Learners K orc s0 n) (hne : K.Nonempty) {Ω : Type}
    [MeasurableSpace Ω] {μ : Measure Ω} {coin : Ω → ℕ → Bool} {loss : ℕ → Ω → E d → ℝ} {noise : ℕ → Ω → ℝ}
    (hA : NoisyAdv K n ℓ.D ℓ.D' μ coin loss noise) (ω : Ω) :
    regretU ℓ.prog K n s0 (envWorld orc coin loss noise ω) ∈ Icc (-(n : ℝ)) n := by
  obtain ⟨B, hM⟩ := hℓ
  have hadm : ∀ t < n, AdmLoss K (loss t ω) := fun t ht => hA.adm t ht ω
  exact regretPts_mem hne (fun t ht y hy => (hadm t ht).2 y hy)
    (hM (fun t => loss t ω) (fun t => noise t ω) (coin ω) hadm).2.1

/-- The tail of the regret of a learner in an environment with its windows is a `TailOK n`. -/
theorem tailOK {ℓ : ProgWin} (hℓ : ℓ ∈ Learners K orc s0 n) (hne : K.Nonempty) {Ω : Type}
    [MeasurableSpace Ω] {μ : Measure Ω} {coin : Ω → ℕ → Bool} {loss : ℕ → Ω → E d → ℝ} {noise : ℕ → Ω → ℝ}
    (hA : NoisyAdv K n ℓ.D ℓ.D' μ coin loss noise) : TailOK n (tailU ℓ.prog K n s0 orc μ coin loss noise) := by
  have := hA.prob
  refine ⟨fun u => prob_le_one, fun u hu => ?_, fun u hu => ?_⟩
  · have : {ω | u < regretU ℓ.prog K n s0 (envWorld orc coin loss noise ω)} = ∅ :=
      eq_empty_iff_forall_notMem.2 fun ω hω => absurd (lt_of_lt_of_le hω (regret_mem hℓ hne hA ω).2) (not_lt.2 hu)
    rw [tailU, this, measure_empty]
  · have : {ω | u < regretU ℓ.prog K n s0 (envWorld orc coin loss noise ω)} = univ :=
      eq_univ_of_forall fun ω => lt_of_lt_of_le hu (regret_mem hℓ hne hA ω).1
    rw [tailU, this, measure_univ]

/-- The tail is antitone. -/
theorem tailU_anti (P : List InstrO) {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (coin : Ω → ℕ → Bool)
    (loss : ℕ → Ω → E d → ℝ) (noise : ℕ → Ω → ℝ) : Antitone (tailU P K n s0 orc μ coin loss noise) :=
  fun _ _ huv => measure_mono fun _ hω => lt_of_le_of_lt huv hω

/-! ## The payoffs -/

/-- Every learner has environments with its windows: the constant loss `0` with zero noise on the coin space. -/
theorem payoffs_nonempty (hK : Convex ℝ K) (pay : (ℝ → ENNReal) → ℝ) (ℓ : ProgWin) :
    (payoffs K n s0 orc pay ℓ).Nonempty :=
  ⟨_, ℕ → Bool, inferInstance, coinStream, id, fun _ _ _ => 0, fun _ _ => 0,
    noisyAdv_const hK n ℓ.D ℓ.D' le_rfl zero_le_one, rfl⟩

/-- The payoffs of a learner lie in the range of the payoff on the tails `TailOK n`. -/
theorem payoffs_subset {pay : (ℝ → ENNReal) → ℝ} {lo hi : ℝ} (hpay : ∀ T, TailOK n T → pay T ∈ Icc lo hi)
    {ℓ : ProgWin} (hℓ : ℓ ∈ Learners K orc s0 n) (hne : K.Nonempty) : payoffs K n s0 orc pay ℓ ⊆ Icc lo hi := by
  rintro v ⟨Ω, _, μ, coin, loss, noise, hA, rfl⟩
  exact hpay _ (tailOK hℓ hne hA)

/-- The range of the mean payoff: `[0, n]`. -/
theorem meanPosOf_range : ∀ T, TailOK n T → meanPosOf T ∈ Icc (0 : ℝ) n :=
  fun _ hT => meanPosOf_mem hT n.cast_nonneg

/-- The range of the `(1 - δ')`-quantile payoff for `δ' < 1`: `[-n, n]`. -/
theorem quantileOf_range {δ' : ℝ} (hδ : δ' < 1) : ∀ T, TailOK n T → quantileOf δ' T ∈ Icc (-(n : ℝ)) n :=
  fun _ hT => quantileOf_mem hT hδ

/-- The supremum of the payoffs of a learner lies in the range of the payoff. -/
theorem sSup_payoffs_mem {pay : (ℝ → ENNReal) → ℝ} {lo hi : ℝ} (hpay : ∀ T, TailOK n T → pay T ∈ Icc lo hi)
    (hK : Convex ℝ K) (hne : K.Nonempty) {ℓ : ProgWin} (hℓ : ℓ ∈ Learners K orc s0 n) :
    sSup (payoffs K n s0 orc pay ℓ) ∈ Icc lo hi := by
  obtain ⟨v, hv⟩ := payoffs_nonempty (n := n) (s0 := s0) (orc := orc) hK pay ℓ
  have hsub := payoffs_subset hpay hℓ hne
  exact ⟨(hsub hv).1.trans (le_csSup ⟨hi, fun w hw => (hsub hw).2⟩ hv),
    csSup_le ⟨v, hv⟩ fun w hw => (hsub hw).2⟩

/-! ## The values -/

/-- The value is at most `X` if a learner `ℓ` of the class has all its payoffs at most `X`. -/
theorem value_le {L : Set ProgWin} (hL : L ⊆ Learners K orc s0 n) {pay : (ℝ → ENNReal) → ℝ} {lo hi : ℝ}
    (hpay : ∀ T, TailOK n T → pay T ∈ Icc lo hi) (hK : Convex ℝ K) (hne : K.Nonempty) {ℓ : ProgWin}
    (hℓ : ℓ ∈ L) {X : ℝ} (hX : ∀ v ∈ payoffs K n s0 orc pay ℓ, v ≤ X) : value L K n s0 orc pay ≤ X := by
  have hb : BddBelow ((fun ℓ => sSup (payoffs K n s0 orc pay ℓ)) '' L) := by
    refine ⟨lo, ?_⟩
    rintro _ ⟨ℓ', hℓ', rfl⟩
    exact (sSup_payoffs_mem hpay hK hne (hL hℓ')).1
  exact (csInf_le hb ⟨ℓ, hℓ, rfl⟩).trans (csSup_le (payoffs_nonempty hK pay ℓ) hX)

/-- The value is at least `Y` if the class is nonempty and every learner of it has a payoff at least `Y`. -/
theorem le_value {L : Set ProgWin} (hL : L ⊆ Learners K orc s0 n) (hLne : L.Nonempty)
    {pay : (ℝ → ENNReal) → ℝ} {lo hi : ℝ} (hpay : ∀ T, TailOK n T → pay T ∈ Icc lo hi) (hne : K.Nonempty)
    {Y : ℝ} (h : ∀ ℓ ∈ L, ∃ v ∈ payoffs K n s0 orc pay ℓ, Y ≤ v) : Y ≤ value L K n s0 orc pay := by
  refine le_csInf (hLne.image _) ?_
  rintro _ ⟨ℓ, hℓ, rfl⟩
  obtain ⟨v, hv, hYv⟩ := h ℓ hℓ
  exact hYv.trans (le_csSup ⟨hi, fun w hw => (payoffs_subset hpay (hL hℓ) hne hw).2⟩ hv)

/-- A nonempty subclass of learners has a value at least that of the class. -/
theorem value_anti {L1 L2 : Set ProgWin} (hL1 : L1 ⊆ Learners K orc s0 n) (h21 : L2 ⊆ L1) (hL2 : L2.Nonempty)
    {pay : (ℝ → ENNReal) → ℝ} {lo hi : ℝ} (hpay : ∀ T, TailOK n T → pay T ∈ Icc lo hi) (hK : Convex ℝ K)
    (hne : K.Nonempty) : value L1 K n s0 orc pay ≤ value L2 K n s0 orc pay := by
  refine csInf_le_csInf ⟨lo, ?_⟩ (hL2.image _) (image_mono h21)
  rintro _ ⟨ℓ, hℓ, rfl⟩
  exact (sSup_payoffs_mem hpay hK hne (hL1 hℓ)).1

/-! ## The bounds from the probability forms -/

/-- From above: in an environment where `μ {Reg_n > U} ≤ δ`, with `0 ≤ U` and `0 ≤ δ < 1`, the quantile payoff at the
level `δ` is at most `U` and the mean payoff at most `U + n δ`. -/
theorem payoff_le_of_prob {ℓ : ProgWin} (hℓ : ℓ ∈ Learners K orc s0 n) (hne : K.Nonempty) {Ω : Type}
    [MeasurableSpace Ω] {μ : Measure Ω} {coin : Ω → ℕ → Bool} {loss : ℕ → Ω → E d → ℝ} {noise : ℕ → Ω → ℝ}
    (hA : NoisyAdv K n ℓ.D ℓ.D' μ coin loss noise) {U δ : ℝ} (hU : 0 ≤ U) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hP : μ {ω | U < regretU ℓ.prog K n s0 (envWorld orc coin loss noise ω)} ≤ ENNReal.ofReal δ) :
    quantileOf δ (tailU ℓ.prog K n s0 orc μ coin loss noise) ≤ U ∧
      meanPosOf (tailU ℓ.prog K n s0 orc μ coin loss noise) ≤ U + n * δ := by
  have hT := tailOK hℓ hne hA
  exact ⟨quantileOf_le hT hδ1 hP, meanPosOf_le hT n.cast_nonneg hU hδ0 fun u hu =>
    (tailU_anti ℓ.prog μ coin loss noise hu.le).trans hP⟩

/-- From below, the quantile: if the class of learners is nonempty and every learner has an environment with its
windows in which `μ {Reg_n ≥ L} > δ'`, the `(1 - δ')`-quantile value is at least `L`. -/
theorem le_valQuant_of (hLne : (Learners K orc s0 n).Nonempty) (hne : K.Nonempty) {δ' L : ℝ} (hδ1 : δ' < 1)
    (h : ∀ ℓ ∈ Learners K orc s0 n, ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (coin : Ω → ℕ → Bool)
      (loss : ℕ → Ω → E d → ℝ) (noise : ℕ → Ω → ℝ), NoisyAdv K n ℓ.D ℓ.D' μ coin loss noise ∧
        ENNReal.ofReal δ' < μ {ω | L ≤ regretU ℓ.prog K n s0 (envWorld orc coin loss noise ω)}) :
    L ≤ value (Learners K orc s0 n) K n s0 orc (quantileOf δ') := by
  refine le_value subset_rfl hLne (quantileOf_range hδ1) hne fun ℓ hℓ => ?_
  obtain ⟨Ω, _, μ, coin, loss, noise, hA, hP⟩ := h ℓ hℓ
  refine ⟨_, ⟨Ω, inferInstance, μ, coin, loss, noise, hA, rfl⟩, le_quantileOf (tailOK hℓ hne hA) fun u hu => ?_⟩
  exact hP.trans_le (measure_mono fun ω hω => lt_of_lt_of_le hu hω)

/-- From below, the mean: if the class of learners is nonempty and every learner has an environment with its windows
in which `μ {Reg_n ≥ L} ≥ p`, with `L ≥ 0` and `p ≥ 0`, the mean value is at least `p L`. At `p = 1 - δ'` it is the
expectation form `(1 - δ') L` of a lower bound with probability `1 - δ'`. -/
theorem le_valMean_of (hLne : (Learners K orc s0 n).Nonempty) (hne : K.Nonempty) {p L : ℝ} (hL : 0 ≤ L)
    (hp : 0 ≤ p)
    (h : ∀ ℓ ∈ Learners K orc s0 n, ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (coin : Ω → ℕ → Bool)
      (loss : ℕ → Ω → E d → ℝ) (noise : ℕ → Ω → ℝ), NoisyAdv K n ℓ.D ℓ.D' μ coin loss noise ∧
        ENNReal.ofReal p ≤ μ {ω | L ≤ regretU ℓ.prog K n s0 (envWorld orc coin loss noise ω)}) :
    p * L ≤ value (Learners K orc s0 n) K n s0 orc meanPosOf := by
  refine le_value subset_rfl hLne meanPosOf_range hne fun ℓ hℓ => ?_
  obtain ⟨Ω, _, μ, coin, loss, noise, hA, hP⟩ := h ℓ hℓ
  refine ⟨_, ⟨Ω, inferInstance, μ, coin, loss, noise, hA, rfl⟩,
    le_meanPosOf (tailOK hℓ hne hA) hL hp fun u _ hu => ?_⟩
  exact hP.trans (measure_mono fun ω hω => lt_of_lt_of_le hu hω)

/-! ## The mean payoff of a measurable regret -/

/-- For an almost everywhere strongly measurable `X`, the mean of the positive part read from the tail of `X` is
`∫ max(X, 0) dμ` (the layer cake formula). -/
theorem meanPosOf_tail_eq_ae {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) {X : Ω → ℝ}
    (hX : AEStronglyMeasurable X μ) : meanPosOf (fun u => μ {ω | u < X ω}) = ∫ ω, max (X ω) 0 ∂μ := by
  have hm : AEMeasurable (fun ω => max (X ω) 0) μ := hX.aemeasurable.max aemeasurable_const
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun ω => le_max_right (X ω) 0)
    hm.aestronglyMeasurable, lintegral_eq_lintegral_meas_lt μ
    (Filter.Eventually.of_forall fun ω => le_max_right (X ω) 0) hm, meanPosOf]
  congr 1
  refine setLIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
  congr 1
  ext ω
  show u < X ω ↔ u < max (X ω) 0
  rw [lt_max_iff]
  exact (or_iff_left (not_lt.2 (le_of_lt (mem_Ioi.1 hu)))).symm

/-- For an integrable `X`, the mean of the positive part read from the tail of `X` is at least `∫ X dμ`
(`E max(X, 0) ≥ E X`). -/
theorem integral_le_meanPosOf {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) {X : Ω → ℝ} (hX : Integrable X μ) :
    ∫ ω, X ω ∂μ ≤ meanPosOf (fun u => μ {ω | u < X ω}) := by
  rw [meanPosOf_tail_eq_ae μ hX.aestronglyMeasurable]
  exact integral_mono hX hX.pos_part fun ω => le_max_left (X ω) 0

/-- From below, the mean, from a mean: if the class of learners is nonempty and every learner has an environment with
its windows in which the regret is integrable with mean at least `c`, the mean value is at least `c`. -/
theorem le_valMean_of_mean (hLne : (Learners K orc s0 n).Nonempty) (hne : K.Nonempty) {c : ℝ}
    (h : ∀ ℓ ∈ Learners K orc s0 n, ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (coin : Ω → ℕ → Bool)
      (loss : ℕ → Ω → E d → ℝ) (noise : ℕ → Ω → ℝ), NoisyAdv K n ℓ.D ℓ.D' μ coin loss noise ∧
        Integrable (fun ω => regretU ℓ.prog K n s0 (envWorld orc coin loss noise ω)) μ ∧
        c ≤ ∫ ω, regretU ℓ.prog K n s0 (envWorld orc coin loss noise ω) ∂μ) :
    c ≤ value (Learners K orc s0 n) K n s0 orc meanPosOf := by
  refine le_value subset_rfl hLne meanPosOf_range hne fun ℓ hℓ => ?_
  obtain ⟨Ω, _, μ, coin, loss, noise, hA, hint, hc⟩ := h ℓ hℓ
  exact ⟨_, ⟨Ω, inferInstance, μ, coin, loss, noise, hA, rfl⟩, hc.trans (integral_le_meanPosOf μ hint)⟩

end AdversarialBco.Minimax
