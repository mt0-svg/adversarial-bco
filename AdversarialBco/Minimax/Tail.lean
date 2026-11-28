/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.StatementMinimax

@[expose] public section

/-!
# Quantiles and means read from a tail

The two payoffs of StatementMinimax.lean are functions of a tail `T : ℝ → ENNReal`, `T u = μ {Reg_n > u}`:
`quantileOf δ' T = inf {u | T u ≤ δ'}` and `meanPosOf T = ∫_0^∞ T u du`. For a regret in `[-N, N]` the tail is a
`TailOK N` (at most `1`, `0` from `N` on, `1` below `-N`). The bounds here use nothing else; no measurability.

* Upper bounds from the probability form: `T U ≤ δ'` gives `quantileOf δ' T ≤ U` (`quantileOf_le`), and `T u ≤ δ` for
  `u > U ≥ 0` gives `meanPosOf T ≤ U + N δ` (`meanPosOf_le`): the tail is at most `1` on `(0, U]`, at most `δ` on
  `(U, N)` and `0` from `N` on.
* Lower bounds from the probability form: `T u > δ'` for `u < L` gives `L ≤ quantileOf δ' T` (`le_quantileOf`), and
  `T u ≥ p` for `0 < u < L` gives `p L ≤ meanPosOf T` (`le_meanPosOf`).
* The ranges, so that no `sSup` or `sInf` of the values is a junk value: `quantileOf δ' T ∈ [-N, N]` for
  `δ' < 1` (`quantileOf_mem`) and `meanPosOf T ∈ [0, N]` (`meanPosOf_mem`).
-/

open MeasureTheory Set

namespace AdversarialBco.Minimax

/-- The tail of a function with values in `[-N, N]` on a probability space: at most `1`, `0` from `N` on, `1` below
`-N`. -/
structure TailOK (N : ℝ) (T : ℝ → ENNReal) : Prop where
  le_one : ∀ u, T u ≤ 1
  zero : ∀ u, N ≤ u → T u = 0
  one : ∀ u, u < -N → T u = 1

variable {N : ℝ} {T : ℝ → ENNReal}

/-! ## Quantiles -/

/-- The quantile from above: if `T U ≤ δ'` with `δ' < 1`, the `(1 - δ')`-quantile is at most `U`. -/
theorem quantileOf_le {δ' U : ℝ} (hT : TailOK N T) (hδ : δ' < 1) (h : T U ≤ ENNReal.ofReal δ') :
    quantileOf δ' T ≤ U := by
  refine csInf_le ⟨-N, fun u hu => ?_⟩ h
  by_contra hlt
  have h1 : T u = 1 := hT.one u (lt_of_not_ge hlt)
  have hu' : T u ≤ ENNReal.ofReal δ' := hu
  rw [h1] at hu'
  exact absurd hu' (not_le.2 (ENNReal.ofReal_lt_one.2 hδ))

/-- The quantile from below: if `T u > δ'` for every `u < L`, the `(1 - δ')`-quantile is at least `L`. -/
theorem le_quantileOf {δ' L : ℝ} (hT : TailOK N T) (h : ∀ u < L, ENNReal.ofReal δ' < T u) :
    L ≤ quantileOf δ' T := by
  refine le_csInf ⟨N, ?_⟩ fun u hu => not_lt.1 fun hlt => (not_le.2 (h u hlt)) hu
  show T N ≤ ENNReal.ofReal δ'
  rw [hT.zero N le_rfl]
  exact zero_le

/-- The `(1 - δ')`-quantile of a `TailOK N` lies in `[-N, N]` for `δ' < 1`. -/
theorem quantileOf_mem {δ' : ℝ} (hT : TailOK N T) (hδ1 : δ' < 1) :
    quantileOf δ' T ∈ Icc (-N) N := by
  refine ⟨le_quantileOf hT fun u hu => ?_, quantileOf_le hT hδ1 ?_⟩
  · rw [hT.one u hu]
    exact ENNReal.ofReal_lt_one.2 hδ1
  · rw [hT.zero N le_rfl]
    exact zero_le

/-! ## Means -/

/-- The integral of the tail on `(0, ∞)` is at most `U + δ N` when the tail is at most `δ` beyond `U`. -/
theorem lintegral_tail_le {U δ : ℝ} (hT : TailOK N T) (h : ∀ u, U < u → T u ≤ ENNReal.ofReal δ) :
    ∫⁻ u in Ioi (0 : ℝ), T u ≤ ENNReal.ofReal U + ENNReal.ofReal δ * ENNReal.ofReal N := by
  calc ∫⁻ u in Ioi (0 : ℝ), T u
      ≤ ∫⁻ u in Ioi (0 : ℝ), ((Iic U).indicator (fun _ => (1 : ENNReal)) u +
          (Iio N).indicator (fun _ => ENNReal.ofReal δ) u) := by
        refine lintegral_mono fun u => ?_
        by_cases hu : u ≤ U
        · rw [indicator_of_mem (mem_Iic.2 hu)]
          exact (hT.le_one u).trans le_self_add
        · by_cases hN : u < N
          · rw [indicator_of_mem (mem_Iio.2 hN)]
            exact (h u (lt_of_not_ge hu)).trans le_add_self
          · rw [hT.zero u (le_of_not_gt hN)]
            exact zero_le
    _ = (∫⁻ u in Ioi (0 : ℝ), (Iic U).indicator (fun _ => (1 : ENNReal)) u) +
          ∫⁻ u in Ioi (0 : ℝ), (Iio N).indicator (fun _ => ENNReal.ofReal δ) u :=
        lintegral_add_left (measurable_const.indicator measurableSet_Iic) _
    _ = ENNReal.ofReal U + ENNReal.ofReal δ * ENNReal.ofReal N := by
        rw [lintegral_indicator_const measurableSet_Iic, lintegral_indicator_const measurableSet_Iio,
          Measure.restrict_apply measurableSet_Iic, Measure.restrict_apply measurableSet_Iio,
          inter_comm (Iic U), inter_comm (Iio N), Ioi_inter_Iic, Ioi_inter_Iio, Real.volume_Ioc,
          Real.volume_Ioo, one_mul, sub_zero, sub_zero]

/-- The integral of a `TailOK N` on `(0, ∞)` is finite. -/
theorem lintegral_tail_ne_top (hT : TailOK N T) : ∫⁻ u in Ioi (0 : ℝ), T u ≠ ⊤ := by
  refine ne_top_of_le_ne_top ?_ (lintegral_tail_le (U := N) (δ := 0) hT fun u hu => ?_)
  · exact ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      ENNReal.ofReal_ne_top⟩
  · rw [hT.zero u hu.le]
    exact zero_le

/-- The mean from above, from the probability form: if the tail is at most `δ` beyond `U ≥ 0`, the mean of the
positive part is at most `U + N δ`. -/
theorem meanPosOf_le {U δ : ℝ} (hT : TailOK N T) (hN : 0 ≤ N) (hU : 0 ≤ U) (hδ : 0 ≤ δ)
    (h : ∀ u, U < u → T u ≤ ENNReal.ofReal δ) : meanPosOf T ≤ U + N * δ := by
  have hle := lintegral_tail_le hT h
  have hfin : ENNReal.ofReal U + ENNReal.ofReal δ * ENNReal.ofReal N ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top⟩
  calc meanPosOf T ≤ (ENNReal.ofReal U + ENNReal.ofReal δ * ENNReal.ofReal N).toReal :=
        ENNReal.toReal_mono hfin hle
    _ = U + N * δ := by
        rw [ENNReal.toReal_add ENNReal.ofReal_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
          ENNReal.ofReal_ne_top), ENNReal.toReal_mul, ENNReal.toReal_ofReal hU, ENNReal.toReal_ofReal hδ,
          ENNReal.toReal_ofReal hN, mul_comm δ]

/-- The mean from below, from the probability form: if the tail is at least `p` on `(0, L)`, the mean of the
positive part is at least `p L`. -/
theorem le_meanPosOf {L p : ℝ} (hT : TailOK N T) (hL : 0 ≤ L) (hp : 0 ≤ p)
    (h : ∀ u, 0 < u → u < L → ENNReal.ofReal p ≤ T u) : p * L ≤ meanPosOf T := by
  have hge : ENNReal.ofReal p * ENNReal.ofReal L ≤ ∫⁻ u in Ioi (0 : ℝ), T u := by
    calc ENNReal.ofReal p * ENNReal.ofReal L
        = ∫⁻ u in Ioi (0 : ℝ), (Iio L).indicator (fun _ => ENNReal.ofReal p) u := by
          rw [lintegral_indicator_const measurableSet_Iio, Measure.restrict_apply measurableSet_Iio,
            inter_comm (Iio L), Ioi_inter_Iio, Real.volume_Ioo, sub_zero]
      _ ≤ ∫⁻ u in Ioi (0 : ℝ), T u := by
          refine setLIntegral_mono' measurableSet_Ioi fun u hu => ?_
          by_cases huL : u < L
          · rw [indicator_of_mem (mem_Iio.2 huL)]
            exact h u hu huL
          · rw [indicator_of_notMem (fun h' => huL (mem_Iio.1 h'))]
            exact zero_le
  calc p * L = (ENNReal.ofReal p * ENNReal.ofReal L).toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hp, ENNReal.toReal_ofReal hL]
    _ ≤ meanPosOf T := ENNReal.toReal_mono (lintegral_tail_ne_top hT) hge

/-- The mean of the positive part read from a `TailOK N` lies in `[0, N]`. -/
theorem meanPosOf_mem (hT : TailOK N T) (hN : 0 ≤ N) : meanPosOf T ∈ Icc 0 N := by
  refine ⟨ENNReal.toReal_nonneg, ?_⟩
  have := meanPosOf_le (U := N) (δ := 0) hT hN hN le_rfl fun u hu => by
    rw [hT.zero u hu.le]
    exact zero_le
  simpa using this

end AdversarialBco.Minimax
