/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.UW.EvCRound
public import AdversarialBco.UW.EvPar
public import AdversarialBco.Poly.Df2EvAdYV

@[expose] public section

/-!
# Event (b) under the clip for the reference of Theorem UW

`evYPropUW_of : SIFactsUW → RowsUW → EvYPropUW`: on every instance of setting (E) at T4U, the sum of the squared
weighted observations up to the stopping time exceeds `s_Y = 21 n + y0² log(7/δc)` with probability at most `δc/7`.
The event is not conditioned on event (a): the clip bounds every term by `y0²`.

The proof is Theorem U's `EvAd.df2EvYPropAdV_of` (Poly/Df2EvAdYV.lean) with three changes.

* The increment is `Z_u = (Y^w_u)²` with `Y^w = obsW b0 y0 ξ Y` (`zYW`), at most `min(Y², y0²)` (`obsW_sq_le`), so
  Freedman's inequality (`EvGY.freedman_W`) runs at the range `B = y0²` and the level `δc/7`.
* Without event (a) the gauge factor `P = pip(X_u)` has no bound, so the conditional bound of a round
  (`EvGY.condExp_round_le`, which needs `|P| ≤ k`) is localised on the sets `{|P| ≤ N, |P - 1| ≤ N}`
  (`condExp_le_of_local`, `condExp_round_le_loc`): `E[min(Y², B) | 𝒢_u ∨ σ(ξ_u)] ≤ 4 P² + 8 (P - 1)²/ε²`.
* The state is the weighted epoch's (`sigE`, UW/EvCProc.lean); the sum `∑_{u ≤ τ} E (P_u - 1)² ≤ n ε²/4` is
  `vsum_le_quarterE` and the stopping time is that of `detBaseE` (UW/EvCRound.lean), so
  `∑_{u ≤ τ} W_u ≤ 8 n + (10/ε²) n ε²/4 = 21 n/2`.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped Matrix ENNReal

namespace AdversarialBco.UW

open AdversarialBco.Poly AdversarialBco.Poly.Layer2 AdversarialBco.Poly.EvGY

variable {d : ℕ}

/-! ## The clip -/

/-- `(Y^w)² ≤ min(Y², y0²)`. -/
theorem obsW_sq_le {y0 : ℝ} (hy0 : 0 ≤ y0) (b0 : ℝ) (ξ : Fin d → ℝ) (Y : ℝ) :
    obsW b0 y0 ξ Y ^ 2 ≤ min (Y ^ 2) (y0 ^ 2) := by
  obtain ⟨h1, h2, -, -⟩ := obsW_sure hy0 b0 ξ Y
  have h0 := abs_nonneg (obsW b0 y0 ξ Y)
  rw [← sq_abs (obsW b0 y0 ξ Y), ← sq_abs Y]
  exact le_min (pow_le_pow_left₀ h0 h2 2) (pow_le_pow_left₀ h0 h1 2)

/-! ## A conditional bound by localisation -/

/-- If `E[1_{S_N} X | H] ≤ 1_{S_N} G` for `H`-measurable sets `S_N` that cover `Ω`, then `E[X | H] ≤ G`. -/
theorem condExp_le_of_local {Ω : Type} (H : MeasurableSpace Ω) {m0 : MeasurableSpace Ω} (μ : Measure[m0] Ω)
    (X G : Ω → ℝ) (hX : Integrable X μ) (S : ℕ → Set Ω) (hS : ∀ N, MeasurableSet[H] (S N))
    (hcov : ∀ ω, ∃ N, ω ∈ S N) (hloc : ∀ N, μ[(S N).indicator X | H] ≤ᵐ[μ] (S N).indicator G) :
    μ[X | H] ≤ᵐ[μ] G := by
  have h2 : ∀ᵐ ω ∂μ, ∀ N, μ[(S N).indicator X | H] ω = (S N).indicator (μ[X | H]) ω ∧
      μ[(S N).indicator X | H] ω ≤ (S N).indicator G ω := by
    rw [ae_all_iff]
    intro N
    filter_upwards [condExp_indicator hX (hS N), hloc N] with ω h1 h2 using ⟨h1, h2⟩
  filter_upwards [h2] with ω hω
  obtain ⟨N, hN⟩ := hcov ω
  have h := (hω N).2
  rw [(hω N).1, Set.indicator_of_mem hN, Set.indicator_of_mem hN] at h
  exact h

/-- One round given `H` with no bound on `P`: `E[min(Y², B) | H] ≤ 4 P² + 8 (P - 1)²/ε²` for
`Y = P (a + e) + 2 (P - 1)/ε`, `P` and `a ∈ [0, 1]` measurable in `H`, `E[e | H] = 0`, `E[exp(e²) | H] ≤ 2`
(`EvGY.condExp_round_le` on `{|P| ≤ N, |P - 1| ≤ N}`, then `condExp_le_of_local`). -/
theorem condExp_round_le_loc {Ω : Type} (H : MeasurableSpace Ω) [m0 : MeasurableSpace Ω] (μ : Measure[m0] Ω)
    [IsProbabilityMeasure μ] (hH : H ≤ m0) (P a : Ω → ℝ) (hP : StronglyMeasurable[H] P)
    (ha : StronglyMeasurable[H] a) (ha01 : ∀ ω, a ω ∈ Set.Icc (0 : ℝ) 1) (ε B : ℝ) (hε : 0 < ε) (hB : 0 ≤ B)
    (e : Ω → ℝ) (he : Measurable[m0] e) (hint : Integrable (fun ω => Real.exp (e ω ^ 2)) μ)
    (hmean : μ[e | H] =ᵐ[μ] 0) (hexp : μ[fun ω => Real.exp (e ω ^ 2) | H] ≤ᵐ[μ] fun _ => 2) :
    μ[fun ω => min ((P ω * (a ω + e ω) + 2 * (P ω - 1) / ε) ^ 2) B | H] ≤ᵐ[μ]
      fun ω => 4 * P ω ^ 2 + 8 * (P ω - 1) ^ 2 / ε ^ 2 := by
  have hv : StronglyMeasurable[H] fun ω => P ω - 1 := hP.sub stronglyMeasurable_const
  set S : ℕ → Set Ω := fun N => {ω | |P ω| ≤ N ∧ |P ω - 1| ≤ N} with hSdef
  have hSm : ∀ N, MeasurableSet[H] (S N) := fun N =>
    (measurableSet_le (continuous_abs.measurable.comp hP.measurable) measurable_const).inter
      (measurableSet_le (continuous_abs.measurable.comp hv.measurable) measurable_const)
  have hPm : Measurable[m0] P := hP.measurable.mono hH le_rfl
  have ham : Measurable[m0] a := ha.measurable.mono hH le_rfl
  have hXm : Measurable[m0] fun ω => min ((P ω * (a ω + e ω) + 2 * (P ω - 1) / ε) ^ 2) B :=
    (((hPm.mul (ham.add he)).add (((hPm.sub_const 1).const_mul 2).div_const ε)).pow_const 2).min
      measurable_const
  have hX : Integrable (fun ω => min ((P ω * (a ω + e ω) + 2 * (P ω - 1) / ε) ^ 2) B) μ := by
    refine Integrable.of_bound hXm.aestronglyMeasurable B (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min (sq_nonneg _) hB)]
    exact min_le_right _ _
  refine condExp_le_of_local H μ _ _ hX S hSm (fun ω => ?_) (fun N => ?_)
  · obtain ⟨N, hN⟩ := exists_nat_ge (max |P ω| |P ω - 1|)
    exact ⟨N, (le_max_left _ _).trans hN, (le_max_right _ _).trans hN⟩
  · set J : Ω → ℝ := (S N).indicator fun _ => (1 : ℝ) with hJdef
    have hJ : StronglyMeasurable[H] J := stronglyMeasurable_const.indicator (hSm N)
    have hJmul : ∀ (f : Ω → ℝ) ω, J ω * f ω = (S N).indicator f ω := fun f ω => by
      by_cases h : ω ∈ S N
      · simp [hJdef, Set.indicator_of_mem h]
      · simp [hJdef, Set.indicator_of_notMem h]
    have hJ01 : ∀ ω, J ω = 0 ∨ J ω = 1 := fun ω => by
      by_cases h : ω ∈ S N
      · right; simp [hJdef, Set.indicator_of_mem h]
      · left; simp [hJdef, Set.indicator_of_notMem h]
    have hJP : ∀ ω, |J ω * P ω| ≤ N := fun ω => by
      rw [hJmul P ω]
      by_cases h : ω ∈ S N
      · rw [Set.indicator_of_mem h]; exact h.1
      · rw [Set.indicator_of_notMem h, abs_zero]; exact Nat.cast_nonneg N
    have hJv : ∀ ω, |J ω * (P ω - 1)| ≤ N := fun ω => by
      have h1 : J ω * (P ω - 1) = (S N).indicator (fun ω => P ω - 1) ω := hJmul (fun ω => P ω - 1) ω
      rw [h1]
      by_cases h : ω ∈ S N
      · rw [Set.indicator_of_mem h]; exact h.2
      · rw [Set.indicator_of_notMem h, abs_zero]; exact Nat.cast_nonneg N
    have h := condExp_round_le H μ hH J P a (fun ω => P ω - 1) hJ hJ01 hP ha ha01 hv (N : ℝ) hJP hJv ε B hε hB e
      he hint hmean hexp
    have e1 : (fun ω => J ω * min ((P ω * (a ω + e ω) + 2 * (P ω - 1) / ε) ^ 2) B) =
        (S N).indicator fun ω => min ((P ω * (a ω + e ω) + 2 * (P ω - 1) / ε) ^ 2) B :=
      funext fun ω => hJmul (fun ω => min ((P ω * (a ω + e ω) + 2 * (P ω - 1) / ε) ^ 2) B) ω
    have e2 : (fun ω => J ω * (4 * P ω ^ 2 + 8 * (P ω - 1) ^ 2 / ε ^ 2)) =
        (S N).indicator fun ω => 4 * P ω ^ 2 + 8 * (P ω - 1) ^ 2 / ε ^ 2 :=
      funext fun ω => hJmul (fun ω => 4 * P ω ^ 2 + 8 * (P ω - 1) ^ 2 / ε ^ 2) ω
    rw [e1, e2] at h
    exact h

/-! ## The functions of a round at a frozen point -/

section Frozen

variable (p : Df2OPar) (y0 : ℝ) {Θ : Type} (Kθ : Θ → Set (E d)) (gθ : ℕ → Θ → E d → ℝ)

/-- `pip(X)` at a frozen point `(q, st, z)`. -/
noncomputable def pYW (x : Θ × Df2St d × (Fin d → ℝ)) : ℝ :=
  df2Pip p (Kθ x.1) (WithLp.toLp 2 (xOfE p x.2.1 x.2.2))

/-- The loss at the play, at a frozen point, read through the extension. -/
noncomputable def aYW (u : ℕ) (x : Θ × Df2St d × (Fin d → ℝ)) : ℝ :=
  (df2Ext p (Kθ x.1) (gθ u x.1) (WithLp.toLp 2 (xOfE p x.2.1 x.2.2)) - 2 * (pYW p Kθ x - 1) / p.eps) /
    pYW p Kθ x

/-- The bound of the conditional mean of a round at `((q, st), z)`: `min(y0², 8 + (10/ε²) (pip - 1)²)`. -/
noncomputable def fYW (y : (Θ × Df2St d) × (Fin d → ℝ)) : ℝ :=
  min (y0 ^ 2) (8 + 10 / p.eps ^ 2 * (pYW p Kθ (y.1.1, y.1.2, y.2) - 1) ^ 2)

theorem one_le_pYW (x : Θ × Df2St d × (Fin d → ℝ)) : 1 ≤ pYW p Kθ x := le_max_left _ _

theorem aYW_eq (u : ℕ) (x : Θ × Df2St d × (Fin d → ℝ)) :
    aYW p Kθ gθ u x = gθ u x.1 ((pYW p Kθ x)⁻¹ • (WithLp.toLp 2 (xOfE p x.2.1 x.2.2) : E d)) := by
  have hP : pYW p Kθ x ≠ 0 := by have := one_le_pYW p Kθ x; positivity
  unfold aYW
  rw [show df2Ext p (Kθ x.1) (gθ u x.1) (WithLp.toLp 2 (xOfE p x.2.1 x.2.2)) =
      pYW p Kθ x * gθ u x.1 ((pYW p Kθ x)⁻¹ • (WithLp.toLp 2 (xOfE p x.2.1 x.2.2) : E d)) +
        2 * (pYW p Kθ x - 1) / p.eps from rfl]
  rw [add_sub_cancel_right, mul_div_cancel_left₀ _ hP]

/-- The unweighted value of a round is `P (a + e) + 2 (P - 1)/ε` at the frozen point. -/
theorem yOfE_eq (u : ℕ) (x : Θ × Df2St d × (Fin d → ℝ)) (e : ℝ) :
    yOfE p Kθ gθ u x.1 x.2.1 x.2.2 e = pYW p Kθ x * (aYW p Kθ gθ u x + e) + 2 * (pYW p Kθ x - 1) / p.eps := by
  have hP : pYW p Kθ x ≠ 0 := by have := one_le_pYW p Kθ x; positivity
  have h1 : yOfE p Kθ gθ u x.1 x.2.1 x.2.2 e =
      df2Ext p (Kθ x.1) (gθ u x.1) (WithLp.toLp 2 (xOfE p x.2.1 x.2.2)) + pYW p Kθ x * e := rfl
  have h2 : pYW p Kθ x * aYW p Kθ gθ u x =
      df2Ext p (Kθ x.1) (gθ u x.1) (WithLp.toLp 2 (xOfE p x.2.1 x.2.2)) - 2 * (pYW p Kθ x - 1) / p.eps := by
    unfold aYW
    rw [← mul_div_assoc, mul_div_cancel_left₀ _ hP]
  rw [h1, mul_add, h2]
  ring

theorem fYW_nonneg (y : (Θ × Df2St d) × (Fin d → ℝ)) : 0 ≤ fYW p y0 Kθ y :=
  le_min (sq_nonneg _) (by positivity)

theorem fYW_le (y : (Θ × Df2St d) × (Fin d → ℝ)) : fYW p y0 Kθ y ≤ y0 ^ 2 := min_le_left _ _

variable {p Kθ gθ}

theorem measurable_pYW [MeasurableSpace Θ] (hg : Measurable fun x : Θ × E d => gauge (Kθ x.1) x.2) :
    Measurable (pYW p Kθ) := by
  have hX : Measurable fun x : Θ × Df2St d × (Fin d → ℝ) => (x.1, (WithLp.toLp 2 (xOfE p x.2.1 x.2.2) : E d)) :=
    measurable_fst.prodMk ((WithLp.measurable_toLp 2 _).comp ((measurable_xOfE p).comp
      ((measurable_fst.comp measurable_snd).prodMk (measurable_snd.comp measurable_snd))))
  have h : Measurable fun x : Θ × Df2St d × (Fin d → ℝ) =>
      gauge (Kθ x.1) (WithLp.toLp 2 (xOfE p x.2.1 x.2.2)) := hg.comp hX
  unfold pYW df2Pip
  exact measurable_const.max (h.div_const _)

theorem measurable_aYW [MeasurableSpace Θ] {V : Type} [MeasurableSpace V] {n m : ℕ} {apθ : V → ApFun d}
    (hmeas : Df2EpochMeasV p n m Kθ gθ apθ) {u : ℕ} (hu : u < m) : Measurable (aYW p Kθ gθ u) := by
  have hX : Measurable fun x : Θ × Df2St d × (Fin d → ℝ) => (x.1, (WithLp.toLp 2 (xOfE p x.2.1 x.2.2) : E d)) :=
    measurable_fst.prodMk ((WithLp.measurable_toLp 2 _).comp ((measurable_xOfE p).comp
      ((measurable_fst.comp measurable_snd).prodMk (measurable_snd.comp measurable_snd))))
  have hext : Measurable fun x : Θ × Df2St d × (Fin d → ℝ) =>
      df2Ext p (Kθ x.1) (gθ u x.1) (WithLp.toLp 2 (xOfE p x.2.1 x.2.2)) := by
    have h := (hmeas.2.1 u hu).comp hX
    exact h
  have hp := measurable_pYW (p := p) hmeas.1
  have h := (hext.sub (((hp.sub_const 1).const_mul 2).div_const p.eps)).div hp
  exact h

theorem measurable_fYW [MeasurableSpace Θ] (hg : Measurable fun x : Θ × E d => gauge (Kθ x.1) x.2) :
    Measurable (fYW p y0 Kθ) := by
  have hr : Measurable fun y : (Θ × Df2St d) × (Fin d → ℝ) => ((y.1.1, y.1.2, y.2) : Θ × Df2St d × (Fin d → ℝ)) :=
    (measurable_fst.comp measurable_fst).prodMk ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
  have hp := (measurable_pYW (p := p) hg).comp hr
  unfold fYW
  exact measurable_const.min (measurable_const.add (measurable_const.mul ((hp.sub_const 1).pow_const 2)))

/-- The integral of the bound of a round against the law of the draw. -/
theorem integral_fYW_le [MeasurableSpace Θ] (hg : Measurable fun x : Θ × E d => gauge (Kθ x.1) x.2)
    (hε0 : 0 < p.eps) (hε1 : p.eps < 1) (q : Θ) (hK : Convex ℝ (Kθ q)) (hKc : IsClosed (Kθ q))
    (hball : Metric.closedBall 0 1 ⊆ Kθ q) (st : Df2St d) :
    ∫ z, fYW p y0 Kθ ((q, st), z) ∂(Measure.pi fun _ : Fin d => gaussianReal 0 1) ≤
      8 + 10 / p.eps ^ 2 * ∫ z, (pYW p Kθ (q, st, z) - 1) ^ 2 ∂(Measure.pi fun _ : Fin d => gaussianReal 0 1) := by
  have hv : Integrable (fun z => (pYW p Kθ (q, st, z) - 1) ^ 2) (Measure.pi fun _ : Fin d => gaussianReal 0 1) :=
    integrable_vsq_pi (Kθ q) hK hKc hball _ hε0.le hε1 st.mu st.A p.lam
  have hmz : Measurable fun z : Fin d → ℝ => (((q, st), z) : (Θ × Df2St d) × (Fin d → ℝ)) :=
    measurable_const.prodMk measurable_id
  have hFm : Measurable fun z => fYW p y0 Kθ ((q, st), z) := (measurable_fYW y0 hg).comp hmz
  have hFi : Integrable (fun z => fYW p y0 Kθ ((q, st), z)) (Measure.pi fun _ : Fin d => gaussianReal 0 1) := by
    refine Integrable.of_bound hFm.aestronglyMeasurable (y0 ^ 2) (ae_of_all _ fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (fYW_nonneg p y0 Kθ _)]
    exact fYW_le p y0 Kθ _
  have hle : ∀ z, fYW p y0 Kθ ((q, st), z) ≤ 8 + 10 / p.eps ^ 2 * (pYW p Kθ (q, st, z) - 1) ^ 2 :=
    fun z => min_le_right _ _
  calc _ ≤ ∫ z, (8 + 10 / p.eps ^ 2 * (pYW p Kθ (q, st, z) - 1) ^ 2)
          ∂(Measure.pi fun _ : Fin d => gaussianReal 0 1) :=
        integral_mono hFi ((integrable_const _).add (hv.const_mul _)) hle
    _ = _ := by
      rw [integral_add (integrable_const _) (hv.const_mul _), integral_const, integral_const_mul]
      simp only [probReal_univ, one_smul]

end Frozen

/-! ## The process on `Ω` -/

section Proc

variable (p : Df2OPar) (n : ℕ) (b0 y0 : ℝ) {Θ : Type} {V : Type} (Kθ : Θ → Set (E d)) (gθ : ℕ → Θ → E d → ℝ)
  (apθ : V → ApFun d) {Ω : Type} (θ : ℕ → Ω → Θ) (ψ : ℕ → Ω → V) (ξ : ℕ → Ω → Fin d → ℝ) (e : ℕ → Ω → ℝ)
  (m : ℕ)

/-- The state of the weighted epoch before round `u`. -/
noncomputable def stYW (u : ℕ) (ω : Ω) : Df2St d := (sigE p n b0 y0 Kθ gθ apθ θ ψ ξ e u ω).2

/-- `Z_u = (Y^w_u)²` for `u < m`, `0` after the horizon. -/
noncomputable def zYW (u : ℕ) (ω : Ω) : ℝ :=
  if u < m then obsW b0 y0 (ξ u ω) (yOfE p Kθ gθ u (θ u ω) (stYW p n b0 y0 Kθ gθ apθ θ ψ ξ e u ω) (ξ u ω) (e u ω)) ^ 2
  else 0

/-- `W_u = 8 + (10/ε²) E_z (pip(μ_u + (1 - λ) A_u z) - 1)²` on the weighted epoch. -/
noncomputable def wYW (u : ℕ) (ω : Ω) : ℝ :=
  8 + 10 / p.eps ^ 2 *
    vmom (ctxP p n Kθ apθ θ ψ ω) (pathW (ctxP p n Kθ apθ θ ψ ω) b0 y0 (pathP gθ θ ξ e ω)) u

theorem zYW_nonneg (u : ℕ) (ω : Ω) : 0 ≤ zYW p n b0 y0 Kθ gθ apθ θ ψ ξ e m u ω := by
  unfold zYW
  split_ifs
  · exact sq_nonneg _
  · exact le_rfl

theorem zYW_le (hy0 : 0 ≤ y0) (u : ℕ) (ω : Ω) : zYW p n b0 y0 Kθ gθ apθ θ ψ ξ e m u ω ≤ y0 ^ 2 := by
  unfold zYW
  split_ifs
  · exact (obsW_sq_le hy0 b0 _ _).trans (min_le_right _ _)
  · exact sq_nonneg _

theorem measurable_zYW [MeasurableSpace Θ] [MeasurableSpace V] [m0 : MeasurableSpace Ω]
    (hmeas : Df2EpochMeasV p n m Kθ gθ apθ) (𝒢 : Filtration ℕ m0) (hK : ∀ s ω, Kθ (θ s ω) = Kθ (θ 0 ω))
    (hθ : ∀ s, Measurable[𝒢 s] (θ s)) (hψ : ∀ s, Measurable[𝒢 (s + 1)] (ψ s))
    (hξ : ∀ s, Measurable[𝒢 (s + 1)] (ξ s)) (he : ∀ s, Measurable[𝒢 (s + 1)] (e s)) (u : ℕ) :
    StronglyMeasurable[𝒢 (u + 1)] (zYW p n b0 y0 Kθ gθ apθ θ ψ ξ e m u) := by
  by_cases hu : u < m
  · have hfun : zYW p n b0 y0 Kθ gθ apθ θ ψ ξ e m u = fun ω =>
        obsW b0 y0 (ξ u ω) (yOfE p Kθ gθ u (θ u ω) (stYW p n b0 y0 Kθ gθ apθ θ ψ ξ e u ω) (ξ u ω) (e u ω)) ^ 2 :=
      funext fun ω => by simp only [zYW, hu, ite_true]
    rw [hfun]
    have hst : Measurable[𝒢 (u + 1)] (stYW p n b0 y0 Kθ gθ apθ θ ψ ξ e u) := by
      have h := (measurable_snd.comp (measurable_sigE p n b0 y0 Kθ gθ apθ θ ψ ξ e hmeas 𝒢 hK hθ hψ hξ he
        hu.le)).mono (𝒢.mono (Nat.le_succ u)) le_rfl
      exact h
    have hθ' : Measurable[𝒢 (u + 1)] (θ u) := (hθ u).mono (𝒢.mono (Nat.le_succ u)) le_rfl
    have hin : Measurable[𝒢 (u + 1)] fun ω =>
        (θ u ω, stYW p n b0 y0 Kθ gθ apθ θ ψ ξ e u ω, ξ u ω, e u ω) :=
      hθ'.prodMk (hst.prodMk ((hξ u).prodMk (he u)))
    have hY : Measurable[𝒢 (u + 1)] fun ω =>
        yOfE p Kθ gθ u (θ u ω) (stYW p n b0 y0 Kθ gθ apθ θ ψ ξ e u ω) (ξ u ω) (e u ω) := by
      have h := (measurable_yOfE hmeas hu).comp hin
      exact h
    have hO : Measurable[𝒢 (u + 1)] fun ω =>
        obsW b0 y0 (ξ u ω) (yOfE p Kθ gθ u (θ u ω) (stYW p n b0 y0 Kθ gθ apθ θ ψ ξ e u ω) (ξ u ω) (e u ω)) := by
      have h := (measurable_obsW_uncurry (d := d) b0 y0).comp ((hξ u).prodMk hY)
      exact h
    exact (hO.pow_const 2).stronglyMeasurable
  · have hfun : zYW p n b0 y0 Kθ gθ apθ θ ψ ξ e m u = fun _ => 0 :=
      funext fun ω => by simp only [zYW, hu, ite_false]
    rw [hfun]
    exact stronglyMeasurable_const

end Proc

/-! ## One round -/

/-- One round: `E[Z_u | 𝒢_u] ≤ W_u` almost surely, for any record `p` with `0 < ε ≤ 1/2`. -/
theorem condExp_zYW_le {p : Df2OPar} {n m : ℕ} {b0 y0 : ℝ} {Θ V : Type} [MeasurableSpace Θ] [MeasurableSpace V]
    {Kθ : Θ → Set (E d)} {gθ : ℕ → Θ → E d → ℝ} {apθ : V → ApFun d} (hε0 : 0 < p.eps) (hε : p.eps ≤ 1 / 2)
    (hy0 : 0 ≤ y0) (hbody : ∀ q, Df2Body d p.R (Kθ q)) (hadm : ∀ q, ∀ s < m, AdmLoss (Kθ q) (gθ s q))
    (hmeas : Df2EpochMeasV p n m Kθ gθ apθ) {Ω : Type} [m0 : MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (𝒢 : Filtration ℕ m0) (θ : ℕ → Ω → Θ) (ψ : ℕ → Ω → V)
    (hK : ∀ s ω, Kθ (θ s ω) = Kθ (θ 0 ω)) (ξ : ℕ → Ω → Fin d → ℝ) (e : ℕ → Ω → ℝ)
    (hθ : ∀ s, Measurable[𝒢 s] (θ s)) (hψ : ∀ s, Measurable[𝒢 (s + 1)] (ψ s)) (hE : Df2SetE d μ 𝒢 ξ e) (u : ℕ) :
    μ[zYW p n b0 y0 Kθ gθ apθ θ ψ ξ e m u | 𝒢 u] ≤ᵐ[μ] wYW p n b0 y0 Kθ gθ apθ θ ψ ξ e u := by
  have hε1 : p.eps < 1 := by linarith
  by_cases hu : u < m
  swap
  · have hfun : zYW p n b0 y0 Kθ gθ apθ θ ψ ξ e m u = 0 :=
      funext fun ω => by simp only [zYW, hu, ite_false, Pi.zero_apply]
    rw [hfun, condExp_zero]
    refine ae_of_all _ fun ω => ?_
    have := vmom_nonneg (ctxP p n Kθ apθ θ ψ ω) (pathW (ctxP p n Kθ apθ θ ψ ω) b0 y0 (pathP gθ θ ξ e ω)) u
    show (0 : ℝ) ≤ 8 + 10 / p.eps ^ 2 *
      vmom (ctxP p n Kθ apθ θ ψ ω) (pathW (ctxP p n Kθ apθ θ ψ ω) b0 y0 (pathP gθ θ ξ e ω)) u
    positivity
  have hξm : Measurable[m0] (ξ u) := (hE.xi_meas u).mono (𝒢.le _) le_rfl
  have hH : hOf 𝒢 ξ u ≤ m0 := sup_le (𝒢.le u) hξm.comap_le
  have hst : Measurable[𝒢 u] (stYW p n b0 y0 Kθ gθ apθ θ ψ ξ e u) :=
    measurable_snd.comp
      (measurable_sigE p n b0 y0 Kθ gθ apθ θ ψ ξ e hmeas 𝒢 hK hθ hψ hE.xi_meas hE.e_meas hu.le)
  have hθu : Measurable[𝒢 u] (θ u) := hθ u
  have hx : Measurable[𝒢 u] fun ω => (θ u ω, stYW p n b0 y0 Kθ gθ apθ θ ψ ξ e u ω) := hθu.prodMk hst
  set xu : Ω → Θ × Df2St d × (Fin d → ℝ) := fun ω => (θ u ω, stYW p n b0 y0 Kθ gθ apθ θ ψ ξ e u ω, ξ u ω)
    with hxu
  have hxH : Measurable[hOf 𝒢 ξ u] xu :=
    (hθu.mono le_sup_left le_rfl).prodMk ((hst.mono le_sup_left le_rfl).prodMk
      ((comap_measurable (ξ u)).mono le_sup_right le_rfl))
  have hPm : StronglyMeasurable[hOf 𝒢 ξ u] fun ω => pYW p Kθ (xu ω) :=
    ((measurable_pYW hmeas.1).comp hxH).stronglyMeasurable
  have ham : StronglyMeasurable[hOf 𝒢 ξ u] fun ω => aYW p Kθ gθ u (xu ω) :=
    ((measurable_aYW hmeas hu).comp hxH).stronglyMeasurable
  have ha01 : ∀ ω, aYW p Kθ gθ u (xu ω) ∈ Set.Icc (0 : ℝ) 1 := by
    intro ω
    obtain ⟨hKc, hKcl, hball, -, -⟩ := hbody (θ u ω)
    rw [aYW_eq]
    exact (hadm (θ u ω) u hu).2 _ (play_mem (Kθ (θ u ω)) hKc hKcl hball _ hε0 hε1 _)
  have he : Measurable[m0] (e u) := (hE.e_meas u).mono (𝒢.le _) le_rfl
  have h1 := condExp_round_le_loc (hOf 𝒢 ξ u) μ hH (fun ω => pYW p Kθ (xu ω)) (fun ω => aYW p Kθ gθ u (xu ω))
    hPm ham ha01 p.eps (y0 ^ 2) hε0 (sq_nonneg _) (e u) he (hE.e_int u) (hE.e_mean u) (hE.e_exp u)
  have hZint : Integrable (zYW p n b0 y0 Kθ gθ apθ θ ψ ξ e m u) μ := by
    refine Integrable.of_bound ((measurable_zYW p n b0 y0 Kθ gθ apθ θ ψ ξ e m hmeas 𝒢 hK hθ hψ hE.xi_meas
      hE.e_meas u).mono (𝒢.le _)).aestronglyMeasurable (y0 ^ 2) (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (zYW_nonneg p n b0 y0 Kθ gθ apθ θ ψ ξ e m u ω)]
    exact zYW_le p n b0 y0 Kθ gθ apθ θ ψ ξ e m hy0 u ω
  have hPm0 : Measurable[m0] fun ω => pYW p Kθ (xu ω) := hPm.measurable.mono hH le_rfl
  have ham0 : Measurable[m0] fun ω => aYW p Kθ gθ u (xu ω) := ham.measurable.mono hH le_rfl
  have hmin_int : Integrable (fun ω => min ((pYW p Kθ (xu ω) * (aYW p Kθ gθ u (xu ω) + e u ω) +
      2 * (pYW p Kθ (xu ω) - 1) / p.eps) ^ 2) (y0 ^ 2)) μ := by
    refine Integrable.of_bound ((((hPm0.mul (ham0.add he)).add
      (((hPm0.sub_const 1).const_mul 2).div_const _)).pow_const 2).min measurable_const).aestronglyMeasurable
      (y0 ^ 2) (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min (sq_nonneg _) (sq_nonneg _))]
    exact min_le_right _ _
  have hZle : ∀ ω, zYW p n b0 y0 Kθ gθ apθ θ ψ ξ e m u ω ≤ min ((pYW p Kθ (xu ω) *
      (aYW p Kθ gθ u (xu ω) + e u ω) + 2 * (pYW p Kθ (xu ω) - 1) / p.eps) ^ 2) (y0 ^ 2) := by
    intro ω
    simp only [zYW, hu, ite_true]
    rw [show yOfE p Kθ gθ u (θ u ω) (stYW p n b0 y0 Kθ gθ apθ θ ψ ξ e u ω) (ξ u ω) (e u ω) =
      pYW p Kθ (xu ω) * (aYW p Kθ gθ u (xu ω) + e u ω) + 2 * (pYW p Kθ (xu ω) - 1) / p.eps from
        yOfE_eq p Kθ gθ u (xu ω) (e u ω)]
    exact obsW_sq_le hy0 b0 (ξ u ω) _
  have hYF1 : μ[zYW p n b0 y0 Kθ gθ apθ θ ψ ξ e m u | hOf 𝒢 ξ u] ≤ᵐ[μ]
      fun ω => 8 + 10 / p.eps ^ 2 * (pYW p Kθ (xu ω) - 1) ^ 2 :=
    (condExp_mono hZint hmin_int (ae_of_all _ hZle)).trans
      (h1.trans (ae_of_all _ fun ω => round_arith _ _ hε0 hε))
  have hYF2 : μ[zYW p n b0 y0 Kθ gθ apθ θ ψ ξ e m u | hOf 𝒢 ξ u] ≤ᵐ[μ] fun _ => y0 ^ 2 := by
    have h := condExp_mono (m := hOf 𝒢 ξ u) hZint (integrable_const (y0 ^ 2))
      (ae_of_all _ (zYW_le p n b0 y0 Kθ gθ apθ θ ψ ξ e m hy0 u))
    rwa [condExp_const hH] at h
  have hYF : μ[zYW p n b0 y0 Kθ gθ apθ θ ψ ξ e m u | hOf 𝒢 ξ u] ≤ᵐ[μ]
      fun ω => fYW p y0 Kθ ((θ u ω, stYW p n b0 y0 Kθ gθ apθ θ ψ ξ e u ω), ξ u ω) := by
    filter_upwards [hYF1, hYF2] with ω h1 h2
    exact le_min h2 h1
  have h3 := condExp_le_freeze lemmaFR (𝒢 u) (hOf 𝒢 ξ u) μ le_sup_left hH
    (fun ω => (θ u ω, stYW p n b0 y0 Kθ gθ apθ θ ψ ξ e u ω)) (ξ u) hx hξm (hE.xi_indep u) _ hZint (fYW p y0 Kθ)
    (measurable_fYW y0 hmeas.1) _ (fYW_nonneg p y0 Kθ) (fYW_le p y0 Kθ) hYF
  rw [hE.xi_law u] at h3
  refine h3.trans (ae_of_all _ fun ω => ?_)
  obtain ⟨hKc, hKcl, hball, -, -⟩ := hbody (θ u ω)
  refine (integral_fYW_le y0 hmeas.1 hε0 hε1 (θ u ω) hKc hKcl hball _).trans (le_of_eq ?_)
  simp only [wYW, vmom, pYW, hK u ω]
  rfl

/-! ## The budget -/

/-- **Event (b) under the clip** fails with probability at most `δc/7` on every instance of setting (E) at T4U. -/
theorem evYPropUW_of (hS : SIFactsUW) (hR : RowsUW) : EvYPropUW := by
  intro d n m ρ hreg hm1 hmn Θ _ V _ Kθ gθ apθ hbody hadm hap hmeas Ω m0 μ hμ 𝒢 θ ψ ξ e hθ hψ hK hE
  show μ {ω | ¬ EvYW (ctxP (parW d n ρ.u) n Kθ apθ θ ψ ω)
      (pathW (ctxP (parW d n ρ.u) n Kθ apθ θ ψ ω) ρ.b0 ρ.y0 (pathP gθ θ ξ e ω)) (sYW n ρ.y0 ρ.δc) m} ≤
    ENNReal.ofReal (1 / 7 * ρ.δc)
  have hε0 := EvP.eps_pos hreg
  have hε : (parW d n ρ.u).eps ≤ 1 / 2 := by linarith [hreg.heps]
  have hy0 := EvP.y0_pos hreg
  have hB : 0 < ρ.y0 ^ 2 := by positivity
  have hdc := hreg.dc_pos
  have hdc7 : 0 < ρ.δc / 7 := by positivity
  have hF := freedman_W μ 𝒢 (zYW (parW d n ρ.u) n ρ.b0 ρ.y0 Kθ gθ apθ θ ψ ξ e m)
    (wYW (parW d n ρ.u) n ρ.b0 ρ.y0 Kθ gθ apθ θ ψ ξ e) (ρ.y0 ^ 2) hB
    (measurable_zYW (parW d n ρ.u) n ρ.b0 ρ.y0 Kθ gθ apθ θ ψ ξ e m hmeas 𝒢 hK hθ hψ hE.xi_meas hE.e_meas)
    (zYW_nonneg (parW d n ρ.u) n ρ.b0 ρ.y0 Kθ gθ apθ θ ψ ξ e m)
    (zYW_le (parW d n ρ.u) n ρ.b0 ρ.y0 Kθ gθ apθ θ ψ ξ e m hy0.le)
    (condExp_zYW_le hε0 hε hy0.le hbody hadm hmeas μ 𝒢 θ ψ hK ξ e hθ hψ hE) m (ρ.δc / 7) hdc7
  refine le_trans (measure_mono ?_) (hF.trans (le_of_eq (congrArg ENNReal.ofReal (by ring))))
  intro ω hω
  set c := ctxP (parW d n ρ.u) n Kθ apθ θ ψ ω with hc
  set πw := pathW c ρ.b0 ρ.y0 (pathP gθ θ ξ e ω) with hπw
  have H : DetBase c (1 / 2) πw m := detBaseE hS hR hreg hm1 hmn hbody hadm hap ψ hK ξ e ω
  have hτm : c.tau πw m < m := H.tau_lt
  refine ⟨c.tau πw m + 1, hτm, ?_⟩
  have hZ : ∑ u ∈ Finset.range (c.tau πw m + 1), zYW (parW d n ρ.u) n ρ.b0 ρ.y0 Kθ gθ apθ θ ψ ξ e m u ω =
      ∑ u ∈ Finset.range (c.tau πw m + 1), c.Y πw u ^ 2 := by
    refine Finset.sum_congr rfl fun u hu => ?_
    have hut : u ≤ c.tau πw m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hu)
    have hrun := (H.stInv_le_tau u hut).run
    rw [Y_sigE (parW d n ρ.u) n ρ.b0 ρ.y0 Kθ gθ apθ θ ψ ξ e hK ω u _ hrun]
    simp only [zYW, lt_of_le_of_lt hut hτm, ite_true]
    rfl
  have hW : ∑ u ∈ Finset.range (c.tau πw m + 1), wYW (parW d n ρ.u) n ρ.b0 ρ.y0 Kθ gθ apθ θ ψ ξ e u ω =
      ((c.tau πw m + 1 : ℕ) : ℝ) * 8 + 10 / (parW d n ρ.u).eps ^ 2 *
        ∑ u ∈ Finset.range (c.tau πw m + 1), vmom c πw u := by
    unfold wYW
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← Finset.mul_sum]
    try rfl
  have hτn : (((c.tau πw m + 1 : ℕ)) : ℝ) ≤ n := by exact_mod_cast (Nat.succ_le_of_lt hτm).trans hmn
  have hV := vsum_le_quarterE H (c.tau πw m) le_rfl
  have hεne : (parW d n ρ.u).eps ^ 2 ≠ 0 := by positivity
  have hWb : 10 / (parW d n ρ.u).eps ^ 2 * ∑ u ∈ Finset.range (c.tau πw m + 1), vmom c πw u ≤ 10 / 4 * n := by
    calc _ ≤ 10 / (parW d n ρ.u).eps ^ 2 * (1 / 4 * n * (parW d n ρ.u).eps ^ 2) :=
          mul_le_mul_of_nonneg_left hV (by positivity)
      _ = 10 / 4 * n := by field_simp
  have hY' : sYW n ρ.y0 ρ.δc < ∑ u ∈ Finset.range (c.tau πw m + 1), c.Y πw u ^ 2 := lt_of_not_ge hω
  have hlog : Real.log (1 / (ρ.δc / 7)) = Real.log (7 / ρ.δc) := by rw [one_div_div]
  rw [hZ, hW, hlog]
  unfold sYW at hY'
  linarith

end AdversarialBco.UW
