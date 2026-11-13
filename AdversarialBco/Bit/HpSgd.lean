/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.PgLemmasProof
public import AdversarialBco.Poly.Df2AzumaProof

@[expose] public section

/-!
# The descent lemma: projected subgradient descent with high probability

The descent lemma, the coupled part of the position theorem.

* `hp_condExp_freeze`: if `U` is `m`-measurable and `W` is independent of `m`, the conditional expectation of a bounded
  `g (U, W)` given `m` is `∫ g (U, w)` against the law of `W`.
* `hp_eps`: the Azuma deviation `ε = G Δ (2 N log(1/δ))^{1/2}` has `exp(-2 ε²/(N (2 G Δ)²)) = δ`.
* `hp_step`: one step, `l(x; y) - l(x°; y) ≤ ⟨Ṽ, x - x°⟩ + β Δ`.
* `hp_jensen`: the average of points of `BX` lies in `BX` and `φ` at the average is at most the average of `φ`.
* `hpSgd`: the lemma. The filtration is that of the first `t` draws; the increments
  `Z_t = l(x°; y_t) - l(x_t; y_t)` lie in `[-G Δ, G Δ]` and have conditional expectation `φ(x°) - φ(x_t)`
  (`hp_condExp_freeze`); `azumaHoeffding` (Poly/Df2Azuma.lean), `sgdPathwise` (Poly/PgLemmas.lean) and `hp_jensen`
  conclude.
-/


open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

universe u

/-- Freezing: if `U` is `m`-measurable and `W` is independent of `m`, the conditional expectation of a bounded
`g (U, W)` given `m` is `∫ g (U, w)` against the law of `W`. -/
theorem AdversarialBco.Bit.hp_condExp_freeze {Ω E Y : Type*} (m : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] [MeasurableSpace E] [MeasurableSpace Y] (hm : m ≤ mΩ)
    (U : Ω → E) (hU : Measurable[m] U) (W : Ω → Y) (hW : Measurable W)
    (hind : Indep m (MeasurableSpace.comap W inferInstance) P) (g : E × Y → ℝ) (hg : Measurable g) (C : ℝ)
    (hgC : ∀ p, |g p| ≤ C) :
    P[fun ω => g (U ω, W ω) | m] =ᵐ[P] fun ω => ∫ w, g (U ω, w) ∂(P.map W) := by
  have hU' : Measurable U := hU.mono hm le_rfl
  have hint : Integrable (fun ω => g (U ω, W ω)) P :=
    Integrable.of_bound (hg.comp (hU'.prodMk hW)).aestronglyMeasurable C
      (Filter.Eventually.of_forall fun ω => by simpa [Real.norm_eq_abs] using hgC (U ω, W ω))
  set ν := P.map W with hν
  set h : E → ℝ := fun u => ∫ w, g (u, w) ∂ν with hh
  have hhm : Measurable h := (hg.stronglyMeasurable.integral_prod_right' (ν := ν)).measurable
  have hhC : ∀ u, |h u| ≤ C := by
    intro u
    have := norm_integral_le_of_norm_le_const (μ := ν) (f := fun w => g (u, w)) (C := C)
      (Filter.Eventually.of_forall fun w => by simpa [Real.norm_eq_abs] using hgC (u, w))
    simpa [Real.norm_eq_abs] using this
  symm
  refine ae_eq_condExp_of_forall_setIntegral_eq hm hint ?_ ?_ ?_
  · intro s hs _
    exact (Integrable.of_bound ((hhm.comp hU').aestronglyMeasurable) C
      (Filter.Eventually.of_forall fun ω => by simpa [Real.norm_eq_abs] using hhC (U ω))).integrableOn
  · intro s hs _
    have hs' : MeasurableSet s := hm s hs
    -- the pair `V = (U, 1_s)` is `m`-measurable, hence independent of `W`
    set V : Ω → E × ℝ := fun ω => (U ω, s.indicator (fun _ => (1 : ℝ)) ω) with hV
    have hVm : Measurable[m] V :=
      hU.prodMk ((measurable_const.indicator hs))
    have hV' : Measurable V := hVm.mono hm le_rfl
    have hVW : IndepFun V W P := by
      rw [IndepFun_iff_Indep]
      exact indep_of_indep_of_le_left hind hVm.comap_le
    have hmap := (indepFun_iff_map_prod_eq_prod_map_map hV'.aemeasurable hW.aemeasurable).1 hVW
    set k : (E × ℝ) × Y → ℝ := fun p => if p.1.2 = 1 then g (p.1.1, p.2) else 0 with hk
    have hkm : Measurable k := by
      refine Measurable.ite ?_ (hg.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
        measurable_const
      exact (measurableSet_singleton (1 : ℝ)).preimage (measurable_snd.comp measurable_fst)
    have hkC : ∀ p, ‖k p‖ ≤ C := by
      intro p
      simp only [hk]
      split_ifs
      · simpa [Real.norm_eq_abs] using hgC _
      · simpa using (abs_nonneg _).trans (hgC (p.1.1, p.2))
    have hkint : Integrable k ((P.map V).prod ν) :=
      Integrable.of_bound hkm.aestronglyMeasurable C (Filter.Eventually.of_forall hkC)
    have hk1 : ∀ ω, k (V ω, W ω) = s.indicator (fun ω => g (U ω, W ω)) ω := by
      intro ω
      by_cases hω : ω ∈ s <;> simp [hk, hV, hω]
    have hk2 : ∀ ω, ∫ w, k (V ω, w) ∂ν = s.indicator (fun ω => h (U ω)) ω := by
      intro ω
      by_cases hω : ω ∈ s <;> simp [hk, hV, hω, hh]
    have e1 : ∫ ω in s, g (U ω, W ω) ∂P = ∫ ω, k (V ω, W ω) ∂P := by
      rw [← integral_indicator hs']
      exact integral_congr_ae (Filter.Eventually.of_forall fun ω => (hk1 ω).symm)
    have e2 : ∫ ω in s, h (U ω) ∂P = ∫ ω, ∫ w, k (V ω, w) ∂ν ∂P := by
      rw [← integral_indicator hs']
      exact integral_congr_ae (Filter.Eventually.of_forall fun ω => (hk2 ω).symm)
    rw [e1, e2]
    have f1 : ∫ ω, k (V ω, W ω) ∂P = ∫ p, k p ∂((P.map V).prod ν) := by
      rw [← hmap, integral_map (hV'.prodMk hW).aemeasurable hkm.aestronglyMeasurable]
    have f2 : ∫ ω, ∫ w, k (V ω, w) ∂ν ∂P = ∫ v, ∫ w, k (v, w) ∂ν ∂(P.map V) := by
      rw [integral_map hV'.aemeasurable]
      exact (hkm.stronglyMeasurable.integral_prod_right' (ν := ν)).aestronglyMeasurable
    rw [f1, f2, integral_prod _ hkint]
  · exact ((hhm.comp hU).stronglyMeasurable).aestronglyMeasurable

/-- The Azuma deviation at confidence `δ`: `exp(-2 ε²/(N (2 G Δ)²)) = δ` and `ε/N = G Δ (2 log(1/δ)/N)^{1/2}` at
`ε = G Δ (2 N log(1/δ))^{1/2}`. -/
theorem AdversarialBco.Bit.hp_eps (N G Δ δ : ℝ) (hN : 0 < N) (hG : 0 < G) (hΔ : 0 < Δ) (hδ0 : 0 < δ)
    (hδ1 : δ < 1) :
    Real.exp (-2 * (G * Δ * Real.sqrt (2 * N * Real.log (1 / δ))) ^ 2 / (N * (G * Δ - -(G * Δ)) ^ 2)) = δ ∧
      G * Δ * Real.sqrt (2 * N * Real.log (1 / δ)) / N = G * Δ * Real.sqrt (2 * Real.log (1 / δ) / N) := by
  have hl : 0 < Real.log (1 / δ) := Real.log_pos (one_lt_one_div hδ0 hδ1)
  constructor
  · rw [mul_pow, Real.sq_sqrt (by positivity)]
    have : -2 * ((G * Δ) ^ 2 * (2 * N * Real.log (1 / δ))) / (N * (G * Δ - -(G * Δ)) ^ 2) =
        -Real.log (1 / δ) := by
      field_simp
      ring
    rw [this, Real.exp_neg, Real.exp_log (by positivity)]
    simp
  · rw [mul_div_assoc]
    congr 1
    rw [show 2 * Real.log (1 / δ) / N = (2 * N * Real.log (1 / δ)) / N ^ 2 by field_simp,
      Real.sqrt_div' _ (by positivity), Real.sqrt_sq hN.le]

/-- One step of the descent: by the subgradient inequality at `x` against `x°` and the rounding of the subgradient,
`l(x; w) - l(x°; w) ≤ ⟨Ṽ, x - x°⟩ + β Δ`. -/
theorem AdversarialBco.Bit.hp_step {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (lx lo β Δ : ℝ)
    (x xo Vx Vtx : E) (ha : lx + ⟪Vx, xo - x⟫ ≤ lo) (hc : ‖Vtx - Vx‖ ≤ β) (hd : ‖x - xo‖ ≤ Δ) :
    lx - lo ≤ ⟪Vtx, x - xo⟫ + β * Δ := by
  have h1 : ⟪Vx, xo - x⟫ = -⟪Vx, x - xo⟫ := by
    rw [← inner_neg_right, neg_sub]
  have h2 : ⟪Vx, x - xo⟫ = ⟪Vtx, x - xo⟫ - ⟪Vtx - Vx, x - xo⟫ := by
    rw [inner_sub_left]; ring
  have h3 : ⟪Vtx - Vx, x - xo⟫ ≥ -(β * Δ) := by
    have := abs_real_inner_le_norm (Vtx - Vx) (x - xo)
    have h4 : ‖Vtx - Vx‖ * ‖x - xo‖ ≤ β * Δ :=
      mul_le_mul hc hd (norm_nonneg _) ((norm_nonneg _).trans hc)
    linarith [neg_abs_le ⟪Vtx - Vx, x - xo⟫]
  linarith

/-- Jensen for the average of `N` points of `BX`, from the subgradient inequality. -/
theorem AdversarialBco.Bit.hp_jensen {E Y : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace Y]
    (ν : Measure Y) (BX : Set E) (hconv : Convex ℝ BX) (l : E → Y → ℝ) (V : E → Y → E)
    (ha : ∀ x ∈ BX, ∀ x' ∈ BX, ∀ w, l x w + ⟪V x w, x' - x⟫ ≤ l x' w) (hlint : ∀ x ∈ BX, Integrable (l x) ν)
    (N : ℕ) (hN : 0 < N) (z : ℕ → E) (hz : ∀ t, z t ∈ BX) :
    (N : ℝ)⁻¹ • ∑ t ∈ Finset.range N, z t ∈ BX ∧
      ∫ w, l ((N : ℝ)⁻¹ • ∑ t ∈ Finset.range N, z t) w ∂ν ≤
        (N : ℝ)⁻¹ * ∑ t ∈ Finset.range N, ∫ w, l (z t) w ∂ν := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  set zb := (N : ℝ)⁻¹ • ∑ t ∈ Finset.range N, z t with hzb
  have hmem : zb ∈ BX := by
    have := hconv.sum_mem (t := Finset.range N) (w := fun _ => (N : ℝ)⁻¹) (z := z)
      (fun _ _ => by positivity) (by simp [Finset.card_range]; field_simp) (fun t _ => hz t)
    simpa [hzb, Finset.smul_sum] using this
  refine ⟨hmem, ?_⟩
  have hpt : ∀ w, l zb w ≤ (N : ℝ)⁻¹ * ∑ t ∈ Finset.range N, l (z t) w := by
    intro w
    have hsum : ∑ t ∈ Finset.range N, (l zb w + ⟪V zb w, z t - zb⟫) ≤ ∑ t ∈ Finset.range N, l (z t) w :=
      Finset.sum_le_sum fun t _ => ha zb hmem (z t) (hz t) w
    have hzero : ∑ t ∈ Finset.range N, ⟪V zb w, z t - zb⟫ = 0 := by
      rw [← inner_sum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, ← Nat.cast_smul_eq_nsmul ℝ, hzb,
        smul_smul, mul_inv_cancel₀ hN'.ne', one_smul, sub_self, inner_zero_right]
    rw [Finset.sum_add_distrib, hzero, Finset.sum_const, Finset.card_range, nsmul_eq_mul, add_zero] at hsum
    rw [le_inv_mul_iff₀ hN']
    linarith
  calc ∫ w, l zb w ∂ν ≤ ∫ w, (N : ℝ)⁻¹ * ∑ t ∈ Finset.range N, l (z t) w ∂ν :=
        integral_mono (hlint zb hmem) ((integrable_finsetSum _ fun t _ => hlint (z t) (hz t)).const_mul _) hpt
    _ = (N : ℝ)⁻¹ * ∑ t ∈ Finset.range N, ∫ w, l (z t) w ∂ν := by
        rw [integral_const_mul, integral_finsetSum _ fun t _ => hlint (z t) (hz t)]

/-- **The descent lemma**. Projected subgradient descent on a convex set `BX` of diameter
at most `Δ`, with independent draws `y t` of law `ν`, a loss `l` with subgradient `V` bounded by `G` (a), (b), and a
rounded subgradient `Vt` within `β` of `V` (c). For every `x°` in `BX` and `0 < δ < 1`, outside an event of
probability at most `δ`, the average `x̄` of the first `N` iterates has
`φ(x̄) - φ(x°) ≤ Δ²/(2sN) + (s/2)(G + β)² + βΔ + GΔ (2 log(1/δ)/N)^{1/2}`, `φ(x) = E l(x; y)`. -/
theorem AdversarialBco.Bit.hpSgd {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E] {Y : Type*} [MeasurableSpace Y]
    {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure Y) (y : ℕ → Ω → Y) (hy : ∀ t, Measurable (y t)) (hind : iIndepFun y P)
    (hlaw : ∀ t, P.map (y t) = ν)
    (BX : Set E) (hconv : Convex ℝ BX) (Δ : ℝ) (hΔ : 0 < Δ) (hdiam : ∀ x ∈ BX, ∀ x' ∈ BX, ‖x - x'‖ ≤ Δ)
    (proj : E → E) (hprojm : Measurable proj) (hprojBX : ∀ z, proj z ∈ BX)
    (hproj : ∀ z, ∀ x ∈ BX, ‖proj z - x‖ ≤ ‖z - x‖)
    (l : E → Y → ℝ) (hl : Measurable (Function.uncurry l)) (V Vt : E → Y → E)
    (hVt : Measurable (Function.uncurry Vt)) (G β : ℝ) (hG : 0 < G)
    (ha : ∀ x ∈ BX, ∀ x' ∈ BX, ∀ w, l x w + ⟪V x w, x' - x⟫ ≤ l x' w) (hlint : ∀ x ∈ BX, Integrable (l x) ν)
    (hb : ∀ x ∈ BX, ∀ w, ‖V x w‖ ≤ G) (hc : ∀ x ∈ BX, ∀ w, ‖Vt x w - V x w‖ ≤ β)
    (s : ℝ) (hs : 0 < s) (x : ℕ → Ω → E) (x0 : E) (hx0BX : x0 ∈ BX) (hx0 : ∀ ω, x 0 ω = x0)
    (hstep : ∀ t ω, x (t + 1) ω = proj (x t ω - s • Vt (x t ω) (y t ω)))
    (N : ℕ) (hN : 0 < N) (xo : E) (hxo : xo ∈ BX) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    P {ω | Δ ^ 2 / (2 * s * N) + s / 2 * (G + β) ^ 2 + β * Δ + G * Δ * Real.sqrt (2 * Real.log (1 / δ) / N) <
        ∫ w, l ((N : ℝ)⁻¹ • ∑ t ∈ Finset.range N, x t ω) w ∂ν - ∫ w, l xo w ∂ν} ≤ ENNReal.ofReal δ := by
  classical
  have hxBX : ∀ t ω, x t ω ∈ BX := by
    intro t ω
    cases t with
    | zero => rw [hx0]; exact hx0BX
    | succ t => rw [hstep]; exact hprojBX _
  -- the filtration of the first `t` draws
  let F : Filtration ℕ mΩ :=
    { seq := fun t => ⨆ j ∈ Set.Iio t, MeasurableSpace.comap (y j) inferInstance
      mono' := fun i j hij => biSup_mono fun k hk => lt_of_lt_of_le hk hij
      le' := fun t => iSup₂_le fun j _ => (hy j).comap_le }
  have hyF : ∀ t, Measurable[F (t + 1)] (y t) := by
    intro t
    refine Measurable.of_comap_le ?_
    exact le_iSup₂ (f := fun j (_ : j ∈ Set.Iio (t + 1)) => MeasurableSpace.comap (y j) inferInstance) t
      (by simp)
  have hxF : ∀ t, Measurable[F t] (x t) := by
    intro t
    induction t with
    | zero =>
      have : x 0 = fun _ => x0 := funext hx0
      rw [this]; exact measurable_const
    | succ t ih =>
      have h1 : Measurable[F (t + 1)] (x t) := ih.mono (F.mono (Nat.le_succ t)) le_rfl
      have h2 : Measurable[F (t + 1)] (fun ω => (x t ω, y t ω)) := h1.prodMk (hyF t)
      have hφ : Measurable (fun p : E × Y => proj (p.1 - s • Vt p.1 p.2)) :=
        hprojm.comp (measurable_fst.sub (hVt.const_smul s))
      have : x (t + 1) = (fun p : E × Y => proj (p.1 - s • Vt p.1 p.2)) ∘ (fun ω => (x t ω, y t ω)) :=
        funext (hstep t)
      rw [this]; exact hφ.comp h2
  -- the clamped increments
  have hC0 : 0 ≤ G * Δ := by positivity
  let g : E × Y → ℝ := fun p => max (-(G * Δ)) (min (G * Δ) (l xo p.2 - l p.1 p.2))
  have hgm : Measurable g := by
    have h1 : Measurable fun p : E × Y => l xo p.2 := hl.comp (measurable_const.prodMk measurable_snd)
    have h2 : Measurable fun p : E × Y => l p.1 p.2 := hl
    exact measurable_const.max (measurable_const.min (h1.sub h2))
  have hgC : ∀ p, |g p| ≤ G * Δ := fun p =>
    abs_le.2 ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  have hgeq : ∀ u ∈ BX, ∀ w, g (u, w) = l xo w - l u w := by
    intro u hu w
    have h1 := ha u hu xo hxo w
    have h2 := ha xo hxo u hu w
    have i1 : |⟪V u w, xo - u⟫| ≤ G * Δ := (abs_real_inner_le_norm _ _).trans
      (mul_le_mul (hb u hu w) (hdiam xo hxo u hu) (norm_nonneg _) hG.le)
    have i2 : |⟪V xo w, u - xo⟫| ≤ G * Δ := (abs_real_inner_le_norm _ _).trans
      (mul_le_mul (hb xo hxo w) (hdiam u hu xo hxo) (norm_nonneg _) hG.le)
    have e1 : -(G * Δ) ≤ l xo w - l u w := by linarith [(abs_le.1 i1).1]
    have e2 : l xo w - l u w ≤ G * Δ := by linarith [(abs_le.1 i2).1]
    show max (-(G * Δ)) (min (G * Δ) (l xo w - l u w)) = l xo w - l u w
    rw [min_eq_right e2, max_eq_right e1]
  let Z : ℕ → Ω → ℝ := fun t ω => g (x t ω, y t ω)
  have hZm : ∀ t, StronglyMeasurable[F (t + 1)] (Z t) := fun t =>
    (hgm.comp (((hxF t).mono (F.mono (Nat.le_succ t)) le_rfl).prodMk (hyF t))).stronglyMeasurable
  have hZbd : ∀ t, ∀ᵐ ω ∂P, Z t ω ∈ Set.Icc ((fun _ => -(G * Δ)) t) ((fun _ => G * Δ) t) :=
    fun t => Filter.Eventually.of_forall fun ω => abs_le.1 (hgC _)
  -- independence of the next draw from the past
  have hindep : ∀ t, Indep (F t) (MeasurableSpace.comap (y t) inferInstance) P := by
    intro t
    have hi := (iIndepFun_iff_iIndep (fun _ => inferInstance) y P).1 hind
    have h := indep_iSup_of_disjoint (fun j => (hy j).comap_le) hi (S := Set.Iio t) (T := {t}) (by simp)
    exact indep_of_indep_of_le_right h
      (le_iSup₂ (f := fun j (_ : j ∈ ({t} : Set ℕ)) => MeasurableSpace.comap (y j) inferInstance) t rfl)
  -- the conditional expectation of the increments
  have hce : ∀ t, P[Z t | F t] =ᵐ[P] fun ω => ∫ w, l xo w ∂ν - ∫ w, l (x t ω) w ∂ν := by
    intro t
    have h := AdversarialBco.Bit.hp_condExp_freeze (F t) (F.le t) (x t) (hxF t) (y t) (hy t) (hindep t) g hgm
      (G * Δ) hgC
    refine h.trans (Filter.Eventually.of_forall fun ω => ?_)
    show ∫ w, g (x t ω, w) ∂(P.map (y t)) = _
    rw [hlaw t, integral_congr_ae (Filter.Eventually.of_forall fun w => hgeq _ (hxBX t ω) w)]
    exact integral_sub (hlint xo hxo) (hlint _ (hxBX t ω))
  -- Azuma
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨heps1, heps2⟩ := AdversarialBco.Bit.hp_eps N G Δ δ hN' hG hΔ hδ0 hδ1
  have hε0 : 0 ≤ G * Δ * Real.sqrt (2 * N * Real.log (1 / δ)) := by positivity
  have hAz := AdversarialBco.Poly.azumaHoeffding P F Z (fun _ => -(G * Δ)) (fun _ => G * Δ) hZm hZbd N _ hε0
  have hsumC : ∑ t ∈ Finset.range N, ((fun _ => G * Δ) t - (fun _ => -(G * Δ)) t) ^ 2 =
      N * (G * Δ - -(G * Δ)) ^ 2 := by
    simp [Finset.sum_const]
  rw [hsumC, heps1] at hAz
  refine le_trans (measure_mono_ae ?_) hAz
  have hce' : ∀ᵐ ω ∂P, ∀ t ∈ Finset.range N, P[Z t | F t] ω = ∫ w, l xo w ∂ν - ∫ w, l (x t ω) w ∂ν :=
    (Filter.eventually_all_finset _).2 fun t _ => hce t
  filter_upwards [hce'] with ω hω hbad
  by_contra hlt
  rw [not_le] at hlt
  have hZ : ∀ t, Z t ω = l xo (y t ω) - l (x t ω) (y t ω) := fun t => hgeq _ (hxBX t ω) _
  have hstepb : ∀ t, l (x t ω) (y t ω) - l xo (y t ω) ≤ ⟪Vt (x t ω) (y t ω), x t ω - xo⟫ + β * Δ := fun t =>
    AdversarialBco.Bit.hp_step _ _ β Δ (x t ω) xo (V (x t ω) (y t ω)) (Vt (x t ω) (y t ω))
      (ha _ (hxBX t ω) xo hxo _) (hc _ (hxBX t ω) _) (hdiam _ (hxBX t ω) xo hxo)
  have hsgd := AdversarialBco.Poly.sgdPathwise E BX proj hproj xo hxo s Δ hs (fun t => x t ω)
    (fun t => Vt (x t ω) (y t ω)) (fun t => hstep t ω) (by rw [hx0]; exact hdiam x0 hx0BX xo hxo) N
  have hvb : ∀ t, ‖Vt (x t ω) (y t ω)‖ ^ 2 ≤ (G + β) ^ 2 := by
    intro t
    have h1 : ‖Vt (x t ω) (y t ω)‖ ≤ G + β := by
      calc ‖Vt (x t ω) (y t ω)‖ = ‖(Vt (x t ω) (y t ω) - V (x t ω) (y t ω)) + V (x t ω) (y t ω)‖ := by
            rw [sub_add_cancel]
        _ ≤ ‖Vt (x t ω) (y t ω) - V (x t ω) (y t ω)‖ + ‖V (x t ω) (y t ω)‖ := norm_add_le _ _
        _ ≤ β + G := add_le_add (hc _ (hxBX t ω) _) (hb _ (hxBX t ω) _)
        _ = G + β := add_comm _ _
    exact pow_le_pow_left₀ (norm_nonneg _) h1 2
  have hsumv : ∑ t ∈ Finset.range N, ‖Vt (x t ω) (y t ω)‖ ^ 2 ≤ N * (G + β) ^ 2 := by
    calc _ ≤ ∑ t ∈ Finset.range N, (G + β) ^ 2 := Finset.sum_le_sum fun t _ => hvb t
      _ = N * (G + β) ^ 2 := by simp
  have hsumstep := Finset.sum_le_sum (s := Finset.range N) fun t _ => hstepb t
  obtain ⟨-, hjen⟩ := AdversarialBco.Bit.hp_jensen ν BX hconv l V ha hlint N hN (fun t => x t ω)
    (fun t => hxBX t ω)
  have hsum1 : ∑ t ∈ Finset.range N, (Z t ω - (∫ w, l xo w ∂ν - ∫ w, l (x t ω) w ∂ν)) <
      G * Δ * Real.sqrt (2 * N * Real.log (1 / δ)) := by
    rwa [Finset.sum_congr rfl fun t ht => by rw [hω t ht]] at hlt
  have e1 : ∑ t ∈ Finset.range N, (Z t ω - (∫ w, l xo w ∂ν - ∫ w, l (x t ω) w ∂ν)) =
      ∑ t ∈ Finset.range N, (∫ w, l (x t ω) w ∂ν - ∫ w, l xo w ∂ν) -
        ∑ t ∈ Finset.range N, (l (x t ω) (y t ω) - l xo (y t ω)) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [hZ t]; ring
  have e2 : ∑ t ∈ Finset.range N, (⟪Vt (x t ω) (y t ω), x t ω - xo⟫ + β * Δ) =
      ∑ t ∈ Finset.range N, ⟪Vt (x t ω) (y t ω), x t ω - xo⟫ + N * (β * Δ) := by
    rw [Finset.sum_add_distrib]; simp
  have e3 : s / 2 * ∑ t ∈ Finset.range N, ‖Vt (x t ω) (y t ω)‖ ^ 2 ≤ s / 2 * (N * (G + β) ^ 2) :=
    mul_le_mul_of_nonneg_left hsumv (by positivity)
  have key : ∑ t ∈ Finset.range N, (∫ w, l (x t ω) w ∂ν - ∫ w, l xo w ∂ν) <
      G * Δ * Real.sqrt (2 * N * Real.log (1 / δ)) + Δ ^ 2 / (2 * s) + s / 2 * (N * (G + β) ^ 2) +
        N * (β * Δ) := by
    linarith
  have e4 : (N : ℝ)⁻¹ * ∑ t ∈ Finset.range N, ∫ w, l (x t ω) w ∂ν - ∫ w, l xo w ∂ν =
      (N : ℝ)⁻¹ * ∑ t ∈ Finset.range N, (∫ w, l (x t ω) w ∂ν - ∫ w, l xo w ∂ν) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    field_simp
  have hdiv := mul_lt_mul_of_pos_left key (inv_pos.2 hN')
  have hexp : (N : ℝ)⁻¹ * (G * Δ * Real.sqrt (2 * N * Real.log (1 / δ)) + Δ ^ 2 / (2 * s) +
      s / 2 * (N * (G + β) ^ 2) + N * (β * Δ)) =
      Δ ^ 2 / (2 * s * N) + s / 2 * (G + β) ^ 2 + β * Δ + G * Δ * Real.sqrt (2 * Real.log (1 / δ) / N) := by
    rw [← heps2]
    field_simp
    ring
  linarith
