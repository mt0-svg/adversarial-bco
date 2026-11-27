/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.HpSgd

@[expose] public section

/-!
# UNI-SGD: projected subgradient descent with a τ-subgradient field, with high probability

Lemma HP-SGD (`AdversarialBco.Bit.hpSgd`, Bit/HpSgd.lean) with the exact subgradient inequality weakened to a
`τ`-subgradient field: `l(x; w) + ⟪V(x; w), x' - x⟫ ≤ l(x'; w) + τ` on the box (UNI-POS, part 1). The field enters
three times:

* the step (`hp_step_tau`): `l(x; w) - l(x°; w) ≤ ⟪Ṽ, x - x°⟫ + β Δ + τ`, one `τ` per step;
* Jensen at the average (`hp_jensen_tau`): one more `τ`;
* the range of the increments `Z_t = l(x°; y_t) - l(x_t; y_t)`: `|Z_t| ≤ G Δ + τ`, which widens the Hoeffding term.

So the bound of `hpSgdTau` is `Δ²/(2sN) + (s/2)(G + β)² + β Δ + (G Δ + τ)(2 log(1/δ)/N)^{1/2} + 2 τ`.

The rounding hypothesis `‖Ṽ - V‖ ≤ β` is asked along the iterates only (`hc`): the field `V` is needed on the whole
box (at the comparator `x°` and at the average), but the rounded field `Ṽ` that drives the iterates is compared with
it only where the procedure evaluates it. `V` need not be measurable.
-/

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

universe u

namespace AdversarialBco.UniPos

/-- One step with a `τ`-subgradient: `l(x; w) - l(x°; w) ≤ ⟪Ṽ, x - x°⟫ + β Δ + τ`. -/
theorem hp_step_tau {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (lx lo β Δ τ : ℝ)
    (x xo Vx Vtx : E) (ha : lx + ⟪Vx, xo - x⟫ ≤ lo + τ) (hc : ‖Vtx - Vx‖ ≤ β) (hd : ‖x - xo‖ ≤ Δ) :
    lx - lo ≤ ⟪Vtx, x - xo⟫ + β * Δ + τ := by
  have := AdversarialBco.Bit.hp_step lx (lo + τ) β Δ x xo Vx Vtx ha hc hd
  linarith

/-- Jensen for the average of `N` points of `BX` from a `τ`-subgradient field: the average lies in `BX` and the
objective there is at most the average of the objectives plus `τ`. -/
theorem hp_jensen_tau {E Y : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace Y]
    (ν : Measure Y) [IsProbabilityMeasure ν] (BX : Set E) (hconv : Convex ℝ BX) (l : E → Y → ℝ) (V : E → Y → E)
    (τ : ℝ) (ha : ∀ x ∈ BX, ∀ x' ∈ BX, ∀ w, l x w + ⟪V x w, x' - x⟫ ≤ l x' w + τ)
    (hlint : ∀ x ∈ BX, Integrable (l x) ν) (N : ℕ) (hN : 0 < N) (z : ℕ → E) (hz : ∀ t, z t ∈ BX) :
    (N : ℝ)⁻¹ • ∑ t ∈ Finset.range N, z t ∈ BX ∧
      ∫ w, l ((N : ℝ)⁻¹ • ∑ t ∈ Finset.range N, z t) w ∂ν ≤
        (N : ℝ)⁻¹ * ∑ t ∈ Finset.range N, ∫ w, l (z t) w ∂ν + τ := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  set zb := (N : ℝ)⁻¹ • ∑ t ∈ Finset.range N, z t with hzb
  have hmem : zb ∈ BX := by
    have := hconv.sum_mem (t := Finset.range N) (w := fun _ => (N : ℝ)⁻¹) (z := z)
      (fun _ _ => by positivity) (by simp [Finset.card_range]; field_simp) (fun t _ => hz t)
    simpa [hzb, Finset.smul_sum] using this
  refine ⟨hmem, ?_⟩
  have hpt : ∀ w, l zb w ≤ (N : ℝ)⁻¹ * ∑ t ∈ Finset.range N, l (z t) w + τ := by
    intro w
    have hsum : ∑ t ∈ Finset.range N, (l zb w + ⟪V zb w, z t - zb⟫) ≤
        ∑ t ∈ Finset.range N, (l (z t) w + τ) :=
      Finset.sum_le_sum fun t _ => ha zb hmem (z t) (hz t) w
    have hzero : ∑ t ∈ Finset.range N, ⟪V zb w, z t - zb⟫ = 0 := by
      rw [← inner_sum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, ← Nat.cast_smul_eq_nsmul ℝ, hzb,
        smul_smul, mul_inv_cancel₀ hN'.ne', one_smul, sub_self, inner_zero_right]
    rw [Finset.sum_add_distrib, hzero, Finset.sum_const, Finset.card_range, nsmul_eq_mul, add_zero,
      Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
    have h1 : (N : ℝ) * l zb w ≤ ∑ t ∈ Finset.range N, l (z t) w + N * τ := hsum
    have h2 : l zb w ≤ (N : ℝ)⁻¹ * (∑ t ∈ Finset.range N, l (z t) w + N * τ) := by
      rw [le_inv_mul_iff₀ hN']; exact h1
    calc l zb w ≤ (N : ℝ)⁻¹ * (∑ t ∈ Finset.range N, l (z t) w + N * τ) := h2
      _ = (N : ℝ)⁻¹ * ∑ t ∈ Finset.range N, l (z t) w + τ := by field_simp
  have hint : Integrable (fun w => (N : ℝ)⁻¹ * ∑ t ∈ Finset.range N, l (z t) w + τ) ν :=
    ((integrable_finsetSum _ fun t _ => hlint (z t) (hz t)).const_mul _).add (integrable_const τ)
  calc ∫ w, l zb w ∂ν ≤ ∫ w, ((N : ℝ)⁻¹ * ∑ t ∈ Finset.range N, l (z t) w + τ) ∂ν :=
        integral_mono (hlint zb hmem) hint hpt
    _ = (N : ℝ)⁻¹ * ∑ t ∈ Finset.range N, ∫ w, l (z t) w ∂ν + τ := by
        rw [integral_add ((integrable_finsetSum _ fun t _ => hlint (z t) (hz t)).const_mul _) (integrable_const τ),
          integral_const_mul, integral_finsetSum _ fun t _ => hlint (z t) (hz t), integral_const, probReal_univ,
          one_smul]

/-- The Azuma deviation at confidence `δ` for increments in `[-C, C]`. -/
theorem hp_eps_C (N C δ : ℝ) (hN : 0 < N) (hC : 0 < C) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    Real.exp (-2 * (C * Real.sqrt (2 * N * Real.log (1 / δ))) ^ 2 / (N * (C - -C) ^ 2)) = δ ∧
      C * Real.sqrt (2 * N * Real.log (1 / δ)) / N = C * Real.sqrt (2 * Real.log (1 / δ) / N) := by
  have h := AdversarialBco.Bit.hp_eps N C 1 δ hN hC one_pos hδ0 hδ1
  simpa only [mul_one] using h

/-- **UNI-SGD**, Lemma HP-SGD with a `τ`-subgradient field (UNI-POS, part 1).
Projected descent on a convex set `BX` of diameter at most `Δ`, with independent draws `y t` of law `ν`, a loss `l`
with a field `V` bounded by `G` on `BX` such that `l(x; w) + ⟪V(x; w), x' - x⟫ ≤ l(x'; w) + τ` for `x, x' ∈ BX` (a),
(b), and a rounded field `Vt` that drives the iterates and lies within `β` of `V` along the iterates (c). For every
`x°` in `BX` and `0 < δ < 1`, outside an event of probability at most `δ`, the average `x̄` of the first `N` iterates
has `φ(x̄) - φ(x°) ≤ Δ²/(2sN) + (s/2)(G + β)² + βΔ + (GΔ + τ)(2 log(1/δ)/N)^{1/2} + 2τ`, `φ(x) = E l(x; y)`. -/
theorem hpSgdTau {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E] {Y : Type*} [MeasurableSpace Y]
    {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure Y) (y : ℕ → Ω → Y) (hy : ∀ t, Measurable (y t)) (hind : iIndepFun y P)
    (hlaw : ∀ t, P.map (y t) = ν)
    (BX : Set E) (hconv : Convex ℝ BX) (Δ : ℝ) (hΔ : 0 < Δ) (hdiam : ∀ x ∈ BX, ∀ x' ∈ BX, ‖x - x'‖ ≤ Δ)
    (proj : E → E) (hprojm : Measurable proj) (hprojBX : ∀ z, proj z ∈ BX)
    (hproj : ∀ z, ∀ x ∈ BX, ‖proj z - x‖ ≤ ‖z - x‖)
    (l : E → Y → ℝ) (hl : Measurable (Function.uncurry l)) (V Vt : E → Y → E)
    (hVt : Measurable (Function.uncurry Vt)) (G β τ : ℝ) (hG : 0 < G) (hτ : 0 ≤ τ)
    (ha : ∀ x ∈ BX, ∀ x' ∈ BX, ∀ w, l x w + ⟪V x w, x' - x⟫ ≤ l x' w + τ)
    (hlint : ∀ x ∈ BX, Integrable (l x) ν) (hb : ∀ x ∈ BX, ∀ w, ‖V x w‖ ≤ G)
    (s : ℝ) (hs : 0 < s) (x : ℕ → Ω → E) (x0 : E) (hx0BX : x0 ∈ BX) (hx0 : ∀ ω, x 0 ω = x0)
    (hstep : ∀ t ω, x (t + 1) ω = proj (x t ω - s • Vt (x t ω) (y t ω)))
    (hc : ∀ t ω, ‖Vt (x t ω) (y t ω) - V (x t ω) (y t ω)‖ ≤ β)
    (N : ℕ) (hN : 0 < N) (xo : E) (hxo : xo ∈ BX) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    P {ω | Δ ^ 2 / (2 * s * N) + s / 2 * (G + β) ^ 2 + β * Δ +
        (G * Δ + τ) * Real.sqrt (2 * Real.log (1 / δ) / N) + 2 * τ <
        ∫ w, l ((N : ℝ)⁻¹ • ∑ t ∈ Finset.range N, x t ω) w ∂ν - ∫ w, l xo w ∂ν} ≤ ENNReal.ofReal δ := by
  classical
  have : IsProbabilityMeasure ν := by rw [← hlaw 0]; infer_instance
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
  -- the clamped increments, in `[-C, C]` with `C = G Δ + τ`
  set C := G * Δ + τ with hCdef
  have hGΔ : 0 < G * Δ := mul_pos hG hΔ
  have hCpos : 0 < C := by rw [hCdef]; linarith
  have hC0 : 0 ≤ C := hCpos.le
  let g : E × Y → ℝ := fun p => max (-C) (min C (l xo p.2 - l p.1 p.2))
  have hgm : Measurable g := by
    have h1 : Measurable fun p : E × Y => l xo p.2 := hl.comp (measurable_const.prodMk measurable_snd)
    have h2 : Measurable fun p : E × Y => l p.1 p.2 := hl
    exact measurable_const.max (measurable_const.min (h1.sub h2))
  have hgC : ∀ p, |g p| ≤ C := fun p =>
    abs_le.2 ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  have hgeq : ∀ u ∈ BX, ∀ w, g (u, w) = l xo w - l u w := by
    intro u hu w
    have h1 := ha u hu xo hxo w
    have h2 := ha xo hxo u hu w
    have i1 : |⟪V u w, xo - u⟫| ≤ G * Δ := (abs_real_inner_le_norm _ _).trans
      (mul_le_mul (hb u hu w) (hdiam xo hxo u hu) (norm_nonneg _) hG.le)
    have i2 : |⟪V xo w, u - xo⟫| ≤ G * Δ := (abs_real_inner_le_norm _ _).trans
      (mul_le_mul (hb xo hxo w) (hdiam u hu xo hxo) (norm_nonneg _) hG.le)
    have e1 : -C ≤ l xo w - l u w := by rw [hCdef]; linarith [(abs_le.1 i1).1]
    have e2 : l xo w - l u w ≤ C := by rw [hCdef]; linarith [(abs_le.1 i2).1]
    show max (-C) (min C (l xo w - l u w)) = l xo w - l u w
    rw [min_eq_right e2, max_eq_right e1]
  let Z : ℕ → Ω → ℝ := fun t ω => g (x t ω, y t ω)
  have hZm : ∀ t, StronglyMeasurable[F (t + 1)] (Z t) := fun t =>
    (hgm.comp (((hxF t).mono (F.mono (Nat.le_succ t)) le_rfl).prodMk (hyF t))).stronglyMeasurable
  have hZbd : ∀ t, ∀ᵐ ω ∂P, Z t ω ∈ Set.Icc ((fun _ => -C) t) ((fun _ => C) t) :=
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
      C hgC
    refine h.trans (Filter.Eventually.of_forall fun ω => ?_)
    show ∫ w, g (x t ω, w) ∂(P.map (y t)) = _
    rw [hlaw t, integral_congr_ae (Filter.Eventually.of_forall fun w => hgeq _ (hxBX t ω) w)]
    exact integral_sub (hlint xo hxo) (hlint _ (hxBX t ω))
  -- Azuma
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨heps1, heps2⟩ := hp_eps_C N C δ hN' hCpos hδ0 hδ1
  have hε0 : 0 ≤ C * Real.sqrt (2 * N * Real.log (1 / δ)) := by positivity
  have hAz := AdversarialBco.Poly.azumaHoeffding P F Z (fun _ => -C) (fun _ => C) hZm hZbd N _ hε0
  have hsumC : ∑ t ∈ Finset.range N, ((fun _ => C) t - (fun _ => -C) t) ^ 2 = N * (C - -C) ^ 2 := by
    simp [Finset.sum_const]
  rw [hsumC, heps1] at hAz
  refine le_trans (measure_mono_ae ?_) hAz
  have hce' : ∀ᵐ ω ∂P, ∀ t ∈ Finset.range N, P[Z t | F t] ω = ∫ w, l xo w ∂ν - ∫ w, l (x t ω) w ∂ν :=
    (Filter.eventually_all_finset _).2 fun t _ => hce t
  filter_upwards [hce'] with ω hω hbad
  by_contra hlt
  rw [not_le] at hlt
  have hZ : ∀ t, Z t ω = l xo (y t ω) - l (x t ω) (y t ω) := fun t => hgeq _ (hxBX t ω) _
  have hstepb : ∀ t, l (x t ω) (y t ω) - l xo (y t ω) ≤ ⟪Vt (x t ω) (y t ω), x t ω - xo⟫ + β * Δ + τ :=
    fun t => hp_step_tau _ _ β Δ τ (x t ω) xo (V (x t ω) (y t ω)) (Vt (x t ω) (y t ω))
      (ha _ (hxBX t ω) xo hxo _) (hc t ω) (hdiam _ (hxBX t ω) xo hxo)
  have hsgd := AdversarialBco.Poly.sgdPathwise E BX proj hproj xo hxo s Δ hs (fun t => x t ω)
    (fun t => Vt (x t ω) (y t ω)) (fun t => hstep t ω) (by rw [hx0]; exact hdiam x0 hx0BX xo hxo) N
  have hvb : ∀ t, ‖Vt (x t ω) (y t ω)‖ ^ 2 ≤ (G + β) ^ 2 := by
    intro t
    have h1 : ‖Vt (x t ω) (y t ω)‖ ≤ G + β := by
      calc ‖Vt (x t ω) (y t ω)‖ = ‖(Vt (x t ω) (y t ω) - V (x t ω) (y t ω)) + V (x t ω) (y t ω)‖ := by
            rw [sub_add_cancel]
        _ ≤ ‖Vt (x t ω) (y t ω) - V (x t ω) (y t ω)‖ + ‖V (x t ω) (y t ω)‖ := norm_add_le _ _
        _ ≤ β + G := add_le_add (hc t ω) (hb _ (hxBX t ω) _)
        _ = G + β := add_comm _ _
    exact pow_le_pow_left₀ (norm_nonneg _) h1 2
  have hsumv : ∑ t ∈ Finset.range N, ‖Vt (x t ω) (y t ω)‖ ^ 2 ≤ N * (G + β) ^ 2 := by
    calc _ ≤ ∑ t ∈ Finset.range N, (G + β) ^ 2 := Finset.sum_le_sum fun t _ => hvb t
      _ = N * (G + β) ^ 2 := by simp
  have hsumstep := Finset.sum_le_sum (s := Finset.range N) fun t _ => hstepb t
  obtain ⟨-, hjen⟩ := hp_jensen_tau ν BX hconv l V τ ha hlint N hN (fun t => x t ω) (fun t => hxBX t ω)
  have hsum1 : ∑ t ∈ Finset.range N, (Z t ω - (∫ w, l xo w ∂ν - ∫ w, l (x t ω) w ∂ν)) <
      C * Real.sqrt (2 * N * Real.log (1 / δ)) := by
    rwa [Finset.sum_congr rfl fun t ht => by rw [hω t ht]] at hlt
  have e1 : ∑ t ∈ Finset.range N, (Z t ω - (∫ w, l xo w ∂ν - ∫ w, l (x t ω) w ∂ν)) =
      ∑ t ∈ Finset.range N, (∫ w, l (x t ω) w ∂ν - ∫ w, l xo w ∂ν) -
        ∑ t ∈ Finset.range N, (l (x t ω) (y t ω) - l xo (y t ω)) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [hZ t]; ring
  have e2 : ∑ t ∈ Finset.range N, (⟪Vt (x t ω) (y t ω), x t ω - xo⟫ + β * Δ + τ) =
      ∑ t ∈ Finset.range N, ⟪Vt (x t ω) (y t ω), x t ω - xo⟫ + N * (β * Δ) + N * τ := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]; simp
  have e3 : s / 2 * ∑ t ∈ Finset.range N, ‖Vt (x t ω) (y t ω)‖ ^ 2 ≤ s / 2 * (N * (G + β) ^ 2) :=
    mul_le_mul_of_nonneg_left hsumv (by positivity)
  have key : ∑ t ∈ Finset.range N, (∫ w, l (x t ω) w ∂ν - ∫ w, l xo w ∂ν) <
      C * Real.sqrt (2 * N * Real.log (1 / δ)) + Δ ^ 2 / (2 * s) + s / 2 * (N * (G + β) ^ 2) +
        N * (β * Δ) + N * τ := by
    linarith
  have e4 : (N : ℝ)⁻¹ * ∑ t ∈ Finset.range N, ∫ w, l (x t ω) w ∂ν - ∫ w, l xo w ∂ν =
      (N : ℝ)⁻¹ * ∑ t ∈ Finset.range N, (∫ w, l (x t ω) w ∂ν - ∫ w, l xo w ∂ν) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    field_simp
  have hdiv := mul_lt_mul_of_pos_left key (inv_pos.2 hN')
  have hexp : (N : ℝ)⁻¹ * (C * Real.sqrt (2 * N * Real.log (1 / δ)) + Δ ^ 2 / (2 * s) +
      s / 2 * (N * (G + β) ^ 2) + N * (β * Δ) + N * τ) =
      Δ ^ 2 / (2 * s * N) + s / 2 * (G + β) ^ 2 + β * Δ + C * Real.sqrt (2 * Real.log (1 / δ) / N) + τ := by
    rw [← heps2]
    field_simp
    ring
  linarith

end AdversarialBco.UniPos
