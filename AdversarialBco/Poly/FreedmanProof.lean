/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.Freedman

@[expose] public section

/-!
# Freedman's inequality at a stopping time: proofs

Proofs of the interface statements of `AdversarialBco/Poly/Freedman.lean`: the exponential supermartingale and the
unnormalised bound, the dyadic truncation and union of Zimmert and Lattimore (2022, Theorem 9) for the one-sided
bound, the stopped and two-sided form at level `δ/2` per side, and Lemma FK by rescaling; then one assembly per
`Prop`.
-/

open MeasureTheory ProbabilityTheory

namespace AdversarialBco.Poly

universe u

/-! ## Leaves -/

theorem exp_le_one_add_add_sq (x : ℝ) (hx : x ≤ 1) : Real.exp x ≤ 1 + x + x ^ 2 := by
  rcases le_or_gt (-1) x with h | h
  · have h1 : |x| ≤ 1 := abs_le.2 ⟨h, hx⟩
    have := Real.abs_exp_sub_one_sub_id_le h1
    have h2 := (abs_le.1 this).2
    linarith
  · have h1 : Real.exp x ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    nlinarith

theorem condExp_exp_step {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω)
    [IsProbabilityMeasure μ] (m : MeasurableSpace Ω) (hm : m ≤ m0) (Z : Ω → ℝ) (α : ℝ) (hα : 0 < α)
    (hZ : Integrable Z μ) (hZ2 : Integrable (fun ω => Z ω ^ 2) μ)
    (hle : ∀ᵐ ω ∂μ, α * Z ω ≤ 1) (hdrift : μ[Z | m] ≤ᵐ[μ] 0) :
    μ[fun ω => Real.exp (α * Z ω - α ^ 2 * (μ[fun ω => Z ω ^ 2 | m]) ω) | m] ≤ᵐ[μ] 1 := by
  set v := μ[fun ω => Z ω ^ 2 | m] with hv
  have hv_sm : StronglyMeasurable[m] v := stronglyMeasurable_condExp
  have hv0 : 0 ≤ᵐ[μ] v := condExp_nonneg (ae_of_all _ fun ω => sq_nonneg _)
  set f : Ω → ℝ := fun ω => Real.exp (-(α ^ 2 * v ω)) with hf
  set g : Ω → ℝ := fun ω => Real.exp (α * Z ω) with hg
  have hf_sm : StronglyMeasurable[m] f :=
    (Real.continuous_exp.comp_stronglyMeasurable ((hv_sm.const_mul (α ^ 2)).neg))
  have hg_aesm : AEStronglyMeasurable[m0] g μ :=
    Real.continuous_exp.comp_aestronglyMeasurable (hZ.aestronglyMeasurable.const_mul α : AEStronglyMeasurable[m0] (fun ω => α * Z ω) μ)
  have hg_bd : ∀ᵐ ω ∂μ, ‖g ω‖ ≤ Real.exp 1 := by
    filter_upwards [hle] with ω h
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact Real.exp_le_exp.2 h
  have hg_int : Integrable g μ := (integrable_const (Real.exp 1)).mono hg_aesm (by
    filter_upwards [hg_bd] with ω h
    simpa [Real.norm_of_nonneg (Real.exp_pos 1).le] using h)
  have hfg_int : Integrable (f * g) μ := by
    refine (integrable_const (Real.exp 1)).mono
      ((hf_sm.mono hm).aestronglyMeasurable.mul hg_aesm) ?_
    filter_upwards [hg_bd, hv0] with ω h1 h2
    rw [Pi.mul_apply, norm_mul, Real.norm_of_nonneg (Real.exp_pos 1).le]
    have hf1 : ‖f ω‖ ≤ 1 := by
      rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_le_one_iff]
      have : 0 ≤ v ω := h2
      nlinarith [sq_nonneg α]
    calc ‖f ω‖ * ‖g ω‖ ≤ 1 * Real.exp 1 :=
          mul_le_mul hf1 h1 (norm_nonneg _) zero_le_one
      _ = Real.exp 1 := one_mul _
  have hpoly_int : Integrable (fun ω => 1 + α * Z ω + α ^ 2 * Z ω ^ 2) μ :=
    ((integrable_const 1).add (hZ.const_mul α)).add (hZ2.const_mul _)
  have hg_le : g ≤ᵐ[μ] fun ω => 1 + α * Z ω + α ^ 2 * Z ω ^ 2 := by
    filter_upwards [hle] with ω h
    have := exp_le_one_add_add_sq (α * Z ω) h
    simp only [hg]
    nlinarith [this]
  have hc1 := condExp_mono (m := m) hg_int hpoly_int hg_le
  have hc2 : μ[fun ω => 1 + α * Z ω + α ^ 2 * Z ω ^ 2 | m] =ᵐ[μ]
      fun ω => 1 + α * (μ[Z | m]) ω + α ^ 2 * v ω := by
    have e1 : (fun ω => 1 + α * Z ω + α ^ 2 * Z ω ^ 2) =
        ((fun _ => (1 : ℝ)) + α • Z) + (α ^ 2) • (fun ω => Z ω ^ 2) := by
      funext ω; simp [smul_eq_mul]
    rw [e1]
    have a1 := condExp_add (m := m) ((integrable_const (1 : ℝ)).add (hZ.smul α)) (hZ2.smul (α ^ 2))
    have a2 := condExp_add (m := m) (integrable_const (1 : ℝ)) (hZ.smul α)
    have a3 := condExp_smul (μ := μ) α Z m
    have a4 := condExp_smul (μ := μ) (α ^ 2) (fun ω => Z ω ^ 2) m
    rw [condExp_const hm (1 : ℝ)] at a2
    filter_upwards [a1, a2, a3, a4] with ω h1 h2 h3 h4
    rw [h1, Pi.add_apply, h2, Pi.add_apply, h3, h4]
    simp [smul_eq_mul, hv]
  have hprod : μ[fun ω => Real.exp (α * Z ω - α ^ 2 * v ω) | m] =ᵐ[μ] f * μ[g | m] := by
    have e : (fun ω => Real.exp (α * Z ω - α ^ 2 * v ω)) = f * g := by
      funext ω
      simp only [hf, hg, Pi.mul_apply, ← Real.exp_add]
      ring_nf
    rw [e]
    exact condExp_mul_of_stronglyMeasurable_left hf_sm hfg_int hg_int
  filter_upwards [hprod, hc1, hc2, hdrift, hv0] with ω h1 h2 h3 h4 h5
  rw [h1, Pi.mul_apply, Pi.one_apply]
  have hv5 : 0 ≤ v ω := h5
  have hfpos : 0 < f ω := Real.exp_pos _
  have hbound : (μ[g | m]) ω ≤ 1 + α ^ 2 * v ω := by
    have h4' : (μ[Z | m]) ω ≤ 0 := h4
    rw [h3] at h2
    nlinarith
  calc f ω * (μ[g | m]) ω ≤ f ω * (1 + α ^ 2 * v ω) := mul_le_mul_of_nonneg_left hbound hfpos.le
    _ ≤ f ω * Real.exp (α ^ 2 * v ω) := mul_le_mul_of_nonneg_left (by
        have := Real.add_one_le_exp (α ^ 2 * v ω); linarith) hfpos.le
    _ = 1 := by simp only [hf]; rw [← Real.exp_add]; simp


theorem integral_expProc_le_one {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω)
    [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0) (X : ℕ → Ω → ℝ) (α : ℝ) (hα : 0 < α)
    (hXm : ∀ t, StronglyMeasurable[ℱ (t + 1)] (X t)) (hX : ∀ t, Integrable (X t) μ)
    (hX2 : ∀ t, Integrable (fun ω => X t ω ^ 2) μ) (hle : ∀ t, ∀ᵐ ω ∂μ, α * X t ω ≤ 1)
    (hdrift : ∀ t, μ[X t | ℱ t] ≤ᵐ[μ] 0) (n : ℕ) :
    Integrable (expProc μ ℱ X α n) μ ∧
      ∫ ω, expProc μ ℱ X α n ω ∂μ ≤ 1 := by
  set v : ℕ → Ω → ℝ := fun t => μ[fun ω => X t ω ^ 2 | ℱ t] with hv
  have hv0 : ∀ᵐ ω ∂μ, ∀ t, 0 ≤ v t ω :=
    ae_all_iff.2 fun t => condExp_nonneg (ae_of_all _ fun ω => sq_nonneg _)
  have hle' : ∀ᵐ ω ∂μ, ∀ t, α * X t ω ≤ 1 := ae_all_iff.2 hle
  set G : ℕ → Ω → ℝ := fun t ω => Real.exp (α * X t ω - α ^ 2 * v t ω) with hG
  have hsucc : ∀ k ω, expProc μ ℱ X α (k + 1) ω = expProc μ ℱ X α k ω * G k ω := by
    intro k ω
    simp only [expProc, predVar, hG, hv, Finset.sum_range_succ, ← Real.exp_add]
    ring_nf
  have hMsm : ∀ k, StronglyMeasurable[ℱ k] (expProc μ ℱ X α k) := by
    intro k
    have h1 : StronglyMeasurable[ℱ k] (fun ω => ∑ t ∈ Finset.range k, X t ω) :=
      Finset.stronglyMeasurable_fun_sum _ fun t ht =>
        (hXm t).mono (ℱ.mono (Finset.mem_range.1 ht))
    have h2 : StronglyMeasurable[ℱ k] (fun ω => predVar μ ℱ X k ω) :=
      Finset.stronglyMeasurable_fun_sum _ fun t ht =>
        (stronglyMeasurable_condExp (m := ℱ t)).mono (ℱ.mono (Finset.mem_range.1 ht).le)
    exact Real.continuous_exp.comp_stronglyMeasurable ((h1.const_mul α).sub (h2.const_mul (α ^ 2)))
  have hMpos : ∀ k ω, 0 < expProc μ ℱ X α k ω := fun k ω => Real.exp_pos _
  have hMbd : ∀ k, ∀ᵐ ω ∂μ, expProc μ ℱ X α k ω ≤ Real.exp k := by
    intro k
    filter_upwards [hv0, hle'] with ω h0 h1
    simp only [expProc]
    apply Real.exp_le_exp.2
    have hs : α * ∑ t ∈ Finset.range k, X t ω ≤ k := by
      rw [Finset.mul_sum]
      calc ∑ t ∈ Finset.range k, α * X t ω ≤ ∑ t ∈ Finset.range k, (1 : ℝ) :=
            Finset.sum_le_sum fun t _ => h1 t
        _ = k := by simp
    have hp : 0 ≤ predVar μ ℱ X k ω := Finset.sum_nonneg fun t _ => h0 t
    nlinarith [sq_nonneg α]
  have hMint : ∀ k, Integrable (expProc μ ℱ X α k) μ := by
    intro k
    refine (integrable_const (Real.exp k)).mono ((hMsm k).mono (ℱ.le k)).aestronglyMeasurable ?_
    filter_upwards [hMbd k] with ω h
    rw [Real.norm_of_nonneg (hMpos k ω).le, Real.norm_of_nonneg (Real.exp_pos _).le]
    exact h
  refine ⟨hMint n, ?_⟩
  induction n with
  | zero => simp [expProc, predVar]
  | succ k ih =>
    have hGint : Integrable (G k) μ := by
      refine (integrable_const (Real.exp 1)).mono ?_ ?_
      · have hXk : AEStronglyMeasurable[m0] (fun ω => α * X k ω - α ^ 2 * v k ω) μ :=
          ((hX k).aestronglyMeasurable.const_mul α).sub
            (((stronglyMeasurable_condExp (m := ℱ k)).mono (ℱ.le k)).aestronglyMeasurable.const_mul _)
        exact Real.continuous_exp.comp_aestronglyMeasurable hXk
      · filter_upwards [hv0, hle'] with ω h0 h1
        rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_of_nonneg (Real.exp_pos _).le]
        apply Real.exp_le_exp.2
        have := h0 k
        nlinarith [h1 k, sq_nonneg α]
    have hprod : expProc μ ℱ X α (k + 1) = expProc μ ℱ X α k * G k := funext (hsucc k)
    have hpull : μ[expProc μ ℱ X α (k + 1) | ℱ k] =ᵐ[μ] expProc μ ℱ X α k * μ[G k | ℱ k] := by
      rw [hprod]
      exact condExp_mul_of_stronglyMeasurable_left (hMsm k) (hprod ▸ hMint (k + 1)) hGint
    have hstep : μ[G k | ℱ k] ≤ᵐ[μ] 1 :=
      condExp_exp_step μ (ℱ k) (ℱ.le k) (X k) α hα (hX k) (hX2 k) (hle k) (hdrift k)
    calc ∫ ω, expProc μ ℱ X α (k + 1) ω ∂μ
        = ∫ ω, (μ[expProc μ ℱ X α (k + 1) | ℱ k]) ω ∂μ := (integral_condExp (ℱ.le k)).symm
      _ ≤ ∫ ω, expProc μ ℱ X α k ω ∂μ := by
        refine integral_mono_ae integrable_condExp (hMint k) ?_
        filter_upwards [hpull, hstep] with ω h1 h2
        rw [h1, Pi.mul_apply]
        calc expProc μ ℱ X α k ω * (μ[G k | ℱ k]) ω ≤ expProc μ ℱ X α k ω * 1 :=
              mul_le_mul_of_nonneg_left h2 (hMpos k ω).le
          _ = expProc μ ℱ X α k ω := mul_one _
      _ ≤ 1 := ih


theorem freedman_unnorm {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω)
    [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0) (X : ℕ → Ω → ℝ) (α : ℝ) (hα : 0 < α)
    (hXm : ∀ t, StronglyMeasurable[ℱ (t + 1)] (X t)) (hX : ∀ t, Integrable (X t) μ)
    (hX2 : ∀ t, Integrable (fun ω => X t ω ^ 2) μ) (hle : ∀ t, ∀ᵐ ω ∂μ, α * X t ω ≤ 1)
    (hdrift : ∀ t, μ[X t | ℱ t] ≤ᵐ[μ] 0) (n : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    μ {ω | α * predVar μ ℱ X n ω + Real.log (1 / δ) / α ≤ ∑ t ∈ Finset.range n, X t ω}
      ≤ ENNReal.ofReal δ := by
  obtain ⟨hint, hle1⟩ := integral_expProc_le_one μ ℱ X α hα hXm hX hX2 hle hdrift n
  have hsub : {ω | α * predVar μ ℱ X n ω + Real.log (1 / δ) / α ≤ ∑ t ∈ Finset.range n, X t ω}
      ⊆ {ω | 1 / δ ≤ expProc μ ℱ X α n ω} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    have h1 : Real.log (1 / δ) ≤ α * ∑ t ∈ Finset.range n, X t ω - α ^ 2 * predVar μ ℱ X n ω := by
      have h2 : Real.log (1 / δ) / α ≤ ∑ t ∈ Finset.range n, X t ω - α * predVar μ ℱ X n ω := by linarith
      rw [div_le_iff₀ hα] at h2
      nlinarith
    calc 1 / δ = Real.exp (Real.log (1 / δ)) := (Real.exp_log (by positivity)).symm
      _ ≤ expProc μ ℱ X α n ω := Real.exp_le_exp.2 h1
  have hmarkov := mul_meas_ge_le_integral_of_nonneg (ae_of_all _ fun ω => (Real.exp_pos _).le) hint (1 / δ)
  have hreal : μ.real {ω | 1 / δ ≤ expProc μ ℱ X α n ω} ≤ δ := by
    have h := le_trans hmarkov hle1
    rw [one_div, inv_mul_le_iff₀ hδ, mul_one] at h
    simpa [one_div, expProc] using h
  calc μ _ ≤ μ {ω | 1 / δ ≤ expProc μ ℱ X α n ω} := measure_mono hsub
    _ = ENNReal.ofReal (μ.real {ω | 1 / δ ≤ expProc μ ℱ X α n ω}) := by
      rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
    _ ≤ ENNReal.ofReal δ := ENNReal.ofReal_le_ofReal hreal

theorem condExp_trunc_nonpos {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω)
    [IsProbabilityMeasure μ] (m : MeasurableSpace Ω) (hm : m ≤ m0) (X : Ω → ℝ)
    (hXm : StronglyMeasurable[m0] X) (hX : Integrable X μ)
    (hdrift : μ[X | m] =ᵐ[μ] 0) (A : Set Ω) (hA : MeasurableSet[m] A) (c : ℝ) (hc : 0 ≤ c) :
    μ[A.indicator (fun ω => if X ω ≤ c then X ω else 0) | m] ≤ᵐ[μ] 0 := by
  set W : Ω → ℝ := {ω | c < X ω}.indicator X with hW
  have hs : MeasurableSet[m0] {ω | c < X ω} := measurableSet_lt measurable_const hXm.measurable
  have hWint : Integrable W μ := hX.indicator hs
  have hW0 : ∀ ω, 0 ≤ W ω := by
    intro ω
    simp only [hW, Set.indicator_apply, Set.mem_ofPred_eq]
    split_ifs with h
    · linarith
    · exact le_rfl
  have e : (fun ω => if X ω ≤ c then X ω else 0) = X - W := by
    funext ω
    simp only [hW, Pi.sub_apply, Set.indicator_apply, Set.mem_ofPred_eq]
    by_cases h : X ω ≤ c
    · simp [h, not_lt.2 h]
    · simp [h, lt_of_not_ge h]
  rw [e]
  filter_upwards [condExp_indicator (m := m) (hX.sub hWint) hA, condExp_sub (m := m) hX hWint,
    hdrift, condExp_nonneg (m := m) (ae_of_all μ hW0)] with ω h1 h2 h3 h4
  rw [h1]
  by_cases hω : ω ∈ A
  · rw [Set.indicator_of_mem hω, h2, Pi.sub_apply, h3]
    simp only [Pi.zero_apply, zero_sub, neg_nonpos]
    exact h4
  · rw [Set.indicator_of_notMem hω]
    exact le_rfl

theorem pow_two_between (a : ℝ) (ha : 1 ≤ a) : ∃ i : ℕ, 1 ≤ i ∧ a ≤ (2 : ℝ) ^ i ∧ (2 : ℝ) ^ i ≤ 2 * a := by
  obtain ⟨n, h1, h2⟩ := exists_nat_pow_near ha (by norm_num : (1 : ℝ) < 2)
  refine ⟨n + 1, by omega, h2.le, ?_⟩
  rw [pow_succ]
  linarith

theorem dyadic_choice (U V δ : ℝ) (hU : 1 ≤ U) (hV : 0 ≤ V) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ i : ℕ, 1 ≤ i ∧ U ≤ 2 ^ i ∧ (2 : ℝ) ^ i ≤ 2 * max U (Real.sqrt V) ∧
      V / 2 ^ i + 2 ^ i * Real.log (2 ^ i / δ) ≤
        3 * Real.sqrt (V * Real.log (2 * max U (Real.sqrt V) / δ))
          + 2 * U * Real.log (2 * max U (Real.sqrt V) / δ) := by
  set q := Real.sqrt V with hq
  set mx := max U q with hmx
  set l := Real.log (2 * mx / δ) with hl
  have hq0 : 0 ≤ q := Real.sqrt_nonneg V
  have hqq : q * q = V := Real.mul_self_sqrt hV
  have hmx1 : 1 ≤ mx := le_trans hU (le_max_left _ _)
  have harg : 2 ≤ 2 * mx / δ := by
    rw [le_div_iff₀ hδ0]; nlinarith
  have hl0 : Real.log 2 ≤ l := Real.log_le_log (by norm_num) harg
  have hlog2 := Real.log_two_gt_d9
  have hlpos : 0 < l := by linarith
  set r := Real.sqrt l with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg l
  have hrr : r * r = l := Real.mul_self_sqrt hlpos.le
  have hr13 : 1 / 2 < r := by
    rw [hr, Real.lt_sqrt (by norm_num)]; linarith
  have hsq : Real.sqrt (V * l) = q * r := by rw [Real.sqrt_mul hV]
  rw [hsq]
  -- the logarithm at a candidate power is at most l
  have hlogle : ∀ i : ℕ, (2 : ℝ) ^ i ≤ 2 * mx → Real.log (2 ^ i / δ) ≤ l := fun i hi =>
    Real.log_le_log (by positivity) (div_le_div_of_nonneg_right hi hδ0.le)
  -- reduce to the bound with l
  suffices h : ∃ i : ℕ, 1 ≤ i ∧ U ≤ 2 ^ i ∧ (2 : ℝ) ^ i ≤ 2 * mx ∧
      V / 2 ^ i + 2 ^ i * l ≤ 3 * (q * r) + 2 * U * l by
    obtain ⟨i, h1, h2, h3, h4⟩ := h
    refine ⟨i, h1, h2, h3, le_trans ?_ h4⟩
    have := hlogle i h3
    have hp : (0 : ℝ) < 2 ^ i := by positivity
    nlinarith
  rcases lt_or_ge l 1 with hl1 | hl1
  · -- l < 1: a power of two in [mx, 2 mx]
    obtain ⟨i, hi1, hi2, hi3⟩ := pow_two_between mx hmx1
    refine ⟨i, hi1, le_trans (le_max_left _ _) hi2, hi3, ?_⟩
    have hp : (0 : ℝ) < 2 ^ i := by positivity
    have hr1 : r < 1 := by nlinarith
    have hA : V / 2 ^ i ≤ V / mx := div_le_div_of_nonneg_left hV (by linarith) hi2
    have hB : (2 : ℝ) ^ i * l ≤ 2 * mx * l := mul_le_mul_of_nonneg_right hi3 hlpos.le
    rcases le_total U q with hUq | hqU
    · have hm : mx = q := max_eq_right hUq
      rw [hm] at hA hB
      have hq1 : 0 < q := by linarith
      have hVq : V / q = q := by rw [← hqq]; field_simp
      rw [hVq] at hA
      -- q (1 + 2 l) ≤ 3 q r since (2 r - 1)(r - 1) ≤ 0
      have key : q * (1 + 2 * l) ≤ 3 * (q * r) := by
        rw [← hrr]; nlinarith [mul_nonneg hq0 (mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * r - 1)
          (by linarith : (0 : ℝ) ≤ 1 - r))]
      nlinarith
    · have hm : mx = U := max_eq_left hqU
      rw [hm] at hA hB
      have hU0 : 0 < U := by linarith
      have hVU : V / U ≤ q := by
        rw [div_le_iff₀ hU0, ← hqq]; nlinarith
      have h3 : q ≤ 3 * (q * r) := by nlinarith
      nlinarith
  · -- l ≥ 1
    have hr1 : 1 ≤ r := by nlinarith
    rcases le_total q (U * r) with hA | hB
    · -- case A: a power of two in [U, 2 U]
      obtain ⟨i, hi1, hi2, hi3⟩ := pow_two_between U hU
      refine ⟨i, hi1, hi2, le_trans hi3 (by have := le_max_left U q; linarith), ?_⟩
      have hU0 : 0 < U := by linarith
      have h1 : V / 2 ^ i ≤ V / U := div_le_div_of_nonneg_left hV hU0 hi2
      have h2 : V / U ≤ q * r := by
        rw [div_le_iff₀ hU0, ← hqq]; nlinarith
      have h3 : (2 : ℝ) ^ i * l ≤ 2 * U * l := mul_le_mul_of_nonneg_right hi3 hlpos.le
      nlinarith [mul_nonneg hq0 hr0]
    · -- case B: a power of two in [q / r, 2 q / r]
      have hs1 : 1 ≤ q / r := by
        rw [le_div_iff₀ (by linarith)]; nlinarith
      obtain ⟨i, hi1, hi2, hi3⟩ := pow_two_between (q / r) hs1
      have hrpos : 0 < r := by linarith
      have hUs : U ≤ q / r := by rw [le_div_iff₀ hrpos]; linarith
      have hsq' : q / r ≤ q := div_le_self hq0 hr1
      refine ⟨i, hi1, le_trans hUs hi2, le_trans hi3 (by have := le_max_right U q; linarith), ?_⟩
      have hspos : 0 < q / r := by linarith
      have h1 : V / 2 ^ i ≤ V / (q / r) := div_le_div_of_nonneg_left hV hspos hi2
      have h2 : V / (q / r) = q * r := by
        have hq1 : 0 < q := by
          rcases eq_or_lt_of_le hq0 with h | h
          · rw [← h, zero_div] at hspos; exact absurd hspos (lt_irrefl 0)
          · exact h
        rw [← hqq]; field_simp
      have h3 : (2 : ℝ) ^ i * l ≤ 2 * (q / r) * l := mul_le_mul_of_nonneg_right hi3 hlpos.le
      have h4 : 2 * (q / r) * l = 2 * (q * r) := by
        rw [← hrr]; field_simp
      have hUl : 0 ≤ 2 * U * l := by positivity
      rw [h2] at h1; rw [h4] at h3
      linarith


theorem upMax_facts {Ω : Type*} (X : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) :
    1 ≤ upMax X k ω ∧
      (∀ t < k, X t ω ≤ upMax X k ω) ∧
      upMax X (k + 1) ω = max (upMax X k ω) (X k ω) ∧
      upMax X k ω ≤ absMax X k ω ∧
      upMax (fun t ω => - X t ω) k ω ≤ absMax X k ω := by
  have habs1 : 1 ≤ absMax X k ω := (Finset.le_fold_max _).2 (Or.inl le_rfl)
  have habs2 : ∀ t < k, |X t ω| ≤ absMax X k ω := fun t ht =>
    (Finset.le_fold_max _).2 (Or.inr ⟨t, Finset.mem_range.2 ht, le_rfl⟩)
  refine ⟨(Finset.le_fold_max _).2 (Or.inl le_rfl),
    fun t ht => (Finset.le_fold_max _).2 (Or.inr ⟨t, Finset.mem_range.2 ht, le_rfl⟩), ?_, ?_, ?_⟩
  · simp only [upMax]
    rw [Finset.range_add_one, Finset.fold_insert Finset.notMem_range_self, max_comm]
  · exact (Finset.fold_max_le _).2 ⟨habs1, fun t ht =>
      le_trans (le_abs_self _) (habs2 t (Finset.mem_range.1 ht))⟩
  · exact (Finset.fold_max_le _).2 ⟨habs1, fun t ht =>
      le_trans (neg_le_abs _) (habs2 t (Finset.mem_range.1 ht))⟩

theorem upMax_measurable {Ω : Type*} {m0 : MeasurableSpace Ω} (ℱ : Filtration ℕ m0)
    (X : ℕ → Ω → ℝ) (hXm : ∀ t, StronglyMeasurable[ℱ (t + 1)] (X t)) (k : ℕ) :
    StronglyMeasurable[ℱ k] (upMax X k) ∧
      StronglyMeasurable[ℱ k] (absMax X k) := by
  induction k with
  | zero =>
    have e0 : upMax X 0 = fun _ => 1 := by funext ω; simp [upMax]
    have e0' : absMax X 0 = fun _ => 1 := by funext ω; simp [absMax]
    rw [e0, e0']
    exact ⟨stronglyMeasurable_const, stronglyMeasurable_const⟩
  | succ k ih =>
    have hmono := ℱ.mono (Nat.le_succ k)
    have e1 : upMax X (k + 1) = fun ω => max (X k ω) (upMax X k ω) := by
      funext ω; simp only [upMax]; rw [Finset.range_add_one, Finset.fold_insert Finset.notMem_range_self]
    have e2 : absMax X (k + 1) = fun ω => max (|X k ω|) (absMax X k ω) := by
      funext ω; simp only [absMax]; rw [Finset.range_add_one, Finset.fold_insert Finset.notMem_range_self]
    rw [e1, e2]
    let _ : MeasurableSpace Ω := ℱ (k + 1)
    exact ⟨((hXm k).measurable.max (ih.1.mono hmono).measurable).stronglyMeasurable,
      ((hXm k).measurable.abs.max (ih.2.mono hmono).measurable).stronglyMeasurable⟩

theorem freedman_rescale (V S B κ δ : ℝ) (hV : 0 ≤ V) (hB : 0 ≤ B) (hκ : 0 < κ)
    (h : |κ * S| ≤ 3 * Real.sqrt (κ ^ 2 * V * Real.log (4 * max B (Real.sqrt (κ ^ 2 * V)) / δ))
        + 2 * B * Real.log (4 * max B (Real.sqrt (κ ^ 2 * V)) / δ)) :
    |S| ≤ 3 * Real.sqrt (V * Real.log (4 * max B (κ * Real.sqrt V) / δ))
        + 2 * (B / κ) * Real.log (4 * max B (κ * Real.sqrt V) / δ) := by
  have hs : Real.sqrt (κ ^ 2 * V) = κ * Real.sqrt V := by
    rw [Real.sqrt_mul (sq_nonneg κ), Real.sqrt_sq hκ.le]
  rw [hs] at h
  set l := Real.log (4 * max B (κ * Real.sqrt V) / δ)
  have hs2 : Real.sqrt (κ ^ 2 * V * l) = κ * Real.sqrt (V * l) := by
    rw [mul_assoc, Real.sqrt_mul (sq_nonneg κ), Real.sqrt_sq hκ.le]
  rw [hs2, abs_mul, abs_of_pos hκ] at h
  have h2 : κ * |S| ≤ κ * (3 * Real.sqrt (V * l) + 2 * (B / κ) * l) := by
    have : κ * (3 * Real.sqrt (V * l) + 2 * (B / κ) * l) = 3 * (κ * Real.sqrt (V * l)) + 2 * B * l := by
      field_simp
    rw [this]
    exact h
  exact le_of_mul_le_mul_left h2 hκ

theorem condExp_stopped {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω)
    [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0) (X : ℕ → Ω → ℝ) (hX : ∀ t, Integrable (X t) μ)
    (hX2 : ∀ t, Integrable (fun ω => X t ω ^ 2) μ) (τ : Ω → ℕ) (hτ : ∀ t, MeasurableSet[ℱ t] {ω | t < τ ω})
    (hdrift : ∀ t, ∀ᵐ ω ∂μ, t < τ ω → μ[X t | ℱ t] ω = 0) (t : ℕ) :
    μ[(fun ω => if t < τ ω then X t ω else 0) | ℱ t] =ᵐ[μ] 0 ∧
      μ[(fun ω => (if t < τ ω then X t ω else 0) ^ 2) | ℱ t] =ᵐ[μ]
        fun ω => if t < τ ω then (μ[fun ω => X t ω ^ 2 | ℱ t]) ω else 0 := by
  set A : Set Ω := {ω | t < τ ω} with hA
  have e1 : (fun ω => if t < τ ω then X t ω else 0) = A.indicator (X t) := by
    funext ω; simp [hA, Set.indicator_apply]
  have e2 : (fun ω => (if t < τ ω then X t ω else 0) ^ 2) = A.indicator (fun ω => X t ω ^ 2) := by
    funext ω; by_cases h : t < τ ω <;> simp [hA, h]
  have e3 : (fun ω => if t < τ ω then (μ[fun ω => X t ω ^ 2 | ℱ t]) ω else 0)
      = A.indicator (μ[fun ω => X t ω ^ 2 | ℱ t]) := by
    funext ω; simp [hA, Set.indicator_apply]
  constructor
  · rw [e1]
    filter_upwards [condExp_indicator (m := ℱ t) (hX t) (hτ t), hdrift t] with ω h1 h2
    rw [h1, Set.indicator_apply, Pi.zero_apply]
    split_ifs with h
    · exact h2 h
    · rfl
  · rw [e2, e3]
    exact condExp_indicator (hX2 t) (hτ t)

theorem stopped_sums {Ω : Type*} (X g : ℕ → Ω → ℝ) (τ : Ω → ℕ) (n : ℕ) (ω : Ω)
    (hτn : τ ω ≤ n) :
    ∑ t ∈ Finset.range n, (if t < τ ω then g t ω else 0) = ∑ t ∈ Finset.range (τ ω), g t ω ∧
      absMax (fun t ω => if t < τ ω then X t ω else 0) n ω =
        absMax X (τ ω) ω := by
  induction n, hτn using Nat.le_induction with
  | base =>
    constructor
    · exact Finset.sum_congr rfl fun t ht => by simp [Finset.mem_range.1 ht]
    · simp only [absMax]
      exact Finset.fold_congr fun t ht => by simp [Finset.mem_range.1 ht]
  | succ m hm ih =>
    constructor
    · have hn : ¬ (m < τ ω) := by omega
      rw [Finset.sum_range_succ, ih.1]
      simp [hn]
    · simp only [absMax] at ih ⊢
      have hn : ¬ (m < τ ω) := by omega
      rw [Finset.range_add_one, Finset.fold_insert Finset.notMem_range_self, ih.2]
      simp only [hn, ↓reduceIte, abs_zero]
      exact max_eq_right (le_trans zero_le_one ((Finset.le_fold_max _).2 (Or.inl le_rfl)))

/-! ## Assemblies -/

theorem upMax_mono {Ω : Type*} (X : ℕ → Ω → ℝ) (ω : Ω) {k l : ℕ} (hkl : k ≤ l) :
    upMax X k ω ≤ upMax X l ω := by
  induction l, hkl using Nat.le_induction with
  | base => exact le_rfl
  | succ l _ ih =>
    rw [(upMax_facts X l ω).2.2.1]
    exact le_trans ih (le_max_left _ _)

theorem freedman_one_sided {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m0) (X : ℕ → Ω → ℝ) (hXm : ∀ t, StronglyMeasurable[ℱ (t + 1)] (X t))
    (hX : ∀ t, Integrable (X t) μ) (hX2 : ∀ t, Integrable (fun ω => X t ω ^ 2) μ)
    (hmg : ∀ t, μ[X t | ℱ t] =ᵐ[μ] 0) (n : ℕ) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    μ {ω | 3 * Real.sqrt (predVar μ ℱ X n ω *
          Real.log (2 * max (upMax X n ω) (Real.sqrt (predVar μ ℱ X n ω)) / δ))
        + 2 * upMax X n ω * Real.log (2 * max (upMax X n ω) (Real.sqrt (predVar μ ℱ X n ω)) / δ)
        < ∑ t ∈ Finset.range n, X t ω} ≤ ENNReal.ofReal δ := by
  set c : ℕ → ℝ := fun i => (2 : ℝ) ^ (i + 1) with hc
  have hcpos : ∀ i, 0 < c i := fun i => by positivity
  set Z : ℕ → ℕ → Ω → ℝ := fun i t ω => if upMax X (t + 1) ω ≤ c i then X t ω else 0 with hZ
  have hZle : ∀ i t ω, Z i t ω ≤ c i := by
    intro i t ω
    simp only [hZ]
    split_ifs with h
    · exact le_trans ((upMax_facts X (t + 1) ω).2.1 t (Nat.lt_succ_self t)) h
    · exact (hcpos i).le
  have hZsq : ∀ i t ω, Z i t ω ^ 2 ≤ X t ω ^ 2 := by
    intro i t ω
    simp only [hZ]
    split_ifs
    · exact le_rfl
    · simpa using sq_nonneg (X t ω)
  have hZabs : ∀ i t ω, ‖Z i t ω‖ ≤ ‖X t ω‖ := by
    intro i t ω
    simp only [hZ]
    split_ifs
    · exact le_rfl
    · simp
  have hZm : ∀ i t, StronglyMeasurable[ℱ (t + 1)] (Z i t) := by
    intro i t
    have h1 := (upMax_measurable ℱ X hXm (t + 1)).1
    have hs : MeasurableSet[ℱ (t + 1)] {ω | upMax X (t + 1) ω ≤ c i} := h1.measurable measurableSet_Iic
    exact StronglyMeasurable.ite hs (hXm t) stronglyMeasurable_const
  have hZint : ∀ i t, Integrable (Z i t) μ := fun i t =>
    (hX t).mono ((hZm i t).mono (ℱ.le (t + 1))).aestronglyMeasurable (ae_of_all _ (hZabs i t))
  have hZ2int : ∀ i t, Integrable (fun ω => Z i t ω ^ 2) μ := by
    intro i t
    refine (hX2 t).mono ?_ (ae_of_all _ fun ω => ?_)
    · exact (((hZm i t).mono (ℱ.le (t + 1))).pow 2).aestronglyMeasurable
    · rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), abs_of_nonneg (sq_nonneg _)]
      exact hZsq i t ω
  have hZdrift : ∀ i t, μ[Z i t | ℱ t] ≤ᵐ[μ] 0 := by
    intro i t
    set A : Set Ω := {ω | upMax X t ω ≤ c i} with hA
    have hAm : MeasurableSet[ℱ t] A := (upMax_measurable ℱ X hXm t).1.measurable measurableSet_Iic
    have hEq : Z i t = A.indicator (fun ω => if X t ω ≤ c i then X t ω else 0) := by
      funext ω
      simp only [hZ, hA, Set.indicator_apply, Set.mem_ofPred_eq, (upMax_facts X t ω).2.2.1, max_le_iff]
      by_cases h1 : upMax X t ω ≤ c i <;> by_cases h2 : X t ω ≤ c i <;> simp [h1, h2]
    rw [hEq]
    exact condExp_trunc_nonpos μ (ℱ t) (ℱ.le t) (X t) ((hXm t).mono (ℱ.le (t + 1))) (hX t) (hmg t) A hAm
      (c i) (hcpos i).le
  set E : ℕ → Set Ω := fun i => {ω | 1 / c i * predVar μ ℱ (Z i) n ω + Real.log (1 / (δ / c i)) / (1 / c i)
    ≤ ∑ t ∈ Finset.range n, Z i t ω} with hE
  have hEμ : ∀ i, μ (E i) ≤ ENNReal.ofReal (δ / c i) := by
    intro i
    refine freedman_unnorm μ ℱ (Z i) (1 / c i) (by have := hcpos i; positivity) (hZm i) (hZint i) (hZ2int i)
      (fun t => ae_of_all _ fun ω => ?_) (hZdrift i) n (δ / c i) (by have := hcpos i; positivity)
    rw [one_div_mul_eq_div, div_le_one (hcpos i)]
    exact hZle i t ω
  have hVZ : ∀ᵐ ω ∂μ, ∀ i, predVar μ ℱ (Z i) n ω ≤ predVar μ ℱ X n ω := by
    rw [ae_all_iff]
    intro i
    have h : ∀ᵐ ω ∂μ, ∀ t, (μ[fun ω => Z i t ω ^ 2 | ℱ t]) ω ≤ (μ[fun ω => X t ω ^ 2 | ℱ t]) ω :=
      ae_all_iff.2 fun t => condExp_mono (hZ2int i t) (hX2 t) (ae_of_all _ (hZsq i t))
    filter_upwards [h] with ω hω
    exact Finset.sum_le_sum fun t _ => hω t
  have hV0 : ∀ᵐ ω ∂μ, 0 ≤ predVar μ ℱ X n ω := by
    have h : ∀ᵐ ω ∂μ, ∀ t, 0 ≤ (μ[fun ω => X t ω ^ 2 | ℱ t]) ω :=
      ae_all_iff.2 fun t => condExp_nonneg (ae_of_all _ fun ω => by positivity)
    filter_upwards [h] with ω hω
    exact Finset.sum_nonneg fun t _ => hω t
  have hsub : ∀ᵐ ω ∂μ, ω ∈ {ω | 3 * Real.sqrt (predVar μ ℱ X n ω *
          Real.log (2 * max (upMax X n ω) (Real.sqrt (predVar μ ℱ X n ω)) / δ))
        + 2 * upMax X n ω * Real.log (2 * max (upMax X n ω) (Real.sqrt (predVar μ ℱ X n ω)) / δ)
        < ∑ t ∈ Finset.range n, X t ω} → ω ∈ ⋃ i, E i := by
    filter_upwards [hVZ, hV0] with ω hω1 hω2 hmain
    obtain ⟨j, hj1, hUj, -, hjb⟩ :=
      dyadic_choice (upMax X n ω) (predVar μ ℱ X n ω) δ (upMax_facts X n ω).1 hω2 hδ0 hδ1
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    refine Set.mem_iUnion.2 ⟨i, ?_⟩
    have hsum : ∑ t ∈ Finset.range n, Z i t ω = ∑ t ∈ Finset.range n, X t ω := by
      refine Finset.sum_congr rfl fun t ht => ?_
      have : upMax X (t + 1) ω ≤ c i :=
        le_trans (upMax_mono X ω (Finset.mem_range.1 ht)) hUj
      simp only [hZ, this, ite_true]
    simp only [hE, Set.mem_ofPred_eq, hsum]
    refine le_trans ?_ (le_trans hjb hmain.le)
    have hci : c i = (2 : ℝ) ^ (i + 1) := rfl
    have hcp := hcpos i
    have h1 : 1 / c i * predVar μ ℱ (Z i) n ω ≤ predVar μ ℱ X n ω / 2 ^ (i + 1) := by
      rw [one_div_mul_eq_div, ← hci]
      exact div_le_div_of_nonneg_right (hω1 i) hcp.le
    have h2 : Real.log (1 / (δ / c i)) / (1 / c i) = 2 ^ (i + 1) * Real.log (2 ^ (i + 1) / δ) := by
      rw [one_div_div, div_div_eq_mul_div, div_one, ← hci]
      ring
    rw [h2]
    linarith
  calc μ _ ≤ μ (⋃ i, E i) := measure_mono_ae hsub
    _ ≤ ∑' i, μ (E i) := measure_iUnion_le E
    _ ≤ ∑' i, ENNReal.ofReal (δ / c i) := ENNReal.tsum_le_tsum hEμ
    _ = ENNReal.ofReal δ := by
      have hgeo : ∀ i, δ / c i = δ / 2 / 2 ^ i := fun i => by
        simp only [hc, pow_succ]; ring
      simp_rw [hgeo]
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => by positivity)
        (summable_geometric_two' δ)]
      rw [tsum_geometric_two']

theorem thr_mono (V U B δ : ℝ) (hV : 0 ≤ V) (hU : 1 ≤ U) (hUB : U ≤ B) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    3 * Real.sqrt (V * Real.log (4 * max U (Real.sqrt V) / δ)) + 2 * U * Real.log (4 * max U (Real.sqrt V) / δ)
      ≤ 3 * Real.sqrt (V * Real.log (4 * max B (Real.sqrt V) / δ))
        + 2 * B * Real.log (4 * max B (Real.sqrt V) / δ) := by
  have hm : 1 ≤ max U (Real.sqrt V) := le_trans hU (le_max_left _ _)
  have h4 : 0 < 4 * max U (Real.sqrt V) / δ := by positivity
  have hle : 4 * max U (Real.sqrt V) / δ ≤ 4 * max B (Real.sqrt V) / δ := by
    gcongr
  have hl1 := Real.log_le_log h4 hle
  have hl0 : 0 ≤ Real.log (4 * max U (Real.sqrt V) / δ) := Real.log_nonneg (by
    rw [le_div_iff₀ hδ0]; nlinarith)
  refine add_le_add ?_ (mul_le_mul (by linarith) hl1 hl0 (by linarith))
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hl1 hV)) (by norm_num)

theorem freedman_stopped {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m0) (X : ℕ → Ω → ℝ) (hXm : ∀ t, StronglyMeasurable[ℱ (t + 1)] (X t))
    (hX : ∀ t, Integrable (X t) μ) (hX2 : ∀ t, Integrable (fun ω => X t ω ^ 2) μ)
    (τ : Ω → ℕ) (hτ : IsStoppingTime ℱ (fun ω => (τ ω : WithTop ℕ))) (n : ℕ) (hτn : ∀ ω, τ ω ≤ n)
    (hdrift : ∀ t, ∀ᵐ ω ∂μ, t < τ ω → μ[X t | ℱ t] ω = 0) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    μ {ω | 3 * Real.sqrt (predVar μ ℱ X (τ ω) ω *
          Real.log (4 * max (absMax X (τ ω) ω) (Real.sqrt (predVar μ ℱ X (τ ω) ω)) / δ))
        + 2 * absMax X (τ ω) ω * Real.log (4 * max (absMax X (τ ω) ω) (Real.sqrt (predVar μ ℱ X (τ ω) ω)) / δ)
        < |∑ t ∈ Finset.range (τ ω), X t ω|} ≤ ENNReal.ofReal δ := by
  have hA : ∀ t, MeasurableSet[ℱ t] {ω | t < τ ω} := by
    intro t
    have h := (hτ t).compl
    convert h using 1
    ext ω
    simp
  set Y : ℕ → Ω → ℝ := fun t ω => if t < τ ω then X t ω else 0 with hY
  set W : ℕ → Ω → ℝ := fun t ω => - Y t ω with hW
  have hYabs : ∀ t ω, ‖Y t ω‖ ≤ ‖X t ω‖ := by
    intro t ω
    simp only [hY]
    split_ifs
    · exact le_rfl
    · simp
  have hYsq : ∀ t ω, Y t ω ^ 2 ≤ X t ω ^ 2 := by
    intro t ω
    simp only [hY]
    split_ifs
    · exact le_rfl
    · simpa using sq_nonneg (X t ω)
  have hYm : ∀ t, StronglyMeasurable[ℱ (t + 1)] (Y t) := fun t =>
    StronglyMeasurable.ite (ℱ.mono (Nat.le_succ t) _ (hA t)) (hXm t) stronglyMeasurable_const
  have hYint : ∀ t, Integrable (Y t) μ := fun t =>
    (hX t).mono ((hYm t).mono (ℱ.le (t + 1))).aestronglyMeasurable (ae_of_all _ (hYabs t))
  have hY2int : ∀ t, Integrable (fun ω => Y t ω ^ 2) μ := by
    intro t
    refine (hX2 t).mono ?_ (ae_of_all _ fun ω => ?_)
    · exact (((hYm t).mono (ℱ.le (t + 1))).pow 2).aestronglyMeasurable
    · rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), abs_of_nonneg (sq_nonneg _)]
      exact hYsq t ω
  have hYmg : ∀ t, μ[Y t | ℱ t] =ᵐ[μ] 0 := fun t =>
    (condExp_stopped μ ℱ X hX hX2 τ hA hdrift t).1
  have hWsq : ∀ t, (fun ω => W t ω ^ 2) = fun ω => Y t ω ^ 2 := fun t => by
    funext ω; simp only [hW, neg_sq]
  have hWm : ∀ t, StronglyMeasurable[ℱ (t + 1)] (W t) := fun t => (hYm t).neg
  have hWint : ∀ t, Integrable (W t) μ := fun t => (hYint t).neg
  have hW2int : ∀ t, Integrable (fun ω => W t ω ^ 2) μ := fun t => by rw [hWsq t]; exact hY2int t
  have hWmg : ∀ t, μ[W t | ℱ t] =ᵐ[μ] 0 := by
    intro t
    have h := condExp_neg (μ := μ) (Y t) (ℱ t)
    filter_upwards [h, hYmg t] with ω h1 h2
    simp only [hW] at h1 ⊢
    rw [show (fun ω => -Y t ω) = -Y t from rfl, h1]
    simp [h2]
  have hpvW : ∀ ω, predVar μ ℱ W n ω = predVar μ ℱ Y n ω := by
    intro ω
    simp only [predVar, hWsq]
  have hpvY : ∀ᵐ ω ∂μ, predVar μ ℱ Y n ω = predVar μ ℱ X (τ ω) ω := by
    have h : ∀ᵐ ω ∂μ, ∀ t, (μ[fun ω => Y t ω ^ 2 | ℱ t]) ω =
        if t < τ ω then (μ[fun ω => X t ω ^ 2 | ℱ t]) ω else 0 :=
      ae_all_iff.2 fun t => (condExp_stopped μ ℱ X hX hX2 τ hA hdrift t).2
    filter_upwards [h] with ω hω
    simp only [predVar]
    rw [Finset.sum_congr rfl fun t _ => hω t]
    exact (stopped_sums X (fun t ω => (μ[fun ω => X t ω ^ 2 | ℱ t]) ω) τ n ω (hτn ω)).1
  have hV0 : ∀ᵐ ω ∂μ, 0 ≤ predVar μ ℱ X (τ ω) ω := by
    have h : ∀ᵐ ω ∂μ, ∀ t, 0 ≤ (μ[fun ω => X t ω ^ 2 | ℱ t]) ω :=
      ae_all_iff.2 fun t => condExp_nonneg (ae_of_all _ fun ω => by positivity)
    filter_upwards [h] with ω hω
    exact Finset.sum_nonneg fun t _ => hω t
  have hsumY : ∀ ω, ∑ t ∈ Finset.range n, Y t ω = ∑ t ∈ Finset.range (τ ω), X t ω := fun ω =>
    (stopped_sums X X τ n ω (hτn ω)).1
  have hsumW : ∀ ω, ∑ t ∈ Finset.range n, W t ω = - ∑ t ∈ Finset.range (τ ω), X t ω := fun ω => by
    simp only [hW, Finset.sum_neg_distrib, hsumY]
  have habsY : ∀ ω, absMax Y n ω = absMax X (τ ω) ω := fun ω => (stopped_sums X X τ n ω (hτn ω)).2
  have hupY : ∀ ω, upMax Y n ω ≤ absMax X (τ ω) ω := fun ω =>
    (habsY ω) ▸ (upMax_facts Y n ω).2.2.2.1
  have hupW : ∀ ω, upMax W n ω ≤ absMax X (τ ω) ω := fun ω =>
    (habsY ω) ▸ (upMax_facts Y n ω).2.2.2.2
  have hδ2 : 0 < δ / 2 := by positivity
  have h1 := freedman_one_sided μ ℱ Y hYm hYint hY2int hYmg n (δ / 2) hδ2 (by linarith)
  have h2 := freedman_one_sided μ ℱ W hWm hWint hW2int hWmg n (δ / 2) hδ2 (by linarith)
  have hfour : ∀ m : ℝ, 2 * m / (δ / 2) = 4 * m / δ := fun m => by field_simp; ring
  simp only [hfour] at h1 h2
  have hsub : ∀ᵐ ω ∂μ, ω ∈ {ω | 3 * Real.sqrt (predVar μ ℱ X (τ ω) ω *
          Real.log (4 * max (absMax X (τ ω) ω) (Real.sqrt (predVar μ ℱ X (τ ω) ω)) / δ))
        + 2 * absMax X (τ ω) ω * Real.log (4 * max (absMax X (τ ω) ω) (Real.sqrt (predVar μ ℱ X (τ ω) ω)) / δ)
        < |∑ t ∈ Finset.range (τ ω), X t ω|} →
      ω ∈ {ω | 3 * Real.sqrt (predVar μ ℱ Y n ω *
          Real.log (4 * max (upMax Y n ω) (Real.sqrt (predVar μ ℱ Y n ω)) / δ))
        + 2 * upMax Y n ω * Real.log (4 * max (upMax Y n ω) (Real.sqrt (predVar μ ℱ Y n ω)) / δ)
        < ∑ t ∈ Finset.range n, Y t ω} ∪
      {ω | 3 * Real.sqrt (predVar μ ℱ W n ω *
          Real.log (4 * max (upMax W n ω) (Real.sqrt (predVar μ ℱ W n ω)) / δ))
        + 2 * upMax W n ω * Real.log (4 * max (upMax W n ω) (Real.sqrt (predVar μ ℱ W n ω)) / δ)
        < ∑ t ∈ Finset.range n, W t ω} := by
    filter_upwards [hpvY, hV0] with ω hpv hv hmain
    simp only [Set.mem_ofPred_eq, Set.mem_union] at hmain ⊢
    rw [hpvW ω, hpv, hsumY ω, hsumW ω]
    have tY := thr_mono (predVar μ ℱ X (τ ω) ω) (upMax Y n ω) (absMax X (τ ω) ω) δ hv
      (upMax_facts Y n ω).1 (hupY ω) hδ0 hδ1
    have tW := thr_mono (predVar μ ℱ X (τ ω) ω) (upMax W n ω) (absMax X (τ ω) ω) δ hv
      (upMax_facts W n ω).1 (hupW ω) hδ0 hδ1
    rcases lt_abs.1 hmain with h | h
    · exact Or.inl (lt_of_le_of_lt tY h)
    · exact Or.inr (lt_of_le_of_lt tW h)
  calc μ _ ≤ μ (_ ∪ _) := measure_mono_ae hsub
    _ ≤ μ _ + μ _ := measure_union_le _ _
    _ ≤ ENNReal.ofReal (δ / 2) + ENNReal.ofReal (δ / 2) := add_le_add h1 h2
    _ = ENNReal.ofReal δ := by rw [← ENNReal.ofReal_add hδ2.le hδ2.le, add_halves]

theorem freedman_fk {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m0) (X : ℕ → Ω → ℝ) (hXm : ∀ t, StronglyMeasurable[ℱ (t + 1)] (X t))
    (hX : ∀ t, Integrable (X t) μ) (hX2 : ∀ t, Integrable (fun ω => X t ω ^ 2) μ)
    (τ : Ω → ℕ) (hτ : IsStoppingTime ℱ (fun ω => (τ ω : WithTop ℕ))) (n : ℕ) (hτn : ∀ ω, τ ω ≤ n)
    (hdrift : ∀ t, ∀ᵐ ω ∂μ, t < τ ω → μ[X t | ℱ t] ω = 0) (κ δ : ℝ) (hκ : 0 < κ) (hδ0 : 0 < δ)
    (hδ1 : δ ≤ 1) :
    μ {ω | 3 * Real.sqrt (predVar μ ℱ X (τ ω) ω * Real.log (4 * max (absMax (fun t ω => κ * X t ω) (τ ω) ω)
            (κ * Real.sqrt (predVar μ ℱ X (τ ω) ω)) / δ))
        + 2 * (absMax (fun t ω => κ * X t ω) (τ ω) ω / κ) * Real.log (4 * max (absMax (fun t ω => κ * X t ω) (τ ω) ω)
            (κ * Real.sqrt (predVar μ ℱ X (τ ω) ω)) / δ)
        < |∑ t ∈ Finset.range (τ ω), X t ω|} ≤ ENNReal.ofReal δ := by
  set K : ℕ → Ω → ℝ := fun t ω => κ * X t ω with hK
  have hKs : ∀ t, K t = κ • X t := fun t => by funext ω; simp [hK]
  have hK2s : ∀ t, (fun ω => K t ω ^ 2) = κ ^ 2 • fun ω => X t ω ^ 2 := fun t => by
    funext ω; simp only [hK, Pi.smul_apply, smul_eq_mul]; ring
  have hKm : ∀ t, StronglyMeasurable[ℱ (t + 1)] (K t) := fun t => by
    rw [hKs t]; exact (hXm t).const_smul κ
  have hKint : ∀ t, Integrable (K t) μ := fun t => by rw [hKs t]; exact (hX t).smul κ
  have hK2int : ∀ t, Integrable (fun ω => K t ω ^ 2) μ := fun t => by
    rw [hK2s t]; exact (hX2 t).smul _
  have hKdrift : ∀ t, ∀ᵐ ω ∂μ, t < τ ω → μ[K t | ℱ t] ω = 0 := by
    intro t
    have h := condExp_smul (μ := μ) κ (X t) (ℱ t)
    filter_upwards [hdrift t, h] with ω h1 h2 hlt
    rw [hKs t, h2, Pi.smul_apply, h1 hlt, smul_zero]
  have hpv : ∀ᵐ ω ∂μ, predVar μ ℱ K (τ ω) ω = κ ^ 2 * predVar μ ℱ X (τ ω) ω := by
    have h : ∀ᵐ ω ∂μ, ∀ t, (μ[fun ω => K t ω ^ 2 | ℱ t]) ω = κ ^ 2 * (μ[fun ω => X t ω ^ 2 | ℱ t]) ω :=
      ae_all_iff.2 fun t => by
        have := condExp_smul (μ := μ) (κ ^ 2) (fun ω => X t ω ^ 2) (ℱ t)
        filter_upwards [this] with ω hω
        rw [hK2s t, hω, Pi.smul_apply, smul_eq_mul]
    filter_upwards [h] with ω hω
    simp only [predVar, hω, Finset.mul_sum]
  have hV0 : ∀ᵐ ω ∂μ, 0 ≤ predVar μ ℱ X (τ ω) ω := by
    have h : ∀ᵐ ω ∂μ, ∀ t, 0 ≤ (μ[fun ω => X t ω ^ 2 | ℱ t]) ω :=
      ae_all_iff.2 fun t => condExp_nonneg (ae_of_all _ fun ω => by positivity)
    filter_upwards [h] with ω hω
    exact Finset.sum_nonneg fun t _ => hω t
  have h := freedman_stopped μ ℱ K hKm hKint hK2int τ hτ n hτn hKdrift δ hδ0 hδ1
  refine le_trans (measure_mono_ae ?_) h
  filter_upwards [hpv, hV0] with ω hp hv hmain
  by_contra hnot
  rw [not_lt, hp] at hnot
  have hsum : ∑ t ∈ Finset.range (τ ω), K t ω = κ * ∑ t ∈ Finset.range (τ ω), X t ω := by
    simp only [hK, Finset.mul_sum]
  rw [hsum] at hnot
  have hB : 0 ≤ absMax K (τ ω) ω := le_trans zero_le_one ((upMax_facts K (τ ω) ω).1.trans
    (upMax_facts K (τ ω) ω).2.2.2.1)
  exact absurd hmain (not_lt.2 (freedman_rescale _ _ _ κ δ hv hB hκ hnot))

/-! ## The interface statements -/

theorem freedmanUnnorm : FreedmanUnnorm.{u} := fun μ _ ℱ X α hα hXm hX hX2 hle hdrift n δ hδ =>
  freedman_unnorm μ ℱ X α hα hXm hX hX2 hle hdrift n δ hδ

theorem freedmanFK : FreedmanFK.{u} := fun μ _ ℱ X hXm hX hX2 τ hτ n hτn hdrift κ δ hκ hδ0 hδ1 =>
  freedman_fk μ ℱ X hXm hX hX2 τ hτ n hτn hdrift κ δ hκ hδ0 hδ1

end AdversarialBco.Poly
